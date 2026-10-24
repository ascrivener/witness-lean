#!/usr/bin/env python3
"""Attest a planned library in parallel: several attesters, several batches to a work package.

    attest.py WORK PLAN BATCHES --witness W --service SVC --check CHECK --pins HEX --check-gas G
              --gas-per-ms RATE --attesters A,B,... [--sim WITNESS_SIM | --witness-dir DIR]

--package-gas caps the refine gas a package is filled with. On a laptop testnet every guarantor
and auditor shares one machine, which can't refine a package of the chain's full 5×10⁹ inside
the guarantors' deadline: "Slow refine ... 5 s" in the node log, then "Not enough signatures",
and the package is dropped. A batch needing more still goes alone. --settle waits some slots after
a round lands, while the validators audit it: on one machine, a round sent straight after the
last can find them too busy to refine it in time.

WORK is lean_batches.py's output for PLAN (lean-host trace's, which records each batch's native
`ms`), BATCHES the number of batches in it. A batch needs the batches it trusts attested first;
batches that don't depend on each other can go in any order. So in each round, every attester
fills a work package with batches whose dependencies are attested (or earlier in that package:
accumulate applies a package's items in order), up to the package's refine gas (each batch's
estimated from its `ms` at RATE gas per native millisecond), accumulate gas, size, extrinsics
and items, and the package's own bytes (see MAX_PACKAGE). Each attester signs with its own nonces and submits to its own core, so their
packages don't depend on each other. Then it waits for the round to land, and requeues whatever
didn't, from the chain's state: what's attested and each attester's nonce. A batch that keeps
failing goes alone with all the gas, and fails the run after a few tries.

On a testnet (JAM_RPC, default ws://localhost:19800) it submits through witness's
scripts/jam-submit.py (DIR is a witness checkout); with --sim, through witness-sim, one item
after another, which applies them the same way. Prints a line per round, and the gas each batch
was estimated to need goes to WORK/estimates.
"""

import argparse
import importlib.util
import json
import os
import re
import subprocess
import sys
import tempfile
import time
from concurrent.futures import ThreadPoolExecutor

# Refine gas beyond the check's: the service's reserve, hashing what it's given, and loading the
# check into its inner PVM before lending it gas, per byte (a 405 KB check took about 3×10⁷).
REFINE_RESERVE = 20_000_000
HASH_GAS_PER_BYTE = 61
LOAD_GAS_PER_BYTE = 100
# What an estimate is scaled by, for safety.
MARGIN = 1.3
# Accumulate gas for an attestation: a base, and a lookup per attestation it rests on (FTA's first
# batches, citing up to 20, used at most 3.1×10⁵ in all).
ACCUMULATE_BASE = 400_000
ACCUMULATE_PER_PARENT = 15_000
# Rounds a batch may fail before it goes alone with all the gas, and before giving up.
ALONE_AFTER, GIVE_UP_AFTER = 1, 6
# The most bytes a package's encoding (payloads, not extrinsics) may take: jam-submit.py's
# MAX_PACKAGE, what PolkaJam v0.1.29's nodes accept. Witness-sim keeps to it too. An attestation's
# payload is small (its citations are an extrinsic): estimated, then measured once built.
MAX_PACKAGE = 200 * 1024
PACKAGE_PER_ITEM = 1024
# Slots to wait for a round to land (a package that lands does in two or three), and seconds
# between polls of the chain.
LAND_SLOTS, POLL = 4, 2
# Threads building ops, at low priority: on a local testnet the validators share this machine,
# and a package they can't refine in time is dropped.
BUILDERS = 4


def run(*args):
    return subprocess.run(args, check=True, capture_output=True, text=True).stdout.strip()


def low_priority():
    os.nice(10)


class Chain:
    """The chain witness runs on: a testnet over RPC, or witness-sim."""

    def __init__(self, a):
        self.a, self.sim = a, a.sim
        if self.sim:
            self.params = {"max_refine_gas": 5 * 10**9, "max_accumulate_gas": 10**7, "max_input": 13_791_360,
                           "max_extrinsics": 128, "max_work_items": 16, "core_count": 1}
            return
        spec = importlib.util.spec_from_file_location("jam_submit", f"{a.witness_dir}/scripts/jam-submit.py")
        self.js = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(self.js)
        self.rpc = self.js.Rpc(self.js.url())
        self.params = next(iter(self.rpc.call("parameters").values()))

    def storage(self, key):
        if self.sim:
            v = subprocess.run([self.sim, "inspect", "storage", "--raw", self.a.service, key],
                               capture_output=True, text=True).stdout.strip()
            return v if v.startswith("0x") else None
        best = self.rpc.call("bestBlock")["header_hash"]
        v = self.rpc.call("serviceValue", best, int(self.a.service), self.js.b64(bytes.fromhex(key[2:])))
        return "0x" + self.js.unb64(v).hex() if v is not None else None

    def slot(self):
        return 0 if self.sim else self.rpc.call("bestBlock")["slot"]

    def submit(self, items, core):
        """Submit (payload, extrinsics, refine gas, accumulate gas) items as one package."""
        if self.sim:
            with tempfile.TemporaryDirectory() as tmp:
                for i, (payload, extrinsics, _, _) in enumerate(items):
                    files = []
                    for j, x in enumerate(extrinsics):
                        files.append(f"{tmp}/{i}-{j}")
                        open(files[-1], "wb").write(x)
                    open(f"{tmp}/op", "w").write(payload.hex())
                    run(self.sim, "item", self.a.service, f"@{tmp}/op", *files)
            return
        self.js.submit(self.rpc, int(self.a.service), items, core)


class Attester:
    def __init__(self, a, chain):
        self.a, self.chain = a, chain
        with open(a.plan) as f:
            self.plan = json.load(f)
        self.total = a.batches
        self.deps, self.parents = [], []
        for n in range(self.total):
            with open(f"{a.work}/batch-{n}.trust") as f:
                cited = {int(m) for m in re.findall(r"batch-(\d+)\.claim:", f.read())}
            self.deps.append(cited)
            self.parents.append(len(cited))
        self.attested = set()
        self.tries = [0] * self.total
        self.keys = {}
        self.estimates = open(f"{a.work}/estimates", "w")

    def w(self, *args):
        return run(self.a.witness, *args)

    def is_attested(self, n):
        claim = f"{self.a.work}/batch-{n}.claim"
        if not os.path.exists(claim):
            return False
        if n not in self.keys:
            self.keys[n] = self.w("key", "--attestation", claim)
        return self.chain.storage(self.keys[n]) is not None

    def nonce(self, who):
        v = self.chain.storage(self.w("key", "--account", who))
        return int(re.search(r"nonce: (\d+)", self.w("decode", "--account", v)).group(1)) if v else 0

    def build(self, n, who, nonce):
        """Batch n's op for `who` with `nonce`: its payload and extrinsics."""
        with tempfile.TemporaryDirectory() as x:
            trust = open(f"{self.a.work}/batch-{n}.trust").read()
            payload = subprocess.run([self.a.witness,
                "attest", "--service", self.a.service, "--attester", who, "--nonce", str(nonce),
                "--check", self.a.check, "--params", self.a.pins,
                "--subjects", open(f"{self.a.work}/batch-{n}.subjects").read(),
                *(["--trust", trust] if trust else []),
                "--witness-file", f"{self.a.work}/batch-{n}.proofs", "--check-gas", str(self.a.check_gas),
                "--claim-out", f"{self.a.work}/batch-{n}.claim", "--extrinsics", x],
                check=True, capture_output=True, text=True, preexec_fn=low_priority).stdout.strip()
            extrinsics = [open(f"{x}/{i}", "rb").read() for i in range(len(os.listdir(x)))]
        return bytes.fromhex(payload.removeprefix("0x")), extrinsics

    def gas(self, n, hashed, alone):
        """Refine and accumulate gas for batch n's item, which hashes `hashed` bytes."""
        p = self.chain.params
        if alone:
            return p["max_refine_gas"], p["max_accumulate_gas"]
        check = self.plan[n]["ms"] * self.a.gas_per_ms
        load = LOAD_GAS_PER_BYTE * os.path.getsize(self.a.check)
        refine = int(MARGIN * (check + HASH_GAS_PER_BYTE * hashed + load) + REFINE_RESERVE)
        accumulate = int(MARGIN * (ACCUMULATE_BASE + ACCUMULATE_PER_PARENT * self.parents[n]))
        return min(refine, p["max_refine_gas"]), min(accumulate, p["max_accumulate_gas"])

    def size(self, n):
        """About how many bytes batch n's item carries, before building it."""
        subjects = open(f"{self.a.work}/batch-{n}.subjects").read().split(",")
        trusted = self.plan[n]["trusted"]
        nodes = os.path.dirname(subjects[0])
        return (os.path.getsize(self.a.check) + sum(map(os.path.getsize, subjects))
                + sum(os.path.getsize(f"{nodes}/{h}") + 48 * 32 for h in trusted))

    def package(self, who, pending, taken):
        """Choose batches for who's next package, from pending in order, and build them."""
        p = self.chain.params
        room = {"refine": self.a.package_gas or p["max_refine_gas"], "accumulate": p["max_accumulate_gas"],
                "input": int(0.95 * p["max_input"]), "package": MAX_PACKAGE, "items": p["max_work_items"]}
        chosen = []
        for n in pending:
            if n in taken or not self.deps[n] <= self.attested | set(chosen):
                continue
            alone = self.tries[n] > ALONE_AFTER
            if alone and chosen:
                continue
            # Estimate from the plan; the op's real size and gas are checked once built.
            size = self.size(n)
            payload = PACKAGE_PER_ITEM
            refine, accumulate = self.gas(n, size, alone)
            fits = (refine <= room["refine"] and accumulate <= room["accumulate"] and size <= room["input"]
                    and payload <= room["package"])
            if chosen and not (fits and room["items"]):
                continue
            chosen.append(n)
            room["refine"] -= refine
            room["accumulate"] -= accumulate
            room["input"] -= size
            room["package"] -= payload
            room["items"] -= 1
            if alone:
                break
        if not chosen:
            return []
        # Build in parallel, but a batch only once those it trusts in this package are built: an
        # op cites their claims, which building writes.
        base, built = self.nonce(who), {}
        with ThreadPoolExecutor(BUILDERS) as pool:
            def build(i, n):
                for m in self.deps[n] & built.keys():
                    built[m].result()
                return self.build(n, who, base + i)
            for i, n in enumerate(chosen):
                built[n] = pool.submit(build, i, n)
            ops = [built[n].result() for n in chosen]
        # Keep the longest prefix that fits as built: dropping from the end keeps nonces in order.
        items, refine, accumulate, size, package, count = [], 0, 0, 0, 512, 0
        for n, (payload, extrinsics) in zip(chosen, ops):
            # JAM hashes the check, extrinsic 0; the service hashes the rest.
            r, acc = self.gas(n, sum(map(len, extrinsics[1:])), self.tries[n] > ALONE_AFTER)
            s = len(payload) + sum(map(len, extrinsics))
            k = len(payload) + 128 + 40 * len(extrinsics)
            if not items and package + k > MAX_PACKAGE:
                sys.exit(f"attest.py: batch {n}'s op alone is {len(payload)} bytes, over a package's {MAX_PACKAGE}")
            if items and (refine + r > (self.a.package_gas or p["max_refine_gas"]) or accumulate + acc > p["max_accumulate_gas"]
                          or size + s > 0.95 * p["max_input"] or package + k > MAX_PACKAGE
                          or count + len(extrinsics) > p["max_extrinsics"]):
                break
            items.append((n, (payload, extrinsics, r, acc)))
            refine, accumulate, size, package = refine + r, accumulate + acc, size + s, package + k
            count += len(extrinsics)
            self.estimates.write(f"{n} {r} {acc} {s}\n")
        self.estimates.flush()
        return items

    def run(self):
        attesters = self.a.attesters.split(",")
        cores = max(1, self.chain.params.get("core_count", 1))
        start, rounds, failed = time.time(), 0, 0
        while len(self.attested) < self.total:
            rounds += 1
            pending = [n for n in range(self.total) if n not in self.attested]
            taken, refused, sent = set(), set(), []
            for i, who in enumerate(attesters):
                items = self.package(who, pending, taken | refused)
                if not items:
                    continue
                try:
                    self.chain.submit([item for _, item in items], i % cores)
                except SystemExit as e:
                    # The testnet sometimes can't reach a guarantor; the next round tries again.
                    print(f"{who}'s package of {len(items)} not submitted: {e}", flush=True)
                    refused.update(n for n, _ in items)
                    continue
                taken.update(n for n, _ in items)
                sent.append([n for n, _ in items])
            if not sent:
                failed += 1
                if failed > GIVE_UP_AFTER:
                    sys.exit(f"attest.py: nothing attested in {failed} rounds, {self.total - len(self.attested)} to go")
                time.sleep(POLL)
                continue
            failed = 0
            # Wait for the round to land: everything sent attested, or the deadline.
            waiting = set(taken)
            deadline = self.chain.slot() + LAND_SLOTS
            while waiting:
                waiting = {n for n in waiting if not self.is_attested(n)}
                if not waiting or self.chain.sim or self.chain.slot() > deadline:
                    break
                time.sleep(POLL)
            landed = taken - waiting
            self.attested |= landed
            if landed and self.a.settle and not self.chain.sim:
                # Let the validators audit what landed before giving them more to refine.
                settle = self.chain.slot() + self.a.settle
                while self.chain.slot() < settle:
                    time.sleep(POLL)
            for n in waiting:
                self.tries[n] += 1
                if self.tries[n] > GIVE_UP_AFTER:
                    sys.exit(f"attest.py: batch {n} wasn't attested after {self.tries[n]} tries")
            print(f"round {rounds}: {len(landed)} of {len(taken)} batches attested in {len(sent)} packages "
                  f"({', '.join(str(len(s)) for s in sent)} items); {len(self.attested)} of {self.total} attested, "
                  f"{time.time() - start:.0f} s", flush=True)


def main():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("work")
    p.add_argument("plan")
    p.add_argument("batches", type=int)
    for flag in ("witness", "service", "check", "pins", "attesters"):
        p.add_argument(f"--{flag}", required=True)
    p.add_argument("--check-gas", type=int, required=True)
    p.add_argument("--gas-per-ms", type=float, required=True)
    p.add_argument("--package-gas", type=int, help="refine gas to fill a package with (default the chain's)")
    p.add_argument("--settle", type=int, default=0, help="slots to wait after a round lands (default 0)")
    p.add_argument("--sim")
    p.add_argument("--witness-dir")
    a = p.parse_args()
    if not a.sim and not a.witness_dir:
        p.error("give --sim or --witness-dir")
    Attester(a, Chain(a)).run()


if __name__ == "__main__":
    main()
