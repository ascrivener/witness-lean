#!/usr/bin/env python3
"""Lay out attesting all of Mathlib for witness's attest-batches.py, heavy declarations included.

    mathlib_work.py PACK PROFILE WORK [--budget-ms MS] [--jobs N] [--lean-host PATH]

PACK is a `lean-host convert --pack` directory (with manifest.jsonl) and PROFILE its `lean-host
profile`. Batches are planned as plan_profile.py plans them, at MS (default 40) estimated native
milliseconds a batch. A node too slow for any batch alone is *heavy*:
- an inductive block is split by declaration and phase (`lean-host split-inductive`);
- a theorem or definition is checked in judgments: `lean-host judgments` and `judgments-ops`,
  twice, the second plan grouping by the costs the first measured.
Heavy nodes are done in N parallel jobs (default 6), in WORK/heavy/HASH, and skipped when done
(their ops.json exists), so a run can be resumed.

WORK is laid out as attest-batches.py reads it, with paths relative to WORK (run it there): batch-N.subjects (node, proof and judgment
files), batch-N.trust (CLAIM:ENTRY references), batch-N.witness and batch-N.gas, with every
heavy node's ops as batches of their own, and each heavy node's own batch trusting what its
judgments' last op trusts and citing the judgments it needs. Node and proof files go in
WORK/nodes and WORK/proofs. Prints the number of batches.
"""
import argparse
import concurrent.futures as cf
import json
import os
import struct
import subprocess
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from lean_pack import pack  # noqa: E402
import plan_profile  # noqa: E402

MAX_WITNESS = 60000  # under witness's MAX_WITNESS_LEN of 64 KiB, as lean_batches.py
GAS_PER_MS = 80e6  # this machine (tools/lean/gas_per_ms.py)


class Pack:
    """A lean-host pack: nodes and proofs by hash (see tools/lean-host/src/pack.rs)."""

    def __init__(self, d):
        idx = open(f"{d}/pack.idx", "rb").read()
        self.files = [open(f"{d}/nodes.pack", "rb"), open(f"{d}/proofs.pack", "rb")]
        self.index = {}
        for k in range(0, len(idx) - 44, 45):
            off, ln = struct.unpack_from("<QI", idx, k + 33)
            self.index[(idx[k], idx[k + 1:k + 33])] = (off, ln)

    def get(self, kind, h):
        off, ln = self.index[(kind, bytes.fromhex(h))]
        f = self.files[kind]
        f.seek(off)
        return f.read(ln)

    def has(self, kind, h):
        return (kind, bytes.fromhex(h)) in self.index


def heavy_job(a, h, kind, closure_file):
    """Do heavy node h: its ops in WORK/heavy/h, ops.json last."""
    d = f"{a.work}/heavy/{h}"
    host = a.lean_host
    def run(*args):
        return subprocess.run([host, *args], check=True, capture_output=True, text=True).stdout
    full = f"{d}/full.args"
    if not os.path.exists(full):
        run("pack-args", a.pack, closure_file, full)
    if kind == "inductive":
        run("split-inductive", full, d, str(int(a.budget_ms)))
        os.remove(full)  # tens of megabytes, made again if needed
        return
    for p in ("p1", "p2"):
        costs = [str(25), f"{d}/p1/costs.json"] if p == "p2" else [str(25)]
        run("judgments", full, f"{d}/{p}", *costs)
        run("judgments-ops", full, f"{d}/{p}")
    # The second plan's ops, with paths relative to WORK/heavy/h.
    o = json.load(open(f"{d}/p2/ops.json"))
    for op in o["ops"]:
        op["subject"], op["witness"] = f"p2/{op['subject']}", f"p2/{op['witness']}"
    json.dump(o, open(f"{d}/ops.json.tmp", "w"))
    os.replace(f"{d}/ops.json.tmp", f"{d}/ops.json")
    os.remove(full)


def main():
    p = argparse.ArgumentParser(usage=__doc__)
    p.add_argument("pack"); p.add_argument("profile"); p.add_argument("work")
    p.add_argument("--budget-ms", type=float, default=40)
    p.add_argument("--jobs", type=int, default=6)
    p.add_argument("--lean-host", default=os.path.join(os.path.dirname(__file__), "../../target/release/lean-host"))
    a = p.parse_args()
    a.work = os.path.abspath(a.work)
    os.makedirs(f"{a.work}/heavy", exist_ok=True)
    entries = [json.loads(l) for l in open(f"{a.pack}/manifest.jsonl")]
    hashes = [e["hash"] for e in entries]
    batches, names, sizes, proof_sizes, us, failed, depths, excluded = plan_profile.plan(a.pack, a.profile, a.budget_ms, 36000)
    if failed:
        sys.exit(f"mathlib_work.py: {len(failed)} nodes fail their check, {failed[0]} first")
    _, _, _, imports, proof_imports, _, _ = plan_profile.load(a.pack, a.profile)
    heavy = [b[1][0] for b in batches if len(b[1]) == 1 and b[4] > a.budget_ms]
    print(f"{len(batches)} batches over {depths} depths; {len(heavy)} heavy nodes", file=sys.stderr, flush=True)

    # Heavy nodes: each one's closure (what its statement and proof import, and what those
    # import, recursively), then its ops, in parallel.
    def closure(i):
        seen, stack = set(), list(imports[i]) + list(proof_imports[i])
        while stack:
            j = int(stack.pop())
            if j not in seen:
                seen.add(j)
                stack.extend(imports[j])
        seen.discard(i)
        return sorted(seen)
    todo = []
    for i in heavy:
        h = hashes[i]
        d = f"{a.work}/heavy/{h}"
        if os.path.exists(f"{d}/ops.json"):
            continue
        os.makedirs(d, exist_ok=True)
        with open(f"{d}/closure", "w") as f:
            f.write("\n".join([h] + [hashes[j] for j in closure(i)]) + "\n")
        todo.append((h, entries[i]["kind"], f"{d}/closure"))
    errors = []
    with cf.ThreadPoolExecutor(a.jobs) as pool:
        futures = {pool.submit(heavy_job, a, h, k, c): (h, k) for h, k, c in todo}
        for n, f in enumerate(cf.as_completed(futures), 1):
            h, k = futures[f]
            try:
                f.result()
            except subprocess.CalledProcessError as e:
                errors.append(h)
                print(f"heavy {h} ({k}) failed: {e.stdout[-300:]} {e.stderr[-300:]}", file=sys.stderr, flush=True)
            if n % 25 == 0 or n == len(todo):
                print(f"heavy: {n} of {len(todo)} done, {len(errors)} failed", file=sys.stderr, flush=True)
    if errors:
        sys.exit(f"mathlib_work.py: {len(errors)} heavy nodes failed")

    # Node and proof files, and where each node is attested.
    pk = Pack(a.pack)
    os.makedirs(f"{a.work}/nodes", exist_ok=True)
    os.makedirs(f"{a.work}/proofs", exist_ok=True)
    for h in hashes:
        if not os.path.exists(f"{a.work}/nodes/{h}"):
            open(f"{a.work}/nodes/{h}", "wb").write(pk.get(0, h))
        if pk.has(1, h) and not os.path.exists(f"{a.work}/proofs/{h}"):
            open(f"{a.work}/proofs/{h}", "wb").write(pk.get(1, h))
    home = {}
    for n, b in enumerate(batches):
        for e, i in enumerate(b[1]):
            home[hashes[i]] = (n, e)
    claim = lambda n: f"batch-{n}.claim"
    node_refs = lambda hs: [f"{claim(home[h][0])}:{home[h][1]}" for h in hs]

    def write(n, subjects, refs, proofs, gas):
        witness_items = [open(f, "rb").read() for f in proofs]
        if len(pack(witness_items)) > MAX_WITNESS:
            # Too big for the witness: the proofs go among the subjects, as lean_batches.py does.
            subjects, witness_items = subjects + proofs, []
        open(f"{a.work}/batch-{n}.subjects", "w").write(",".join(rel(f) for f in subjects))
        open(f"{a.work}/batch-{n}.trust", "w").write(",".join(refs))
        open(f"{a.work}/batch-{n}.witness", "wb").write(pack(witness_items))
        open(f"{a.work}/batch-{n}.gas", "w").write(str(int(gas)))

    rel = lambda f: os.path.relpath(f, a.work)
    heavy_set = set(heavy)
    total = len(batches)
    ops_written = 0
    for n, b in enumerate(batches):
        level, subjects, _, _, ms, trusted = b
        files = [f"{a.work}/nodes/{hashes[i]}" for i in subjects]
        proofs = [f"{a.work}/proofs/{hashes[i]}" for i in subjects if pk.has(1, hashes[i])]
        if len(subjects) == 1 and subjects[0] in heavy_set:
            h = hashes[subjects[0]]
            d = f"{a.work}/heavy/{h}"
            o = json.load(open(f"{d}/ops.json"))
            number = {}
            for op in o["ops"]:
                number[op["name"]] = total
                refs = node_refs(op["trust_nodes"]) + [f"{claim(number[c])}:0" for c in op["trust_ops"]]
                with open(f"{d}/{op['witness']}", "rb") as f:
                    w = f.read()
                open(f"{a.work}/batch-{total}.subjects", "w").write(rel(f"{d}/{op['subject']}"))
                open(f"{a.work}/batch-{total}.trust", "w").write(",".join(refs))
                open(f"{a.work}/batch-{total}.witness", "wb").write(w)
                open(f"{a.work}/batch-{total}.gas", "w").write(str(int(4e9)))
                total += 1
                ops_written += 1
            refs = node_refs(o["final"]["trust_nodes"]) + [f"{claim(number[c])}:0" for c in o["final"]["trust_ops"]]
            write(n, files, refs, proofs, 4e9)
            continue
        write(n, files, node_refs(hashes[i] for i in trusted), proofs, ms * GAS_PER_MS)
    print(f"{len(batches)} batches and {ops_written} heavy ops", file=sys.stderr)
    print(total)


if __name__ == "__main__":
    main()
