#!/usr/bin/env python3
"""Measure what splitting heavy declarations into judgment ops costs, in PolkaVM.

    heavy_bench.py PACK NAMES OUT --check LEAN_CHECK.jam --sim WITNESS_SIM [--ms MS] [--jobs N]

PACK is a `lean-host convert --pack` directory; NAMES a file of declaration names, a line each.
For each declaration, in OUT/NAME: its closure's arguments (`lean-host pack-args`), its whole
check's gas (`witness-sim check`, no limit), then its ops planned as mathlib_work.py plans them
(`lean-host judgments` at MS a group, default 25, twice, the second with the first's measured
costs; then `judgments-ops` with VERIFY=1 for each op's arguments), and each op's gas. Writes
OUT/NAME/bench.json (the whole check's gas; each op's gas, units, citations, cited bytes and
argument bytes) and prints a line a declaration: ops, relays, rounds, gas, and gas over the whole
check's.
"""
import argparse
import concurrent.futures as cf
import json
import os
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
HOST = os.path.join(HERE, "../../target/release/lean-host")


def run(*args, env=None):
    return subprocess.run(args, check=True, capture_output=True, text=True, env=env).stdout


def gas_of(a, args, limit):
    out = run(a.sim, "check", a.check, args, str(limit))
    m = re.search(r"^(\w+).*: used (\d+) gas", out)
    return m.group(1) == "Ok", int(m.group(2))


def bench(a, name, manifest):
    d = f"{a.out}/{name}"
    os.makedirs(d, exist_ok=True)
    by_name = {n: e for e in manifest for n in e["names"]}
    by_hash = {e["hash"]: e for e in manifest}
    node = by_name[name]
    seen, stack = set(), list(node["imports"]) + list(node.get("proof_imports", []))
    while stack:
        h = stack.pop()
        if h not in seen:
            seen.add(h)
            stack.extend(by_hash[h]["imports"])
    with open(f"{d}/closure", "w") as f:
        f.write("\n".join([node["hash"]] + sorted(seen)) + "\n")
    full = f"{d}/full.args"
    if not os.path.exists(full):
        run(HOST, "pack-args", a.pack, f"{d}/closure", full)
    if not os.path.exists(f"{d}/whole.json"):
        ok, gas = gas_of(a, full, 10**13)
        json.dump({"ok": ok, "gas": gas}, open(f"{d}/whole.json", "w"))
    whole = json.load(open(f"{d}/whole.json"))
    ms = str(a.ms)
    run(HOST, "judgments", full, f"{d}/p1", ms)
    run(HOST, "judgments-ops", full, f"{d}/p1")
    run(HOST, "judgments", full, f"{d}/p2", ms, f"{d}/p1/costs.json")
    run(HOST, "judgments-ops", full, f"{d}/p2", env={**os.environ, "VERIFY": "1"})
    plan = json.load(open(f"{d}/p2/plan.json"))
    groups = plan["groups"]
    with cf.ThreadPoolExecutor(a.jobs) as pool:
        gases = list(pool.map(lambda g: gas_of(a, f"{d}/p2/group-{g}.args", 5 * 10**9), range(len(groups))))
    ops = []
    for g, (group, (ok, gas)) in enumerate(zip(groups, gases)):
        ops.append({
            "ok": ok, "gas": gas, "round": group["round"], "units": group["units"], "cites": len(group["cites"]),
            "cited_bytes": sum(groups[c]["judgment_bytes"] for c in group["cites"]),
            "judgment_bytes": group["judgment_bytes"], "calls_bytes": group["calls_bytes"],
            "args_bytes": os.path.getsize(f"{d}/p2/group-{g}.args"), "planned_gas": group["gas"],
        })
        os.remove(f"{d}/p2/group-{g}.args")  # tens of megabytes each, made again if needed
    result = {"name": name, "whole": whole, "rounds": plan["rounds"], "ops": ops}
    json.dump(result, open(f"{d}/bench.json", "w"), indent=1)
    total = sum(o["gas"] for o in ops)
    relays = [o for o in ops if o["units"] == 0]
    failed = sum(not o["ok"] for o in ops)
    print(f"{name}: {len(ops)} ops ({len(relays)} relays, {failed} failed), {plan['rounds']} rounds; "
          f"ops {total:.3g} gas (relays {sum(o['gas'] for o in relays):.3g}), whole {whole['gas']:.3g}: "
          f"{total / whole['gas']:.1f}x", flush=True)


def main():
    p = argparse.ArgumentParser(usage=__doc__)
    p.add_argument("pack"); p.add_argument("names"); p.add_argument("out")
    p.add_argument("--check", required=True); p.add_argument("--sim", required=True)
    p.add_argument("--ms", type=float, default=25)
    p.add_argument("--jobs", type=int, default=os.cpu_count())
    a = p.parse_args()
    a.out = os.path.abspath(a.out)
    manifest = json.load(open(f"{a.pack}/manifest.json"))
    for name in [l.strip() for l in open(a.names) if l.strip()]:
        bench(a, name, manifest)


if __name__ == "__main__":
    sys.exit(main())
