#!/usr/bin/env python3
"""Plan a pack directory's attestation from `lean-host profile`, without per-batch environments.

    plan_profile.py DIR PROFILE [--budget-ms MS] [--plan OUT.json] [--max-proof BYTES]

Makes the batches lean_plan.py and `lean-host trace` would: nodes of one dependency depth, split
where their proofs pass MAX_PROOF bytes or a batch's estimated native check time passes MS
(default 100). A batch trusts what its subjects' checks looked up (from the profile) and what
they and their proofs import, outside the batch. Its time is estimated as its subjects' profiled
check times plus a cost per byte of nodes it loads, fitted on FTA (see the README). Prints totals:
batches, trusted bytes, estimated gas, and the nodes too slow for any batch.
"""

import argparse
import json
import sys

import numpy as np

# A batch's native time, fitted on FTA's 2,419 traced batches (median error 7%): its subjects'
# profiled check times (checked in one big environment, which runs slower than a batch's), plus
# loading its trusted nodes and its subjects with their proofs, per byte.
CHECK_SCALE = 0.658
NS_PER_TRUSTED_BYTE = 20.5
NS_PER_SUBJECT_BYTE = 44.0
GAS_PER_MS = 27e6  # PolkaVM gas per native millisecond (measured on the heavy Mathlib theorems)


def load(d, profile):
    sizes, proof_sizes, names = [], [], []
    with open(f"{d}/manifest.jsonl") as f:
        for line in f:
            e = json.loads(line)
            sizes.append(e["size"])
            proof_sizes.append(e.get("proof_size", 0))
            names.append(e["names"][0])
    n = len(sizes)
    idx = np.fromfile(f"{profile}.index", dtype="<u4")
    prof = np.fromfile(profile, dtype="<u4")
    imports, proof_imports, us, touched = [], [], np.zeros(n, dtype=np.int64), []
    p = 0
    for i in range(n):
        k = int(idx[p]); imports.append(idx[p + 1 : p + 1 + k]); p += 1 + k
        k = int(idx[p]); proof_imports.append(idx[p + 1 : p + 1 + k]); p += 1 + k
    q = 0
    for i in range(n):
        us[i] = int(prof[q]); k = int(prof[q + 1]); touched.append(prof[q + 2 : q + 2 + k]); q += 2 + k
    return np.array(sizes, dtype=np.int64), np.array(proof_sizes, dtype=np.int64), names, imports, proof_imports, us, touched


def plan(d, profile, budget_ms, max_proof):
    sizes, proof_sizes, names, imports, proof_imports, us, touched = load(d, profile)
    n = len(sizes)
    failed = [names[i] for i in range(n) if us[i] == 0xFFFFFFFF]
    excluded = us == 0xFFFFFFFE  # depends on an unpermitted axiom: not attested
    us = np.where(us >= 0xFFFFFFFE, 0, us)
    depth = np.zeros(n, dtype=np.int64)
    for i in np.fromfile(f"{profile}.order", dtype="<u4").tolist():  # dependency order
        deps = np.concatenate([imports[i], proof_imports[i]])
        depth[i] = 1 + (depth[deps].max() if len(deps) else -1)
    keep = np.nonzero(~excluded)[0]
    order = keep[np.argsort(depth[keep], kind="stable")]
    n = len(order)

    def needs(subjects):
        s = set(subjects)
        need = set()
        for i in subjects:
            need.update(touched[i].tolist()); need.update(imports[i].tolist()); need.update(proof_imports[i].tolist())
        return need - s

    def estimate_ms(subjects, trusted):
        t_bytes = int(sizes[list(trusted)].sum()) if trusted else 0
        s_bytes = int(sizes[subjects].sum() + proof_sizes[subjects].sum())
        return (CHECK_SCALE * us[subjects].sum() / 1000) + (t_bytes * NS_PER_TRUSTED_BYTE + s_bytes * NS_PER_SUBJECT_BYTE) / 1e6, t_bytes

    batches = []

    def close(level, subjects):
        trusted = needs(subjects)
        ms, t_bytes = estimate_ms(subjects, trusted)
        if ms > budget_ms and len(subjects) > 1:
            half = len(subjects) // 2
            # As trace does: the second half may trust the first, attested before it.
            close(level, subjects[:half]); close(level, subjects[half:])
            return
        batches.append((level, subjects, len(trusted), t_bytes, ms, sorted(trusted)))

    start = 0
    while start < n:
        level = depth[order[start]]
        end = start
        while end < n and depth[order[end]] == level:
            end += 1
        current, proof_bytes = [], 0
        for i in order[start:end].tolist():
            if current and proof_bytes + proof_sizes[i] > max_proof:
                close(level, current); current, proof_bytes = [], 0
            current.append(i); proof_bytes += int(proof_sizes[i])
        if current:
            close(level, current)
        start = end
    return batches, names, sizes, proof_sizes, us, failed, int(depth.max()) + 1, int(excluded.sum())


def main():
    p = argparse.ArgumentParser(usage=__doc__)
    p.add_argument("dir"); p.add_argument("profile")
    p.add_argument("--budget-ms", type=float, default=100)
    p.add_argument("--max-proof", type=int, default=36000)
    p.add_argument("--plan", help="write the batches as subject and trusted counts, one a line")
    p.add_argument("--fit", help="a `lean-host plan` times file for the same directory: compare estimates")
    a = p.parse_args()
    batches, names, sizes, proof_sizes, us, failed, depths, excluded = plan(a.dir, a.profile, a.budget_ms, a.max_proof)
    ms = np.array([b[4] for b in batches])
    over = [(b[4], names[b[1][0]]) for b in batches if b[4] > a.budget_ms]
    gas = ms * GAS_PER_MS
    print(f"{len(sizes)} nodes ({excluded} left out for an unpermitted axiom), {len(failed)} failed checks; "
          f"{len(batches)} batches over {depths} depths")
    print(f"node bytes {sizes.sum():,} (kept on chain), proof bytes {proof_sizes.sum():,}")
    print(f"profiled checking {us.sum() / 1e6:.0f} s; estimated batch time {ms.sum() / 1e3:.0f} s native, "
          f"{gas.sum():.3g} gas ({gas.sum() / 4.5e9:.0f} refines' worth at 4.5e9)")
    print(f"trusted nodes per batch: median {int(np.median([b[2] for b in batches]))}, max {max(b[2] for b in batches)}; "
          f"trusted bytes: median {int(np.median([b[3] for b in batches])):,}, max {max(b[3] for b in batches):,}")
    for cap in (4.5e9, 5e9):
        print(f"batches over {cap:.2g} gas: {int((gas > cap).sum())}")
    print(f"single nodes over {a.budget_ms} ms: {len(over)}")
    for t, nm in sorted(over, reverse=True)[:15]:
        print(f"  {t:8.0f} ms  {t * GAS_PER_MS:.3g} gas  {nm}")
    for nm in failed[:20]:
        print(f"  check failed: {nm}")
    if a.plan:
        with open(a.plan, "w") as f:
            for level, subjects, nt, tb, t, _ in batches:
                f.write(json.dumps({"depth": int(level), "subjects": subjects, "trusted": nt, "trusted_bytes": tb, "ms": round(t, 2)}) + "\n")
    if a.fit:
        import re
        real = [float(m.group(2)) * {"µs": 1e-3, "ms": 1, "s": 1e3}[m.group(3)]
                for m in (re.match(r"batch (\d+): \w+ in ([\d.]+)(µs|ms|s)\b", l) for l in open(a.fit)) if m]
        print(f"reference: {len(real)} batches, {sum(real) / 1e3:.1f} s native, max {max(real):.0f} ms; "
              f"estimate: {len(batches)} batches, {ms.sum() / 1e3:.1f} s, max {ms.max():.0f} ms")


if __name__ == "__main__":
    main()
