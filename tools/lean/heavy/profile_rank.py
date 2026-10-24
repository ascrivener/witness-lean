"""Rank Mathlib's nodes by nanoda check time (lean-host profile), and size the heavy tail.

    rank.py PACK PROFILE [LEAN_TIMES]
"""
import json, struct, sys
pack, prof = sys.argv[1], sys.argv[2]
GAS_PER_MS = 80e6  # this M3 (tools/lean/gas_per_ms.py: 77-83M)
BUDGET = 4.5e9
entries = [json.loads(l) for l in open(f"{pack}/manifest.jsonl")]
data, pos, rows = open(prof, "rb").read(), 0, []
FAIL, EXCL = 2**32 - 1, 2**32 - 2
fails = excluded = 0
for e in entries:
    t, n = struct.unpack_from("<II", data, pos)
    pos += 8 + 4 * n
    if t == FAIL:
        fails += 1
    elif t == EXCL:
        excluded += 1
    else:
        rows.append((t, e["names"][0], e["kind"]))
rows.sort(reverse=True)
total = sum(t for t, _, _ in rows)
print(f"{len(entries)} nodes: {len(rows)} checked, {fails} failed, {excluded} excluded; total {total / 1e6:.0f} s"
      f" ≈ {total / 1e3 * GAS_PER_MS:.1e} gas")
for ms in [20, 56, 100, 500, 1000]:
    over = [t for t, _, _ in rows if t >= ms * 1000]
    print(f"  ≥ {ms:>4} ms: {len(over):6} nodes, {sum(over) / 1e6:7.1f} s")
over = [r for r in rows if r[0] / 1e3 * GAS_PER_MS > BUDGET]
kinds = {}
for _, _, k in over:
    kinds[k] = kinds.get(k, 0) + 1
print(f"over one refine (> {BUDGET:.1e} gas, {BUDGET / GAS_PER_MS:.0f} ms): {len(over)}, by kind {kinds}")
lean = {}
if len(sys.argv) > 3:
    for l in open(sys.argv[3]).readlines()[1:]:
        p = l.split()
        lean[p[2]] = int(p[0])
print(f"\n{'nanoda ms':>10} {'≈ refines':>9} {'Lean ms':>8}  kind  name")
for t, name, kind in rows[:40]:
    print(f"{t / 1e3:>10.1f} {t / 1e3 * GAS_PER_MS / BUDGET:>9.1f} {lean.get(name, ''):>8}  {kind[:5]:5} {name}")
