"""The fact DAG of one heavy declaration: pieces plus every call whose cache entry a unit hits
from outside its own region, closed to a fixpoint; then units, total work, and depth.

    fact_dag.py DIR [OUT]

DIR holds a nanoda-profiling run's `spans.bin` (NANODA_SPANS), `hits.bin` (NANODA_HITS) and
`pieces.txt` (the piece cut, as NANODA_PIECES reads it), all from the same binary. With OUT,
also writes OUT/units.json (the DAG) and OUT/facts.txt (every needed fact, for NANODA_PIECES).
"""
import sys
import numpy as np

h = sys.argv[1]
sp = np.fromfile(f"{h}/spans.bin", dtype="<u8").reshape(-1, 3)
hits = np.fromfile(f"{h}/hits.bin", dtype="<u8").reshape(-1, 2)
n = int(sp[:, 0].max())
end = np.zeros(n + 1, dtype=np.int64); us = np.zeros(n + 1, dtype=np.int64)
end[sp[:, 0]] = sp[:, 1]; us[sp[:, 0]] = sp[:, 2]
# Virtual root 0 spans the whole declaration.
end[0] = n
# Parent of every call (calls are numbered in pre-order).
parent = np.zeros(n + 1, dtype=np.int64)
stack = [0]
for i in range(1, n + 1):
    while end[stack[-1]] < i:
        stack.pop()
    parent[i] = stack[-1]
    stack.append(i)
us[0] = int(sum(us[i] for i in range(1, n + 1) if parent[i] == 0))
BUDGET = 30_000  # µs of instrumented time per unit's own work (about 18 ms native)
pieces = [int(l.split()[0]) for l in open(f"{h}/pieces.txt")]
# Units to start with: the pieces, the declaration, and each of its top-level calls.
roots = set(pieces) | {0} | {i for i in range(1, n + 1) if parent[i] == 0}
at, made = hits[:, 0].astype(np.int64), hits[:, 1].astype(np.int64)

def unit_of(isroot):
    """Each call's nearest enclosing unit root (itself if a root)."""
    u = np.zeros(n + 1, dtype=np.int64)
    for i in range(1, n + 1):
        u[i] = i if isroot[i] else u[parent[i]]
    return u

for it in range(50):
    isroot = np.zeros(n + 1, dtype=bool); isroot[list(roots)] = True
    u = unit_of(isroot)
    outside = u[at] != u[made]
    new = set(made[outside].tolist()) - roots
    # A unit whose own work is over budget gives up its biggest sub-calls as units of their own.
    own = us.copy()
    for i in range(1, n + 1):
        if isroot[i]:
            own[u[parent[i]]] -= us[i]
    split = set()
    over = {r for r in roots if r and own[r] > BUDGET}
    if over:
        # Candidates: the largest calls in the region that fit the budget themselves (the
        # frontier), so that big intermediate calls stay put instead of becoming a chain.
        kids = {}
        for i in range(1, n + 1):
            if not isroot[i] and u[i] in over and us[i] <= BUDGET and (isroot[parent[i]] or us[parent[i]] > BUDGET):
                kids.setdefault(int(u[i]), []).append(i)
        for r, ks in kids.items():
            left = own[r]
            for k in sorted(ks, key=lambda k: -us[k]):
                if left <= BUDGET:
                    break
                split.add(k)
                left -= us[k]
    print(f"iteration {it}: {len(roots)} units, {int(outside.sum())} outside hits, {len(new)} new units, {len(over)} over budget split into {len(split)}", flush=True)
    if not new and not split:
        break
    roots |= new | split

# Work: each unit's own region.
own = us.copy()
for i in range(1, n + 1):
    if isroot[i]:
        own[u[parent[i]]] -= us[i]
R = sorted(roots)
work = {r: int(own[r]) for r in R}
# Needs: facts hit from outside, plus nested units' results.
needs = {r: set() for r in R}
for a, m in zip(u[at][outside].tolist(), u[made][outside].tolist()):
    needs[a].add(m)
for r in R:
    if r:
        needs[int(u[parent[r]])].add(r)
if len(sys.argv) > 2:
    # The DAG, for grouping (fact_groups.py): each unit's root, own work, depth comes after; the
    # facts (creation indices) it needs from outside, the facts made in it that others need, and
    # the units nested directly in it. And every needed fact, as NANODA_PIECES reads a piece.
    import json
    made_in = {}
    for m in set(made[outside].tolist()):
        made_in.setdefault(int(u[m]), []).append(m)
    need_facts = {r: set() for r in R}
    for a, m in zip(u[at][outside].tolist(), made[outside].tolist()):
        need_facts[a].add(m)
    nested = {r: [] for r in R}
    for r in R:
        if r:
            nested[int(u[parent[r]])].append(r)
    with open(sys.argv[2] + "/facts.txt", "w") as f:
        f.write(" ".join(["0"] + [str(m) for m in sorted(set(made[outside].tolist()))]) + "\n")
    units_out = [{"root": r, "work": work[r], "needs": sorted(need_facts[r]), "makes": sorted(made_in.get(r, [])), "nested": nested[r]} for r in R]

# Depth: longest chain, processing units by when they finished.
order = sorted(R, key=lambda r: (end[r], -r))
pos = {r: k for k, r in enumerate(order)}
bad = sum(1 for r in R for m in needs[r] if pos[m] >= pos[r])
depth, path = {}, {}
for r in order:
    ds = [depth[m] for m in needs[r] if m in depth]
    depth[r] = 1 + max(ds, default=0)
    path[r] = work[r] + max((path[m] for m in needs[r] if m in path), default=0)
if len(sys.argv) > 2:
    for x in units_out:
        x["depth"] = depth[x["root"]]
    with open(sys.argv[2] + "/units.json", "w") as f:
        json.dump(units_out, f)
total = sum(work.values())
w = np.array([work[r] for r in R])
print(f"\n{len(R)} units; order violations {bad}")
print(f"work: total {total/1e3:.0f} ms (whole check {us[0]/1e3:.0f} ms); per unit median {np.median(w):.0f} µs, p99 {np.percentile(w,99)/1e3:.1f} ms, max {w.max()/1e3:.1f} ms")
D = max(depth.values())
print(f"depth {D} rounds; critical path {max(path.values())/1e3:.0f} ms")
ne = np.array([len(needs[r]) for r in R])
print(f"needs per unit: median {np.median(ne):.0f}, p99 {np.percentile(ne,99):.0f}, max {ne.max()}")
lv = {}
for r in R:
    lv.setdefault(depth[r], []).append(work[r])
print("round  units  work_ms  max_unit_ms")
for d in sorted(lv):
    if d <= 5 or d % max(1, D // 15) == 0 or d == D:
        print(f"{d:5} {len(lv[d]):6} {sum(lv[d])/1e3:8.0f} {max(lv[d])/1e3:11.1f}")
