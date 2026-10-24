"""Group a heavy declaration's fact DAG into work items, and measure what citing facts costs.

    fact_groups.py DIR [CAP_KB...]

DIR holds `units.json` (fact_dag.py's DAG) and `factnodes.bin` (NANODA_FACTNODES: each needed
fact's node ids). Within each round of the DAG, units are packed in call order into groups. A
group is one work item: it attests its units, and publishes the facts they make as one blob,
which later groups cite whole. A group closes when adding a unit would take it past the gas
budget, the citation or cited-bytes limits, or (when given) CAP_KB of its own blob.

The model, from the stage-1 measurements (docs/design/heavy-declarations.md):
- gas: loading the environment, plus the units' own work, plus parsing the blobs it cites;
- bytes: distinct nodes (shared within one blob, not across blobs) at about 6 bytes each.
"""
import json
import sys
import numpy as np

ENV_GAS = 5.0e8  # loading the declaration's environment (traced arguments, 620 nodes)
GAS_PER_US = 5.0e4  # gas per microsecond of instrumented work: the whole check, 2.09 s ≈ 1.0e11
GAS_PER_BYTE = 300  # rebuilding and seeding cited facts: ~1 ms (≈3e7 gas) per 100 KB
BYTES_PER_NODE = 6  # the piece files: about 6 bytes per expression, names and levels included
BUDGET = 4.5e9
MAX_CITES = 3000  # MAX_BLOBS is 4096, and the environment takes ~620
MAX_CITED = 12e6  # MAX_BLOBS_LEN is 16 MiB; the bundle about 13.8 MB, the environment 0.6 MB

d = sys.argv[1]
units = json.load(open(f"{d}/units.json"))
raw = np.fromfile(f"{d}/factnodes.bin", dtype="<u8")
nodes, pos = {}, 0
while pos < len(raw):
    at, n = int(raw[pos]), int(raw[pos + 1])
    nodes[at] = raw[pos + 2 : pos + 2 + n]
    pos += 2 + n
empty = np.zeros(0, dtype="<u8")


def size(facts):
    """Bytes of one blob holding `facts`, shared subterms once."""
    arrs = [nodes.get(f, empty) for f in facts]
    if not arrs:
        return 0
    return len(np.unique(np.concatenate(arrs))) * BYTES_PER_NODE


# A nested unit's result is a fact its parent needs too; its terms were mostly not logged (they
# weren't hit as cache entries), so it counts as a citation of no bytes unless it was.
by_root = {x["root"]: x for x in units}
for x in units:
    for r in x["nested"]:
        x["needs"].append(r)
        by_root[r]["makes"].append(r)


# Each unit's facts as a blob of its own: a work item can attest several subjects, so what a group
# publishes needn't be one blob.
unit_blob = {}
unit_of_fact = {}
for x in units:
    seen = set()
    for f in x["makes"]:
        seen.update(nodes.get(f, empty).tolist())
        unit_of_fact[f] = x["root"]
    unit_blob[x["root"]] = len(seen) * BYTES_PER_NODE


def run(cap, per_unit=False):
    group_of_fact, blob, blob_nodes = {}, [], []
    groups = []  # (round, units, cited groups, cited bytes, needed bytes, gas)
    rounds = sorted({x["depth"] for x in units})
    for rnd in rounds:
        members = sorted((x for x in units if x["depth"] == rnd), key=lambda x: x["root"])
        g0 = dict(units=0, cites=set(), cited=0, work=0, made=set(), needed=set())
        cur = dict(g0, cites=set(), made=set(), needed=set())

        def close(cur):
            if not cur["units"]:
                return
            g = len(blob)
            blob.append(len(cur["made"]) * BYTES_PER_NODE)
            blob_nodes.append(np.fromiter(cur["made"], dtype="<u8", count=len(cur["made"])))
            if not per_unit and cur["cites"]:
                # The cited blobs' distinct nodes: what they'd cost with subterms shared across them.
                cur["unique"] = len(np.unique(np.concatenate([blob_nodes[c] for c in cur["cites"]]))) * BYTES_PER_NODE
            for f in cur["facts"]:
                group_of_fact[f] = g
            gas = ENV_GAS + cur["work"] * GAS_PER_US + cur["cited"] * GAS_PER_BYTE
            groups.append((rnd, cur["units"], len(cur["cites"]), cur["cited"], len(cur["needed"]) * BYTES_PER_NODE, gas, cur.get("unique", 0)))

        cur["facts"] = []
        for x in members:
            if per_unit:
                c = {unit_of_fact[f] for f in x["needs"] if f in unit_of_fact and f in group_of_fact} - cur["cites"]
                add_cited = sum(unit_blob[u] for u in c)
            else:
                c = {group_of_fact[f] for f in x["needs"] if f in group_of_fact} - cur["cites"]
                add_cited = sum(blob[g] for g in c)
            mine = set()
            for f in x["makes"]:
                mine.update(nodes.get(f, empty).tolist())
            gas = ENV_GAS + (cur["work"] + x["work"]) * GAS_PER_US + (cur["cited"] + add_cited) * GAS_PER_BYTE
            over = (
                gas > BUDGET
                or len(cur["cites"]) + len(c) > MAX_CITES
                or cur["cited"] + add_cited > MAX_CITED
                or (cap and cur["made"] and len(cur["made"] | mine) * BYTES_PER_NODE > cap)
            )
            if cur["units"] and over:
                close(cur)
                cur = dict(g0, cites=set(), made=set(), needed=set())
                cur["facts"] = []
                if per_unit:
                    c = {unit_of_fact[f] for f in x["needs"] if f in unit_of_fact and f in group_of_fact}
                    add_cited = sum(unit_blob[u] for u in c)
                else:
                    c = {group_of_fact[f] for f in x["needs"] if f in group_of_fact}
                    add_cited = sum(blob[g] for g in c)
            cur["units"] += 1
            cur["cites"] |= c
            cur["cited"] += add_cited
            cur["work"] += x["work"]
            cur["made"] |= mine
            cur["facts"] += x["makes"]
            for f in x["needs"]:
                cur["needed"].update(nodes.get(f, empty).tolist())
        close(cur)
    return groups, blob


def report(cap, per_unit=False):
    groups, blob = run(cap, per_unit)
    if per_unit:
        blob = [b for b in unit_blob.values() if b]
    a = np.array([g[1:] for g in groups], dtype=float)
    bad = sum(1 for g in groups if g[5] > BUDGET or g[2] > MAX_CITES or g[3] > MAX_CITED)
    cited, needed, unique = a[:, 2].sum(), a[:, 3].sum(), a[:, 5].sum()
    print(
        f"{'unit blobs' if per_unit else 'group blobs'} cap {cap // 1000 if cap else '-':>5} KB: {len(groups):6} groups, gas {a[:, 4].sum():.2e}"
        f" (max {a[:, 4].max():.2e}); cites max {int(a[:, 1].max())}, median {int(np.median(a[:, 1]))};"
        f" cited MB max {a[:, 2].max() / 1e6:.1f}; cited/needed {cited / max(needed, 1):.1f}x;"
        f" blob KB median {np.median(blob) / 1e3:.0f} max {max(blob) / 1e3:.0f}; over a limit {bad}"
    )
    if not per_unit:
        work = sum(x["work"] for x in units) * GAS_PER_US
        print(
            f"    duplication across cited blobs {cited / unique:.1f}x, unneeded facts {unique / needed:.1f}x;"
            f" gas: environment {len(groups) * ENV_GAS:.1e}, work {work:.1e}, parsing cited {cited * GAS_PER_BYTE:.1e}"
            f" (shared subterms {unique * GAS_PER_BYTE:.1e}, only what's needed {needed * GAS_PER_BYTE:.1e})"
        )


print(f"{len(units)} units, {len(nodes)} facts with terms logged, {sum(len(v) for v in nodes.values()) / 1e6:.1f}M node refs")
for cap in [int(c) * 1000 for c in sys.argv[2:]] or [0, 500_000, 20_000]:
    report(cap)
report(0, per_unit=True)
a = np.array(sorted(unit_blob.values()))
print(f"unit blobs: {int((a > 0).sum())} non-empty; KB median {np.median(a[a > 0]) / 1e3:.1f}, p99 {np.percentile(a[a > 0], 99) / 1e3:.0f}, max {a.max() / 1e3:.0f}")
