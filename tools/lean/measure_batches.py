#!/usr/bin/env python3
"""Measure batching for content-addressed attestations (docs/design/content-addressed.md).

    measure_batches.py EXPORT.ndjson

Cuts the export's declarations into batches (in export order, then by dependency depth), and for
each batch finds the batches holding the statements its declarations need (its trusted set), how
many bytes of statements those are, and how many rounds attesting takes.
"""
import sys, runpy
# Reuse measure_dag's parsing (it runs its own report first).
sys.argv = ['measure_dag.py', sys.argv[1]] + sys.argv[2:]
import io, contextlib
buf = io.StringIO()
with contextlib.redirect_stdout(buf):
    g = runpy.run_path(__import__('os').path.join(__import__('os').path.dirname(__file__), 'measure_dag.py'), run_name='__main__')
D, TY, VAL, refs, load, stmt_bytes = g['D'], g['TY'], g['VAL'], g['refs'], g['load'], g['stmt_bytes']
order = list(D)  # export order: dependencies first
def proof_bytes(n): return VAL[n][1] if D[n][0] == 'thm' else 0
for target in (50_000, 150_000, 400_000):  # NDJSON bytes of statements + proofs per batch
    batch_of, batches, cur, size = {}, [], [], 0
    for n in order:
        cur.append(n); size += stmt_bytes(n) + proof_bytes(n)
        if size >= target:
            batches.append(cur); cur, size = [], 0
    if cur: batches.append(cur)
    for i, b in enumerate(batches):
        for n in b: batch_of[n] = i
    stmt = [sum(stmt_bytes(n) for n in b) for b in batches]
    trusted, depth = [], []
    for i, b in enumerate(batches):
        need = set()
        for n in b:
            need |= {batch_of[c] for c in load(n) if c in batch_of}
        need.discard(i)
        trusted.append(need)
        depth.append(1 + max((depth[j] for j in need), default=0))
    loads = sorted(sum(stmt[j] for j in t) for t in trusted)
    counts = sorted(len(t) for t in trusted)
    q = lambda xs, f: xs[int(f * (len(xs) - 1))]
    print(f"batches of ~{target//1000} KB: {len(batches)} batches, {depth[-1] if depth else 0}..{max(depth)} rounds; "
          f"trusted batches per batch median {q(counts,.5)} max {counts[-1]}; "
          f"trusted statement KB median {q(loads,.5)//1000} p90 {q(loads,.9)//1000} max {loads[-1]//1000}")

print("-- batching by dependency depth, then export order within a depth --")
depth_of = {}
for n in order:
    depth_of[n] = 1 + max((depth_of[c] for c in refs(n) if c in depth_of), default=0)
for target in (50_000, 150_000, 400_000):
    batches, by_level = [], {}
    for n in order: by_level.setdefault(depth_of[n], []).append(n)
    for lvl in sorted(by_level):
        cur, size = [], 0
        for n in by_level[lvl]:
            cur.append(n); size += stmt_bytes(n) + proof_bytes(n)
            if size >= target: batches.append(cur); cur, size = [], 0
        if cur: batches.append(cur)
    batch_of = {n: i for i, b in enumerate(batches) for n in b}
    stmt = [sum(stmt_bytes(n) for n in b) for b in batches]
    trusted, depth = [], []
    for i, b in enumerate(batches):
        need = set()
        for n in b: need |= {batch_of[c] for c in load(n) if c in batch_of}
        need.discard(i); trusted.append(need)
        depth.append(1 + max((depth[j] for j in need), default=0))
    loads = sorted(sum(stmt[j] for j in t) for t in trusted); counts = sorted(len(t) for t in trusted)
    q = lambda xs, f: xs[int(f * (len(xs) - 1))]
    print(f"batches of ~{target//1000} KB: {len(batches)} batches, {max(depth)} rounds; "
          f"trusted batches per batch median {q(counts,.5)} max {counts[-1]}; "
          f"trusted statement KB median {q(loads,.5)//1000} p90 {q(loads,.9)//1000} max {loads[-1]//1000}")
