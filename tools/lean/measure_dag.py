#!/usr/bin/env python3
"""Measure what checking each declaration of a lean4export export needs.

    measure_dag.py EXPORT.ndjson

For each definition and theorem: its direct references, and its load set (the constants it
mentions, closed over the types of everything loaded and the values of definitions, which
checking may unfold, but not theorem proofs), with the NDJSON size of those statements. Also the
depth of the dependency DAG. See docs/design/content-addressed.md.
"""
import json, sys
from functools import lru_cache
lines = open(sys.argv[1]).read().splitlines()
items = [json.loads(l) for l in lines]
expr, name_of, decls = {}, {}, []
for it, l in zip(items, lines):
    if 'ie' in it: expr[it['ie']] = (it, len(l))
    if 'in' in it: name_of[it['in']] = it
EXPR = {"type", "value", "body", "fn", "arg", "struct", "rhs", "expr"}
def kids(e):
    body = [v for k, v in e.items() if k != 'ie'][0]
    if isinstance(body, dict):
        for k, v in body.items():
            if k in EXPR and isinstance(v, int): yield v
def const_of(e):
    body = e.get('const')
    return body['name'] if isinstance(body, dict) else None
sys.setrecursionlimit(100000)
memo = {}
def consts(root):
    # constants mentioned in the expression DAG under root, and its bytes
    seen = set(); st = [root]; cs = set(); size = 0
    while st:
        x = st.pop()
        if x in seen or x not in expr: continue
        seen.add(x); e, n = expr[x]; size += n
        c = const_of(e)
        if c is not None: cs.add(c)
        st.extend(kids(e))
    return cs, size
# declarations: name -> (kind, type root, value root or None, line bytes)
D = {}
for it, l in zip(items, lines):
    for kind in ('def', 'thm', 'axiom', 'opaque', 'quot', 'inductive'):
        if kind in it:
            d = it[kind]
            if kind == 'inductive':
                # an inductive block declares types, ctors and recursors; treat each as a node
                for sub in ('types', 'ctors', 'recs'):
                    for x in d.get(sub, []):
                        D[x['name']] = ('ind', x['type'], None, 0)
            else:
                D[d['name']] = (kind, d['type'], d.get('value'), len(l))
TY, VAL = {}, {}
for n, (k, t, v, _) in D.items():
    TY[n] = consts(t); VAL[n] = consts(v) if v is not None else (set(), 0)
def refs(n): return (TY[n][0] | VAL[n][0]) - {n}
# load set: statements of referenced constants, closed over definition values and types
def load(n):
    need = set(); st = list(refs(n))
    while st:
        c = st.pop()
        if c in need or c not in D: continue
        need.add(c)
        st.extend(TY[c][0])
        if D[c][0] == 'def': st.extend(VAL[c][0])
    return need
def stmt_bytes(c): return TY[c][1] + (VAL[c][1] if D[c][0] == 'def' else 0)
depth = {}
order = [n for n in D]
for n in order:  # export order is topological
    depth[n] = 1 + max((depth[c] for c in refs(n) if c in depth), default=0)
names = [n for n in D if D[n][0] in ('def', 'thm')]
stats = []
for n in names:
    L = load(n)
    stats.append((len(refs(n)), len(L), sum(stmt_bytes(c) for c in L)))
stats.sort(key=lambda s: s[2])
q = lambda i: stats[int(i * (len(stats) - 1))]
tot = sum(stmt_bytes(c) for c in D)
print(f"{len(D)} declarations, {len(names)} defs/theorems; NDJSON of all statements (types + def values): {tot/1e6:.1f} MB")
for label, i in [('median', .5), ('90%', .9), ('99%', .99), ('max', 1)]:
    r, l, b = q(i)
    print(f"  {label:6} load set: {l} declarations, {b/1e3:.0f} KB NDJSON (direct refs {r})")
print("DAG depth:", max(depth.values()))
