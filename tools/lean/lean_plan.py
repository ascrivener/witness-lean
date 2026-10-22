#!/usr/bin/env python3
"""Plan attesting a lean_nodes.py output directory in batches.

    lean_plan.py DIR [--goal NAME] [--max-proof BYTES] > PLAN.json

Batches follow dependency depth: a node's depth is one more than the deepest node it or its proof
imports, and each batch takes nodes of one depth, so a batch only trusts nodes of earlier batches,
and all batches of one depth can be attested at once. A depth is split into several batches when
its proofs would make a witness bigger than MAX_PROOF_BYTES (default 36000: an op travels as a
hex command-line argument to `jamt item`, which Linux caps at 128 KiB).

Each batch lists its subjects (nodes, in dependency order) and the nodes it must trust: everything
its subjects and their proofs import, recursively, outside the batch. The plan is a list of
batches, each {"depth", "subjects", "trusted"}, with node hashes in hex.

With --goal, the theorem NAME is left out of the batches, for a solver to reveal instead, and the
plan gets a last entry {"goal": hash, "trusted": [...]} with what revealing it needs trusted.
"""
import json
import sys


def main(d, goal_name, max_proof):
    manifest = json.load(open(f"{d}/manifest.json"))
    by_hash = {e["hash"]: e for e in manifest}
    goal = None
    if goal_name:
        goal = next(e for e in manifest if goal_name in e["names"])
        manifest = [e for e in manifest if e is not goal]
    depth = {}
    for e in manifest:  # dependency order
        deps = e["imports"] + e.get("proof_imports", [])
        depth[e["hash"]] = 1 + max((depth[h] for h in deps), default=-1)

    closure_memo = {}

    def closure(h):
        """h and everything its node imports, recursively."""
        if h not in closure_memo:
            out = {h}
            for i in by_hash[h]["imports"]:
                out |= closure(i)
            closure_memo[h] = frozenset(out)
        return closure_memo[h]

    batches = []
    for level in range(max(depth.values()) + 1):
        current, proof_bytes = [], 0
        for e in manifest:
            if depth[e["hash"]] != level:
                continue
            size = e.get("proof_size", 0)
            if current and proof_bytes + size > max_proof:
                batches.append((level, current))
                current, proof_bytes = [], 0
            current.append(e["hash"])
            proof_bytes += size
        if current:
            batches.append((level, current))

    def needs(subjects):
        need = set()
        for h in subjects:
            e = by_hash[h]
            for i in e["imports"] + e.get("proof_imports", []):
                need |= closure(i)
        return sorted(need - set(subjects))

    plan = [{"depth": level, "subjects": subjects, "trusted": needs(subjects)} for level, subjects in batches]
    out = plan + ([{"goal": goal["hash"], "trusted": needs([goal["hash"]])}] if goal else [])
    json.dump(out, sys.stdout, indent=0)

    def stat(xs):
        xs = sorted(xs)
        return f"median {xs[len(xs) // 2]}, max {xs[-1]}"

    size = lambda hs: sum(by_hash[h]["size"] for h in hs)
    home = {h: i for i, b in enumerate(plan) for h in b["subjects"]}
    print(
        f"{len(plan)} batches over {max(depth.values()) + 1} depths\n"
        f"subjects per batch: {stat([len(b['subjects']) for b in plan])}\n"
        f"trusted nodes per batch: {stat([len(b['trusted']) for b in plan])}\n"
        f"trusted bytes per batch: {stat([size(b['trusted']) for b in plan])}\n"
        f"batches cited per batch: {stat([len({home[h] for h in b['trusted']}) for b in plan])}",
        file=sys.stderr,
    )


if __name__ == "__main__":
    import argparse
    p = argparse.ArgumentParser(usage=__doc__)
    p.add_argument("dir")
    p.add_argument("--goal")
    p.add_argument("--max-proof", type=int, default=36000)
    a = p.parse_args()
    main(a.dir, a.goal, a.max_proof)
