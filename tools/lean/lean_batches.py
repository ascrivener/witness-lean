#!/usr/bin/env python3
"""Lay out a lean_plan.py plan as files for attesting with the witness CLI.

    lean_batches.py DIR PLAN WORK

For each batch N, in WORK: batch-N.subjects (comma-separated paths of its nodes, for `witness
bundle`), batch-N.trust (comma-separated CLAIM:ENTRY references to the nodes it trusts, CLAIM
being batch-M.claim, the claim file `witness attest --claim-out` writes for batch M) and
batch-N.proofs (its proofs, packed as the check's witness). For a plan with a goal: goal.trust,
goal.pack (the goal's node and proof, the reveal's witness), goal.hash (its hash, hex), and
goal.cite (one CLAIM:ENTRY the bounty cites, to fix the pins: a node the goal imports). Also
pins (the pinned nodes' hashes, hex, back to back: the check's attest params).
"""
import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from lean_pack import pack  # noqa: E402

PINNED = {
    "eagerReduce", "Quot", "Quot.mk", "Quot.lift", "Quot.ind", "String", "String.ofList", "Nat",
    "Nat.zero", "Nat.succ", "Nat.add", "Nat.sub", "Nat.mul", "Nat.pow", "Nat.mod", "Nat.div",
    "Nat.beq", "Nat.ble", "Nat.gcd", "Nat.xor", "Nat.land", "Nat.lor", "Nat.shiftLeft",
    "Nat.shiftRight", "Bool.true", "Bool.false", "Char", "Char.ofNat", "List", "List.nil",
    "List.cons", "propext", "Classical.choice", "Quot.sound",
}  # nanoda_lib::nodes::PINNED_NAMES


def main(d, plan_path, work):
    manifest = json.load(open(f"{d}/manifest.json"))
    by_hash = {e["hash"]: e for e in manifest}
    plan = json.load(open(plan_path))
    os.makedirs(work, exist_ok=True)
    home = {}  # node hash -> (batch, entry)
    for n, b in enumerate(plan):
        for i, h in enumerate(b.get("subjects", [])):
            home[h] = (n, i)

    def refs(hashes):
        return ",".join(f"{work}/batch-{home[h][0]}.claim:{home[h][1]}" for h in hashes)

    def write(name, data):
        with open(f"{work}/{name}", "wb" if isinstance(data, bytes) else "w") as f:
            f.write(data)

    proof = lambda h: open(f"{d}/proofs/{h}", "rb").read()
    for n, b in enumerate(plan):
        if "goal" in b:
            g = b["goal"]
            write("goal.trust", refs(b["trusted"]))
            write("goal.pack", pack([open(f"{d}/nodes/{g}", "rb").read(), proof(g)]))
            write("goal.hash", g)
            write("goal.cite", refs(by_hash[g]["imports"][:1]))
            continue
        write(f"batch-{n}.subjects", ",".join(f"{d}/nodes/{h}" for h in b["subjects"]))
        write(f"batch-{n}.trust", refs(b["trusted"]))
        write(f"batch-{n}.proofs", pack([proof(h) for h in b["subjects"] if "proof_size" in by_hash[h]]))
    write("pins", "".join(e["hash"] for e in manifest if PINNED & set(e["names"])))
    print(sum("subjects" in b for b in plan), file=sys.stderr)


if __name__ == "__main__":
    if len(sys.argv) != 4:
        sys.exit(__doc__)
    main(*sys.argv[1:])
