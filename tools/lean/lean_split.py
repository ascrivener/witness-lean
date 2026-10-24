#!/usr/bin/env python3
"""Split theorems whose proofs are too slow to check in one refine (see WitnessSplit.lean).

    LEAN4EXPORT=path/to/lean4export lean_split.py PROJECT MODULE NODES_DIR NAME[=MS]... \\
        [--budget N] [--stmt-ms MS] [--trace-ms MS]

Runs `#witness_split NAME N MS PCT` (defaults 2000 and 10) on each theorem in Lean project
PROJECT, importing MODULE, and for each it reports split: exports the new proof and the theorems
split off from it, converts them to nodes and merges them into NODES_DIR (a lean_nodes.py output).
The new proof becomes the proof of NAME's statement node, whose hash doesn't change; each piece's
node goes into the manifest just before NAME's. Prints the names it split.

PCT is the share of NAME's own time each piece may take: a theorem `lean-host trace` timed at MS
(`over MS: NAME`) against a batch budget of --trace-ms has to come down to that budget, so
100 × TRACE_MS / MS percent, at most 100. Without MS (or --trace-ms), 80.
"""

import json
import os
import shutil
import subprocess
import sys
import tempfile

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import lean_nodes  # noqa: E402

HERE = os.path.dirname(os.path.abspath(__file__))


def lean_env(project, extra):
    path = subprocess.run(["lake", "env", "printenv", "LEAN_PATH"], cwd=project, check=True,
                          capture_output=True, text=True).stdout.strip()
    return dict(os.environ, LEAN_PATH=f"{extra}:{path}")


def split(project, module, names, budget, stmt_ms, work):
    """Compile the splits in `work`; return the names whose split helped."""
    env = lean_env(project, work)
    shutil.copy(f"{HERE}/WitnessSplit.lean", f"{work}/WitnessSplit.lean")
    subprocess.run(["lean", f"--root={work}", "-o", f"{work}/WitnessSplit.olean", f"{work}/WitnessSplit.lean"],
                   cwd=project, env=env, check=True)
    with open(f"{work}/WitnessSplitGen.lean", "w") as f:
        f.write(f"import {module}\nimport WitnessSplit\nset_option maxHeartbeats 0\n")
        for n, pct in names:
            f.write(f"#witness_split {n} {budget} {stmt_ms} {pct}\n")
    out = subprocess.run(["lean", f"--root={work}", "-o", f"{work}/WitnessSplitGen.olean", f"{work}/WitnessSplitGen.lean"],
                         cwd=project, env=env, capture_output=True, text=True)
    if out.returncode != 0:
        sys.exit(f"lean_split: splitting failed:\n{out.stdout}{out.stderr}")
    done = []
    for line in out.stdout.splitlines():
        if "witness_split " in line:
            report = line[line.index("witness_split "):]
            print(report, file=sys.stderr)
            verdict, rest = report.split(" ", 2)[1:]
            if verdict == "split":
                done.append(rest.split(":")[0])
    if not done:
        return []
    export = subprocess.run([os.environ["LEAN4EXPORT"], "WitnessSplitGen", "--"] + [f"{n}.wsplit" for n in done],
                            cwd=project, env=env, check=True, capture_output=True).stdout
    with open(f"{work}/split.ndjson", "wb") as f:
        f.write(export)
    return done


def merge(nodes_dir, work, done):
    with open(f"{work}/split.ndjson") as f:
        ex = lean_nodes.Export(json.loads(l) for l in f if l.strip())
    with open(f"{nodes_dir}/manifest.json") as f:
        manifest = json.load(f)
    have = {e["hash"] for e in manifest}
    declared = {n: e["hash"] for e in manifest for n in e["names"]}
    before = {n: [] for n in done}  # new entries to go before each theorem's
    proofs = {}
    for names, kind, node, imports, proof, proof_imports in lean_nodes.convert(ex):
        h = lean_nodes.blake2b256(node).hex()
        if len(names) == 1 and names[0].endswith(".wsplit") and names[0][: -len(".wsplit")] in before:
            proofs[names[0][: -len(".wsplit")]] = (proof, proof_imports)
            continue
        if h in have:
            continue
        clash = [n for n in names if n in declared]
        if clash:
            sys.exit(f"lean_split: {clash[0]} is already declared by another node")
        owner = next((t for t in done if names[0].startswith(t + ".wsplit_")), None)
        if owner is None:
            sys.exit(f"lean_split: the split exports {names[0]}, which NODES_DIR lacks")
        with open(f"{nodes_dir}/nodes/{h}", "wb") as f:
            f.write(node)
        entry = {"hash": h, "names": names, "kind": kind, "size": len(node), "imports": [i.hex() for i in imports]}
        if proof is not None:
            with open(f"{nodes_dir}/proofs/{h}", "wb") as f:
                f.write(proof)
            entry["proof_size"] = len(proof)
            entry["proof_imports"] = [i.hex() for i in proof_imports]
        before[owner].append(entry)
        have.add(h)
    out = []
    for e in manifest:
        theorem = next((n for n in e["names"] if n in before), None)
        if theorem is not None:
            out += before[theorem]
            proof, proof_imports = proofs[theorem]
            # The proof was exported for NAME.wsplit; it proves NAME's statement, node e.
            proof = lean_nodes.PROOF_MAGIC + bytes.fromhex(e["hash"]) + proof[len(lean_nodes.PROOF_MAGIC) + 32 :]
            with open(f"{nodes_dir}/proofs/{e['hash']}", "wb") as f:
                f.write(proof)
            e = dict(e, proof_size=len(proof), proof_imports=[i.hex() for i in proof_imports])
        out.append(e)
    with open(f"{nodes_dir}/manifest.json", "w") as f:
        json.dump(out, f, indent=0)


def main(argv):
    opts = {"--budget": "2000", "--stmt-ms": "10", "--trace-ms": None}
    args = []
    it = iter(argv)
    for a in it:
        if a in opts:
            opts[a] = next(it)
        else:
            args.append(a)
    if len(args) < 4:
        sys.exit(__doc__)
    project, module, nodes_dir = args[0], args[1], args[2]
    names = []
    for arg in args[3:]:
        name, _, ms = arg.partition("=")
        pct = 80
        if ms and opts["--trace-ms"]:
            pct = max(1, min(100, int(100 * float(opts["--trace-ms"]) / float(ms))))
        names.append((name, pct))
    with tempfile.TemporaryDirectory() as work:
        done = split(project, module, names, int(opts["--budget"]), int(opts["--stmt-ms"]), work)
        if done:
            merge(nodes_dir, work, done)
    for n in done:
        print(n)


if __name__ == "__main__":
    main(sys.argv[1:])
