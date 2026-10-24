#!/usr/bin/env python3
"""Make the pins the Lean check is built with: the nodes allowed to declare the kernel's special
names (`Nat`, `Nat.add`, the permitted axioms and the like; lean_batches.PINNED).

    LEAN4EXPORT=path/to/lean4export lean_pins.py PROJECT OUT

Exports every pinned name from Lean core (`Init`) in Lean project PROJECT, whose lean-toolchain
the pins are for, converts the export to nodes (lean_nodes.py), and writes OUT.bin (the nodes'
hashes, 32 bytes each, sorted) and OUT.txt (each in hex with the names it declares). Nodes are
canonical, so a pinned node hashes the same in every export on one toolchain: these pins serve
any library built on it, and a new toolchain needs new pins (and so a new check).
"""

import json
import os
import subprocess
import sys
import tempfile

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import lean_nodes  # noqa: E402
from lean_batches import PINNED  # noqa: E402


def main(project, out):
    with tempfile.TemporaryDirectory() as tmp:
        with open(f"{tmp}/export.ndjson", "w") as f:
            subprocess.run(["lake", "env", os.environ["LEAN4EXPORT"], "Init", "--", *sorted(PINNED)],
                           cwd=project, stdout=f, check=True)
        lean_nodes.main(f"{tmp}/export.ndjson", f"{tmp}/nodes")
        with open(f"{tmp}/nodes/manifest.json") as f:
            manifest = json.load(f)
    pinned = {e["hash"]: sorted(PINNED & set(e["names"])) for e in manifest if PINNED & set(e["names"])}
    missing = PINNED - {n for names in pinned.values() for n in names}
    if missing:
        sys.exit(f"lean_pins.py: no node declares {sorted(missing)}")
    with open(f"{out}.bin", "wb") as f:
        f.write(b"".join(bytes.fromhex(h) for h in sorted(pinned)))
    toolchain = open(f"{project}/lean-toolchain").read().strip()
    with open(f"{out}.txt", "w") as f:
        f.write(f"# The Lean check's pins, for {toolchain} (tools/lean/lean_pins.py).\n")
        for h in sorted(pinned):
            f.write(f"{h} {' '.join(pinned[h])}\n")
    print(f"{len(pinned)} pinned nodes for {toolchain}", file=sys.stderr)


if __name__ == "__main__":
    if len(sys.argv) != 3:
        sys.exit(__doc__)
    main(*sys.argv[1:])
