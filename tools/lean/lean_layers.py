#!/usr/bin/env python3
"""Cut a lean4export NDJSON export into consecutive layers.

    lean_layers.py EXPORT MAX_BYTES OUT_PREFIX

Writes OUT_PREFIX-0.ndjson, OUT_PREFIX-1.ndjson, ... and prints their names. Each layer is a run
of the export's lines, cut just after a declaration once the layer has reached MAX_BYTES (so a
layer can exceed MAX_BYTES by one declaration and what it needs).

No renumbering is needed: every name, level and expression refers only to earlier items, so each
layer continues the numbering of the layers before it, and the checker reads them in order as one
export. That is also why a layer only means something after exactly those layers.
"""

import json
import sys

DECLARATIONS = ("def", "thm", "inductive", "axiom", "opaque", "quot")


def is_declaration(line):
    return any(key in DECLARATIONS for key in json.loads(line))


def main(path, max_bytes, prefix):
    layers, current, size = [], [], 0
    with open(path) as f:
        for line in f:
            current.append(line)
            size += len(line)
            if size >= max_bytes and is_declaration(line):
                layers.append(current)
                current, size = [], 0
    if current:
        layers.append(current)
    for i, lines in enumerate(layers):
        name = f"{prefix}-{i}.ndjson"
        with open(name, "w") as out:
            out.writelines(lines)
        print(name)


if __name__ == "__main__":
    if len(sys.argv) != 4:
        sys.exit(__doc__)
    main(sys.argv[1], int(sys.argv[2]), sys.argv[3])
