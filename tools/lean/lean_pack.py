#!/usr/bin/env python3
"""Pack nodes and proofs from a lean_nodes.py output directory into one blob.

    lean_pack.py DIR [NAME...] > PACK

The pack is a list, as the Lean check's witness is: a count, then each item's length and bytes,
all unsigned LEB128. It holds the nodes declaring NAMEs (every node if none are given), in
dependency order, then their proofs. Used for test fixtures and for reveal witnesses.
"""
import json
import sys


def uvar(n):
    out = bytearray()
    while True:
        b = n & 0x7F
        n >>= 7
        if n:
            out.append(b | 0x80)
        else:
            out.append(b)
            return bytes(out)


def pack(items):
    return uvar(len(items)) + b"".join(uvar(len(i)) + i for i in items)


def main(d, names):
    manifest = json.load(open(f"{d}/manifest.json"))
    if names:
        manifest = [e for e in manifest if set(e["names"]) & set(names)]
    nodes = [open(f"{d}/nodes/{e['hash']}", "rb").read() for e in manifest]
    proofs = [open(f"{d}/proofs/{e['hash']}", "rb").read() for e in manifest if "proof_size" in e]
    sys.stdout.buffer.write(pack(nodes + proofs))


if __name__ == "__main__":
    if len(sys.argv) < 2:
        sys.exit(__doc__)
    main(sys.argv[1], sys.argv[2:])
