#!/usr/bin/env python3
"""Convert a lean4export NDJSON export to content-addressed declaration nodes.

    lean_nodes.py EXPORT.ndjson OUT_DIR

Writes OUT_DIR/nodes/HASH (one file per node, named by its hex hash), OUT_DIR/proofs/HASH (a
theorem's proof, named by its statement node's hash) and OUT_DIR/manifest.json. See
node_format.md for the format and docs/design/content-addressed.md for why.

Each declaration (an inductive block, with its constructors and recursors, counts as one) becomes
a node: its own tables of names, levels and expressions, numbered from scratch, and the hashes of
the nodes declaring the constants it mentions. A theorem's node is its statement; its proof is a
separate blob. The export must list declarations in dependency order, as lean4export does.
"""

import hashlib
import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import lean_bin  # noqa: E402

NODE_MAGIC = b"LEANNOD\x01"
PROOF_MAGIC = b"LEANPRF\x01"
TAG_STATEMENT = 23
TAG_PROOF = 24
DECL_KINDS = ("axiom", "thm", "def", "opaque", "quot", "inductive")


def blake2b256(data):
    return hashlib.blake2b(data, digest_size=32).digest()


def body(item):
    """An item's payload and kind, ignoring its own index."""
    for k, v in item.items():
        if k not in ("in", "il", "ie"):
            return k, v
    raise ValueError(f"empty item {item}")


class Export:
    def __init__(self, items):
        self.names, self.levels, self.exprs, self.decls = {}, {}, {}, []
        for it in items:
            if "in" in it:
                self.names[it["in"]] = it
            elif "il" in it:
                self.levels[it["il"]] = it
            elif "ie" in it:
                self.exprs[it["ie"]] = it
            elif any(k in it for k in DECL_KINDS):
                self.decls.append(it)
        # The level of each universe parameter, by its name.
        self.param_levels = {v: i for i, it in self.levels.items() for k, v in [body(it)] if k == "param"}

    def name_str(self, i):
        if i == 0:
            return ""
        k, v = body(self.names[i])
        pre = self.name_str(v["pre"])
        last = v["str"] if k == "str" else str(v["i"])
        return f"{pre}.{last}" if pre else last


class Closure:
    """The names, levels and expressions some roots reach, and the constants they mention."""

    def __init__(self, ex):
        self.ex = ex
        self.names, self.levels, self.exprs = set(), set(), set()
        self.consts = set()  # name indices of constants mentioned

    def name(self, i):
        while i and i not in self.names:
            self.names.add(i)
            i = body(self.ex.names[i])[1]["pre"]

    def level(self, i):
        stack = [i]
        while stack:
            i = stack.pop()
            if i == 0 or i in self.levels:
                continue
            self.levels.add(i)
            k, v = body(self.ex.levels[i])
            if k == "succ":
                stack.append(v)
            elif k in ("max", "imax"):
                stack.extend(v)
            elif k == "param":
                self.name(v)

    def expr(self, i):
        stack = [i]
        while stack:
            i = stack.pop()
            if i in self.exprs:
                continue
            self.exprs.add(i)
            k, v = body(self.ex.exprs[i])
            if k in ("bvar", "natVal", "strVal"):
                continue
            if k == "sort":
                self.level(v)
            elif k == "const":
                self.name(v["name"]); self.consts.add(v["name"])
                for u in v["us"]:
                    self.level(u)
            elif k == "app":
                stack += [v["fn"], v["arg"]]
            elif k in ("forallE", "lam"):
                self.name(v["name"]); stack += [v["type"], v["body"]]
            elif k == "letE":
                self.name(v["name"]); stack += [v["type"], v["value"], v["body"]]
            elif k == "proj":
                self.name(v["typeName"]); self.consts.add(v["typeName"]); stack.append(v["struct"])
            else:
                raise ValueError(f"unknown expression {k}")

    def info(self, d):
        self.name(d["name"])
        for p in d["levelParams"]:
            self.name(p)
            # lean4export exports each universe parameter's level before the declaration.
            self.levels.add(self.param_level(p))
        self.expr(d["type"])

    def param_level(self, name):
        if name not in self.ex.param_levels:
            raise ValueError(f"no level for universe parameter {self.ex.name_str(name)}")
        return self.ex.param_levels[name]


def remap(item, names, levels, exprs):
    """`item` with every index replaced by its local one."""
    k, v = body(item)
    n, l, e = names.__getitem__, levels.__getitem__, exprs.__getitem__
    ns = lambda xs: [n(x) for x in xs]
    if k == "str":
        return {k: {"pre": n(v["pre"]), "str": v["str"]}}
    if k == "num":
        return {k: {"pre": n(v["pre"]), "i": v["i"]}}
    if k == "succ":
        return {k: l(v)}
    if k in ("max", "imax"):
        return {k: [l(x) for x in v]}
    if k == "param":
        return {k: n(v)}
    if k in ("natVal", "strVal", "bvar"):
        return {k: v}
    if k == "sort":
        return {k: l(v)}
    if k == "const":
        return {k: {"name": n(v["name"]), "us": [l(x) for x in v["us"]]}}
    if k == "app":
        return {k: {"fn": e(v["fn"]), "arg": e(v["arg"])}}
    if k in ("forallE", "lam"):
        return {k: {"name": n(v["name"]), "type": e(v["type"]), "body": e(v["body"]), "binderInfo": v["binderInfo"]}}
    if k == "letE":
        return {k: {"name": n(v["name"]), "type": e(v["type"]), "value": e(v["value"]), "body": e(v["body"]), "nondep": v["nondep"]}}
    if k == "proj":
        return {k: {"typeName": n(v["typeName"]), "idx": v["idx"], "struct": e(v["struct"])}}
    if k == "inductive":
        out = {"types": [], "ctors": [], "recs": []}
        for t in v["types"]:
            t2 = dict(t, name=n(t["name"]), levelParams=ns(t["levelParams"]), type=e(t["type"]), all=ns(t["all"]), ctors=ns(t["ctors"]))
            out["types"].append(t2)
        for c in v["ctors"]:
            out["ctors"].append(dict(c, name=n(c["name"]), levelParams=ns(c["levelParams"]), type=e(c["type"]), induct=n(c["induct"])))
        for r in v["recs"]:
            rules = [dict(x, ctor=n(x["ctor"]), rhs=e(x["rhs"])) for x in r["rules"]]
            out["recs"].append(dict(r, name=n(r["name"]), levelParams=ns(r["levelParams"]), type=e(r["type"]), all=ns(r["all"]), rules=rules))
        return {k: out}
    d = dict(v)
    d["name"] = n(v["name"])
    d["levelParams"] = ns(v["levelParams"])
    d["type"] = e(v["type"])
    if k in ("thm", "def", "opaque"):
        d["value"] = e(v["value"])
        return {k: d}
    if k in ("axiom", "quot"):
        return {k: d}
    raise ValueError(f"unknown item {k}")


def tables(ex, closure):
    """Local numbering and the items defining it, in an order where each comes after what it
    uses. Export indices already have that order."""
    names = {0: 0}
    levels = {0: 0}
    exprs = {}
    for i in sorted(closure.names):
        names[i] = len(names)
    for i in sorted(closure.levels):
        levels[i] = len(levels)
    for i in sorted(closure.exprs):
        exprs[i] = len(exprs)
    lines = []
    for i in sorted(closure.names):
        lines.append(dict(remap(ex.names[i], names, levels, exprs), **{"in": names[i]}))
    for i in sorted(closure.levels):
        lines.append(dict(remap(ex.levels[i], names, levels, exprs), **{"il": levels[i]}))
    for i in sorted(closure.exprs):
        lines.append(dict(remap(ex.exprs[i], names, levels, exprs), **{"ie": exprs[i]}))
    return names, levels, exprs, lines


def items_bytes(lines):
    return lean_bin.encode(lines)[len(lean_bin.MAGIC):]


def header(magic, imports):
    w = lean_bin.Writer()
    w.out = bytearray(magic)
    w.uvar(len(imports))
    for h in imports:
        w.out += h
    return bytes(w.out)


def declared(ex, decl):
    k, v = body(decl)
    if k == "inductive":
        return [x["name"] for part in ("types", "ctors", "recs") for x in v[part]]
    return [v["name"]]


def convert(ex):
    """Yield (names declared, kind, node bytes, imports, proof bytes or None, proof imports)."""
    node_of = {}  # name index -> node hash
    for decl in ex.decls:
        k, v = body(decl)
        own = set(declared(ex, decl))
        c = Closure(ex)
        if k == "inductive":
            for part in ("types", "ctors", "recs"):
                for x in v[part]:
                    c.info(x)
                    for rule in x.get("rules", []):
                        c.name(rule["ctor"]); c.expr(rule["rhs"])
                    for nm in x.get("all", []) + x.get("ctors", []) + ([x["induct"]] if "induct" in x else []):
                        c.name(nm)
        else:
            c.info(v)
            if k in ("def", "opaque"):
                c.expr(v["value"])

        def imports_of(closure, own):
            out = set()
            for nm in closure.consts - own:
                if nm not in node_of:
                    raise ValueError(f"{ex.name_str(v['name'])} mentions {ex.name_str(nm)}, declared later or not at all")
                out.add(node_of[nm])
            return sorted(out)

        imports = imports_of(c, own)
        names, levels, exprs, lines = tables(ex, c)
        if k == "thm":
            w = lean_bin.Writer(); w.out = bytearray()
            w.byte(TAG_STATEMENT); w.uvar(names[v["name"]]); w.ints([names[p] for p in v["levelParams"]]); w.uvar(exprs[v["type"]])
            node = header(NODE_MAGIC, imports) + items_bytes(lines) + bytes(w.out)
        else:
            node = header(NODE_MAGIC, imports) + items_bytes(lines + [remap(decl, names, levels, exprs)])
        h = blake2b256(node)
        for nm in own:
            node_of[nm] = h

        proof, proof_imports = None, []
        if k == "thm":
            pc = Closure(ex)
            pc.expr(v["value"])
            for p in v["levelParams"]:
                pc.name(p); pc.levels.add(pc.param_level(p))
            # A proof can't mention its own theorem, so everything it mentions is imported.
            proof_imports = imports_of(pc, set())
            pnames, plevels, pexprs, plines = tables(ex, pc)
            w = lean_bin.Writer(); w.out = bytearray()
            w.byte(TAG_PROOF); w.uvar(pexprs[v["value"]])
            proof = PROOF_MAGIC + h + header(b"", proof_imports) + items_bytes(plines) + bytes(w.out)
        yield [ex.name_str(n) for n in declared(ex, decl)], k, node, imports, proof, proof_imports


def main(path, out_dir):
    with open(path) as f:
        ex = Export(json.loads(l) for l in f if l.strip())
    os.makedirs(f"{out_dir}/nodes", exist_ok=True)
    os.makedirs(f"{out_dir}/proofs", exist_ok=True)
    manifest = []
    for names, kind, node, imports, proof, proof_imports in convert(ex):
        h = blake2b256(node).hex()
        with open(f"{out_dir}/nodes/{h}", "wb") as f:
            f.write(node)
        entry = {"hash": h, "names": names, "kind": kind, "size": len(node), "imports": [i.hex() for i in imports]}
        if proof is not None:
            with open(f"{out_dir}/proofs/{h}", "wb") as f:
                f.write(proof)
            entry["proof_size"] = len(proof)
            entry["proof_imports"] = [i.hex() for i in proof_imports]
        manifest.append(entry)
    with open(f"{out_dir}/manifest.json", "w") as f:
        json.dump(manifest, f, indent=0)
    total = sum(e["size"] for e in manifest)
    proofs = sum(e.get("proof_size", 0) for e in manifest)
    print(f"{len(manifest)} nodes, {total} bytes of nodes, {proofs} bytes of proofs", file=sys.stderr)


if __name__ == "__main__":
    if len(sys.argv) != 3:
        sys.exit(__doc__)
    main(sys.argv[1], sys.argv[2])
