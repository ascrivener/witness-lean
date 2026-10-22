# Node format

Content-addressed Lean declarations, for checking proofs in JAM refine a few at a time instead
of as one export. `lean_nodes.py` converts lean4export NDJSON (version 3.1.0) to nodes, and nanoda
loads them (`nanoda_lib::nodes`). See [the design](../../docs/design/content-addressed.md) for
why.

## Nodes

A **node** holds one declaration. An inductive block (its types, constructors and recursors)
counts as one, and so do the quotient declarations (`Quot`, `Quot.mk`, `Quot.lift`, `Quot.ind`),
which the kernel adds together. For a theorem, the node is its **statement**: everything but the
proof.

```
node := "LEANNOD\x01" ++ u(n) ++ import^n ++ item*
```

- **`import`:** the 32-byte hash of a node declaring a constant this one mentions. Every constant
  the node mentions (in a `const` or `proj` expression) must be declared by the node itself or by
  one of its imports. Sorted, no duplicates.
- **`item`:** as in the [binary format](binary_format.md): names, levels and expressions, then the
  declaration. Indices are local: names count from 1 (0 is anonymous), levels from 1 (0 is
  zero), expressions from 0, each in the order the node lists them. So a node holds every name,
  level and expression it uses, and means the same thing wherever it's loaded.
- **Canonical form:** each table lists its entries in the order a depth-first walk from the
  declaration first finishes them (an expression after its children, function before argument;
  a name after its prefix). Binders are anonymous, with default binder info, and lets have
  `nondep` false: the kernel ignores these, and lean4export shares expressions up to them, so
  which ones an export keeps depends on what else it exports. In this form a declaration's node,
  and so its hash, is the same whichever export it came from.
- A theorem's node ends with a **statement** item instead of a declaration (tag 23: name `u32`,
  level params `[u32]`, type `u32`).

A node's **hash** is Blake2b-256 of all its bytes. It covers the hashes it imports, so it commits
to everything the declaration means, recursively. It doesn't cover a theorem's proof: any proof
of the statement will do.

## Proofs

```
proof := "LEANPRF\x01" ++ statement ++ u(n) ++ import^n ++ item* ++ value
```

- **`statement`:** the 32-byte hash of the theorem's node.
- **`import`, `item`:** as in a node, local to the proof. A proof doesn't see the statement's
  tables, so it lists what it uses again (the universe parameters' levels, say).
- **`value`:** tag 24, then the proof term's local expression index (`u32`).

## Loading

nanoda reads nodes into one environment, each after everything it imports, and checks as it goes:

- every import is loaded, and every constant mentioned is declared by the node or an import;
- no name is declared twice;
- the names the kernel treats specially (`Nat`, `Nat.add` and the other operations it computes
  with natively, `String`, `Quot`, and the permitted axioms `propext`, `Classical.choice` and
  `Quot.sound`; see `PINNED_NAMES`) are declared only by pinned nodes, whose hashes the caller
  gives. Without that, a node could declare its own `Nat.add` (or a `propext : False`) and the
  kernel would trust it by name.

A theorem statement loaded with its proof becomes a theorem, and is type-checked with it. Loaded
without one, it's an assumption, for statements already proven (in witness, attested ones).

## Packs and witnesses

The Lean check's witness, and a `lean_pack.py` pack, is a list: `u(count)` then each item as
`u(len) ++ bytes`. In attest mode it holds the batch's proofs; in reveal mode, the solver's nodes
and proofs.

`u` is unsigned LEB128 throughout.
