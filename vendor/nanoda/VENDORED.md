# Vendored nanoda_lib

[nanoda_lib](https://github.com/ammkrn/nanoda_lib) (Apache-2.0, see `LICENSE`), an independent
Lean 4 kernel type checker, at upstream commit `a3ef25a` (2026-10-23: recursor and nested-inductive
field-count validation, #63 and #65), with changes for running as a witness check:

- **`no_std`** (the Lean checker spike's `nanoda-no_std.patch`, on the `spike/lean-checker`
  branch): `core`/`alloc` instead of `std`, `hashbrown` for collections, serial checking, no file
  or stdout I/O, parsing from memory (`Config::in_memory`), panics instead of process exits.
- **A binary export format** (also from the spike, see its `binary_format.md`), detected by its
  magic and about 6× cheaper to parse than lean4export's NDJSON.
- **Content-addressed nodes** (`src/nodes.rs`, and node mode in `src/parser.rs`): declarations
  that each number their names, levels and expressions locally and name the nodes they use by
  hash, loaded into one environment after their imports, with every constant they mention
  pinned, and the kernel's special names (`Nat.add`, the permitted axioms) pinned to given
  nodes. See witness-lean's `tools/lean/node_format.md`.
- **Judgments** (`src/judgment.rs`, and `Nodes::check_with` and `Nodes::attest_judgments` in
  `src/nodes.rs`): kernel cache entries written out and read back into a checker with its own
  constructors, so an attested entry can seed a later check of the same declaration. A judgment
  imports, as a node does, the nodes declaring every constant it mentions; a call runs from a
  starting depth above its inputs' locals. See witness-lean's
  `docs/design/heavy-declarations.md`. `lazy_delta_step` is `pub(crate)` for running it as a
  call, and `SortedPair`'s fields for writing its entries.

The crate is `no_std` except under test: upstream's tests run with std (and `rand`, a
dev-dependency), reading their exports through `Config::in_memory`'s parser (`src/tests/util.rs`).
`cargo test -p nanoda_lib` runs the same 54 tests as upstream.

**Soundness regressions.** `tools/lean/arena_bugs.py` runs the Lean Kernel Arena's 20 known
kernel bugs (its `tests/bugs`, each an export a sound kernel must reject) through nanoda, pinning
each export's own nodes as an attacker on the check's toolchain would, and through the check. At
`a3ef25a` the kernel rejects all 20. At `9d6964f`, the commit vendored before, it accepted
`nested-rec-rule-nfields` (a nested inductive's recursor rule with the wrong field count), which
upstream's #63 fixed: run it again whenever nanoda is updated.

The CLI (`src/main.rs`) was removed: the port is the library only. Upstream's release profiles
were dropped, since only the workspace root's apply.
