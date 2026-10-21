# Vendored nanoda_lib

[nanoda_lib](https://github.com/ammkrn/nanoda_lib) (Apache-2.0, see `LICENSE`), an independent
Lean 4 kernel type checker, at upstream commit `9d6964f`, with changes for running as a witness
check:

- **`no_std`** (the Lean checker spike's `nanoda-no_std.patch`, on the `spike/lean-checker`
  branch): `core`/`alloc` instead of `std`, `hashbrown` for collections, serial checking, no file
  or stdout I/O, parsing from memory (`Config::in_memory`), panics instead of process exits.
- **A binary export format** (also from the spike, see its `binary_format.md`), detected by its
  magic and about 6× cheaper to parse than lean4export's NDJSON.
- **Layers** (`src/binding.rs`): an export read as consecutive parts, each continuing the
  numbering of the ones before, so a caller can type-check only the parts not checked before, and
  bind a proof to a statement.

The CLI (`src/main.rs`) was removed: the port is the library only. Upstream's release profiles
were dropped, since only the workspace root's apply.
