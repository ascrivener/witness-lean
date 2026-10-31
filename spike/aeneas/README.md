# Spike: proofs about Rust code, checked by witness-lean

Can a bounty pay for a proof about real Rust code? Here the path is:
- [Charon](https://github.com/AeneasVerif/charon) extracts the Rust;
- [Aeneas](https://github.com/AeneasVerif/aeneas) translates it to Lean;
- a proof is written about the translation;
- witness-lean checks that proof in witness-sim with the check as it is, pins and all.

It works end to end, with no change to the check.

## What's here

```
leb128/      a Rust crate: an unsigned LEB128 u32 decoder, with a loop, slice indexing,
             bit operations and early returns
lean/        Leb128.lean, Aeneas's translation (generated, untouched); two theorems about it;
             a Lake project on Aeneas's Lean library (Lean v4.35.0, Mathlib v4.35.0)
probe/       common Rust features, run through Charon and Aeneas to see what translates
pins-v4.35.0.*  the pins lean_pins.py makes for Lean v4.35.0
```

`scripts/lean-e2e.sh aeneas`, `aeneas-correct` and `aeneas-fnv` run the theorems as bounties in
witness-sim. Each is posted, committed, revealed and paid, after Aeneas's library closure is
attested.

## Results

**Two theorems about `decode_u32`, both checked:**

| Theorem | Says | Proof |
|---|---|---|
| `decode_u32_spec` | never panics or overflows on any input; a decoded value took 1 to 5 bytes, all within the buffer | 7 lines: the loop's measure and invariant, then `step*`, `simp_all`, `scalar_tac` |
| `decode_u32_correct` | a decoded value is exactly the LEB128 value of the bytes taken: every byte but the last has its continuation bit set, the last doesn't, and the 7-bit digits add up | about 60 lines: a loop invariant, two lemmas about digits, two about the continuation bit |

Both depend only on `propext`, `Classical.choice` and `Quot.sound`.

**Checking, in witness-sim:**

| | `decode_u32_spec` | `decode_u32_correct` |
|---|---|---|
| Closure | 4,754 nodes (2.7 MB statements, 4.1 MB proofs) | 5,190 nodes (3.0 MB statements, 4.5 MB proofs) |
| Library attested | 158 batches over 74 depths, 22 rounds | 176 batches over 74 depths, 24 rounds |
| Attest gas | median 3.0×10⁸, max 1.8×10⁹ | median 3.0×10⁸, max 1.8×10⁹ |
| Reveal gas | 3.4×10⁸ (7% of a refine) | 1.3×10⁹ (25% of a refine) |

The library is mostly Aeneas's support library and the slice of Mathlib it uses. It's attested
once and cited by every bounty after, like Mathlib in the other examples.

**The toolchain didn't matter.** Aeneas pins Lean v4.35.0, and the check is built for
v4.36.0-rc1. But all 26 pinned nodes hash the same on both (`pins-v4.35.0.txt` matches
`check/pins.txt`), so the existing check accepts v4.35.0 exports. Only lean4export had to be
built for v4.35.0, from its commit on that toolchain. The pins won't always survive a toolchain
change, but here they did.

## Coverage (probe/)

Run through Charon and Aeneas nightly-2026.10.31:

| Feature | Result |
|---|---|
| `while` and `loop`, early `return`, slice indexing, bit operations, integer casts | translates |
| structs with references, `&mut self` methods | translates |
| `?` on `Result` | translates |
| `?` on `Option` | translates, but the standard library's `Try` impl for `Option` comes out as **two axioms**. witness-lean refuses any axiom but the three permitted, so these need definitions supplied by hand (`-split-files`). That's easy, but it's a gap in Aeneas's library. |
| `for` over a slice iterator, `for` over a range | translates (ranges with warnings about the `Step` trait model) |
| `Vec::new`, `push` | translates |
| traits with generic functions | translates |
| iterator adaptors with closures (`iter().copied().max_by_key(...)`) | **Aeneas fails** on the whole crate, until the function is removed |

Not tried: `unsafe` (Aeneas doesn't support it), concurrency, `dyn`, complex lifetimes.

## Real crates (real/)

Five small, widely used crates from crates.io, unmodified, run through Charon and Aeneas, then
type-checked in Lean. "Axioms" are standard-library items Aeneas has no model for: any proof whose
closure reaches one is refused by the check.

| Crate | Lines | Translation | Lean | Notes |
|---|---:|---|---|---|
| fnv 1.0.7 | 367 | complete | type-checks | 3 axioms, all `HashMap`/`HashSet` type aliases the hasher doesn't use. **`Hasher::write` is proved to compute exactly FNV-1a** (`lean/FnvSpec.lean`, a 46-line file), and checked in witness-sim (`lean-e2e.sh aeneas-fnv`): a 3,793-node library in 130 batches, max 1.2×10⁹ gas, then a reveal of 2.8×10⁷. |
| crc32fast 1.4.2 | 1,390 | complete | type-checks | The table-driven CRC (`update_slow`, the slicing-by-16 `update_fast_16`) and `combine` translate. The SIMD and hardware-CRC paths don't appear: Charon translates the build it's given, and in this one `specialized::State::new` is the stub returning `None`. 4 axioms, all `Debug` formatting and `unwrap_or_else`. |
| leb128 0.2.5 | 746 | complete | 2 errors | Built on `std::io::Read`/`Write`: 8 axioms (I/O errors, `write_all`), and Aeneas's model of `std::error::Error` lacks `source`. The arithmetic is there, but everything goes through I/O. |
| adler 1.0.2 | 433 | partial | 2 errors | Iterator `zip` isn't in Aeneas's model. |
| hex 0.4.3 | 686 | partial | 30 errors | Iterator adaptors (`zip`, `skip`, `map`, `enumerate`), closures, `char`: 26 axioms, 3 `sorry`s. |

So two of five crates translate into Lean that type-checks, and one has a real proof checked end
to end. The failures are all the same kind: the standard library's iterator, I/O and formatting
traits, which Aeneas's Lean library doesn't model yet. Plain loops over slices and integers work.

## What it means

- **The checking side is done.** witness-lean checks proofs about Aeneas-translated Rust with no
  change, at modest gas: the reveal used 7% of a refine for the no-panic proof, 25% for
  full correctness.
- **Coverage is the main limit.** Straight-line and loop-heavy code (parsers, encoders,
  arithmetic) works. Idiomatic iterator chains don't yet. Standard-library gaps show up as axioms,
  which the check rightly refuses, so each one needs a hand-written definition first.
- **Proof effort depends on the property.** Absence of panics and overflow is nearly automatic:
  Aeneas's `step*` and `scalar_tac` do almost all of it. Functional correctness needs a real loop
  invariant and a few lemmas: here, an AI agent (Claude) took about 15 minutes and half a dozen
  attempts against Lean's errors, for a 20-line function. That's the work bounties would pay
  agents for.
- **Trust in the translation stays off chain.** The bounty fixes the Lean model by its hash.
  Anyone can re-run Charon and Aeneas on the crate and get the same model; the check doesn't need
  to.

## Reproducing

The Lake project expects Aeneas's release bundle (with its Lean library) at
`../../../../tools/aeneas/aeneas-bin`, relative to `lean/`.

```bash
# Aeneas and Charon: nightly-2026.10.31-ab34bd2, macOS aarch64, from AeneasVerif/aeneas releases
rustup toolchain install nightly-2026-09-17 --profile minimal -c rustc-dev,llvm-tools,rust-src,miri
(cd leb128 && charon cargo --preset=aeneas && aeneas -backend lean leb128.llbc -dest ../lean)
(cd lean && lake build)
# lean4export at its v4.35.0 commit (5a9a355)
WITNESS_SIM=1 WITNESS_DIR=../witness LEAN4EXPORT=.../lean4export scripts/lean-e2e.sh aeneas-correct
```
