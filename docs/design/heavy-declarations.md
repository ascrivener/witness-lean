# Design: Mathlib's heavy declarations, checked on chain

Status: research. Measured 2026-10-24 on an M3 MacBook Air, PolkaJam v0.1.29, nanoda `a3ef25a`,
Lean `v4.36.0-rc1`. Nothing here is built yet; the proposal at the end is what the measurements
point to.

## The problem

Every attestation must fit one refine: 5×10⁹ gas, of which a check gets what refine can spare
(witness `MAX_CHECK_GAS`). On this machine a native millisecond of nanoda is about 82M gas in
PolkaVM (`tools/lean/gas_per_ms.py`), so a check gets roughly 55 ms of nanoda time. FTA's heaviest
declaration (`iteratedFDerivWithin_succ_apply_right`, 4.57×10⁹ gas) only just fits. Mathlib's
heaviest are far beyond that, and they're the declarations everything in algebraic geometry and
sheaf cohomology rests on.

## How heavy, and where

Lean's own kernel, re-checking all 453,104 Mathlib theorems (`tools/lean/kernel_times.lean`):
4,954 take 20 ms or more, 45 take over a second, the heaviest 16.9 s
(`AlgebraicGeometry.Proj.awayι_comp_map`).

**Lean's ranking doesn't carry over to nanoda.** nanoda profiled the combined closure of Lean's
top 60 (70,788 declarations, 85 s, `lean-host profile`):

| | nanoda | Lean's kernel |
|---|---|---|
| `WeierstrassCurve.Affine.Point.sym2x_add_sub_eq_addSubMap_sym2x._proof_1_8` | 3.2 s (≈2.6×10¹¹ gas, ~60 refines) | 3.9 s |
| `AlgebraicGeometry.Proj.awayι_comp_map` | 1.9 s | 16.9 s |
| `CategoryTheory.instIsIsoIndCoimageImageComparison` | 1.3 s | 12.7 s |
| `Polynomial.iterate_derivative_derivative_mul_X` | 7.5 ms | 9.2 s |
| `PresheafOfModules.freeObj._proof_2` | 4 ms | 15.2 s |

57 of the 60 need more than one refine under nanoda; the median needs about four. The tail is
mostly sheaf cohomology, Mayer–Vietoris and algebraic geometry. How many declarations nanoda finds
heavy across all of Mathlib is still unmeasured: that needs `lean-host profile` over all of it.

## What doesn't work

**Splitting proofs** (`lean_split.py`, fit-based since #16). None of four heavy declarations
splits:

| | Result |
|---|---|
| `Sheaf.H.longSequence_exact` | nothing to split off at any node budget, 2000 down to 125 |
| `Scheme.Hom.toNormalization_app_preimage` | up to 385 pieces; slowest 737 ms against 731 ms whole |
| `instIsIsoIndCoimageImageComparison` | best split slower than the whole (15.2 s against 12.9 s) |
| `Proj.awayι_comp_map` | best split slower than the whole (21.9 s against 18.5 s) |

The expensive comparisons happen where a sub-proof is *used* (its type against the type expected
there), so splitting the sub-proof off leaves the cost in the outer proof.

**Checkpointing the check's VM**, CoreVM style: pause the inner PVM when a refine's gas runs out
and carry its memory to the next refine (registers, PC and pages, under a state-hash chain in
accumulate). Pages a step reads that an earlier step wrote must be carried, with Merkle paths, in a
package of about 13.8 MB (witness `page-profile` branch, `witness-sim pages`):

| | Whole check | Carried into each later step |
|---|---|---|
| FTA's heaviest (2.5×10⁹-gas steps) | 6,082 pages (24 MiB) | ~2,800 pages (11 MiB): fits, just |
| `instIsIsoIndCoimageImageComparison` (4×10⁹) | over the 128 MiB a check may use | 10,000–19,000 pages (40–75 MiB) |
| `Proj.awayι_comp_map` (4×10⁹) | over the 128 MiB a check may use | 9,000–19,000 pages (36–76 MiB) |

The carried set barely shrinks with smaller steps. JAM's D³L doesn't help: it can hold the pages
between packages, and imported segments need no hashing in refine, but one work item imports at
most 3,072 segments (~12.6 MB) inside the same bundle limit.

**Rebuilding instead of carrying.** Most carried pages aren't the environment nanoda loads at the
start (rebuildable from the arguments): by the sixth step, 57 of 69 MiB were written after the
first. They're nanoda's own state:

| `instIsIsoIndCoimageImageComparison`, natively | |
|---|---|
| Interned expressions | 2.03 M (~92 MiB), append-only, never freed |
| Cache entries | 0.79 M (~24 MiB) |
| Caches cleared every 100,000 whnf calls | 15× slower, and 4.6 M expressions |

The caches can't be dropped: recomputing builds more terms, not fewer.

## Where the time goes

A call-tree profile of `instIsIsoIndCoimageImageComparison` (nanoda `nanoda-profiling` branch,
`NANODA_PROF_MS`): about 300,000 definitional-equality checks, 465,000 inferences, and 392,000
unfoldings of just 481 definitions (`DFunLike.coe` 50,000 times, `Equiv.toFun`, `EquivLike.coe`,
`Functor.map`, `HSMul.hSMul`…). The proof's rewrite casts (`Eq.mpr`) each need a check
`IsIso … =?= fun …` of about 400 ms, which come apart into `Abelian.image`/`coimage`
comparisons (~200 ms), then `parallelPair`, `HasKernel`, `Preadditive.homGroup` (~115 ms), down to
instance structures such as `Function.Injective.addGroup` (17 arguments) at ~106 ms:
typeclass-instance diamonds, reached by different paths and compared by unfolding.

**It's a tree, not one step.** Cut at 50 ms, the calls give 311 pieces covering 78% of the work;
the rest is the calls' own work between pieces, none over 27 ms. The tree is 170+ calls deep.

## Proposal: attested memoization

Split the check at the level of kernel judgments, and attest the judgments the pieces share.

- **Pieces.** A piece is a kernel run on one sub-judgment (`A ≡ B`, `infer e = T`,
  `whnf e = N`), closed over its local context: median 399 DAG nodes, max 1,068, at most 12
  locals.
- **Shared facts.** Alone, a piece is slow: run with empty caches, a call takes a median 7× (90th
  percentile 54×) its time inside the whole check, a median 121 ms. Its warm speed comes from
  results cached elsewhere in the check. Those results are judgments too. Attest them, and let a
  piece trust them: nanoda consults its trusted facts before computing, as it consults its cache.
- **Sizes.** A piece needs a median 370 facts made outside it (90th percentile 774, max 3,452);
  57,626 distinct facts across the whole check. Facts share structure heavily: a piece's facts
  reach a median 17,033 distinct nodes (~0.7 MB), max 45,298 (~1.8 MB), against a plain sum 28×
  larger. That fits a package easily, *if* shared subterms are shipped once.
- **Soundness.** Unchanged in kind: every fact is a judgment the same kernel checked on chain in
  its own attestation, cited the way attested nodes are now. The new trusted code is the
  "consult attested facts" path: facts must match exactly (terms, contexts, universe levels), and
  it needs adversarial tests of its own, as the Kernel Arena's do for the kernel.
- **Contexts.** 96% of the facts pieces need mention local variables (the declaration's
  hypotheses and binders), so facts are mostly specific to their declaration, and few would be
  reused across Mathlib. They can still be matched exactly: a cache entry that mentions a local is
  only hit while that local is in scope, so every fact a piece needs should mention only locals in
  scope where the piece starts. State a piece as a judgment under that context, and each fact
  closed over a prefix of it; a piece run opens the context as fresh locals, instantiates its facts
  with them, and seeds its caches, after which lookups match by hash as usual.

This keeps every step re-executed by validators: no ZK proof and no fraud-proof window.

## Open questions

1. **The fact DAG's total work and depth.** Checking a fact can need other facts. Each entry is
   computed once, so total work should stay near the original, plus loading each attestation's
   inputs; the depth sets how many rounds attesting takes. Unmeasured.
2. **Shipping facts with sharing.** The 28× saving needs subterms content-addressed and carried
   once, as witness-lean's nodes are, without a Merkle path per node outweighing them. Facts as
   self-contained blobs would be 18–120 MB a piece.
3. **More than one declaration.** Measured on `instIsIsoIndCoimageImageComparison` only.
4. **Matching facts across contexts.** That every fact a piece needs mentions only locals in scope
   at its start follows from how nanoda creates locals, but is unmeasured; universe parameters need
   the same treatment.
5. **Chains.** Long reductions (`decide`, big computations) are chains rather than trees. The same
   mechanism attests them link by link (`a ≡ a₁ ≡ a₂ …`) if the intermediate terms stay small.
   None of the heavy tail measured so far is of this kind.

If attested memoization falls through, the fallbacks move the big state off chain: a ZK proof of
the nanoda run that refine verifies, or optimistic attestations with bisection down to a disputed
PVM step.

## Reproducing

- Lean's ranking: `tools/lean/kernel_times.lean`.
- nanoda's: export the candidates' closure in one go (`lake env lean4export Mathlib -- NAME…`),
  `lean-host convert --pack`, write the manifest as `manifest.jsonl`, `lean-host profile`.
- Page working sets: witness `page-profile` branch, `witness-sim pages CHECK ARGS WINDOW`, on a
  batch's arguments from `lean-host args`.
- nanoda's memory, call tree, cold re-runs and facts: witness-lean `nanoda-profiling` branch,
  `lean-host run ARGS` with the variables its commit lists. The facts measurement takes two runs:
  `NANODA_HITS` to log cache hits, then (after cutting the tree at 50 ms) `NANODA_PIECES` with each
  piece's needed entries.
