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
  reused across Mathlib. That needs no renaming: nanoda's locals are de Bruijn *levels*, a local
  is the value (level, name, type), and binders open and close as a stack. A piece is a pure
  function of its input terms and its starting depth, so a run that starts at the same depth with
  the same inputs builds the same keys, and its facts match by hash, shipped as they are.

This keeps every step re-executed by validators: no ZK proof and no fraud-proof window.

## Stage 1: a native prototype

Measured on `instIsIsoIndCoimageImageComparison` with nanoda's own caches (`nanoda-profiling`
branch, `NANODA_REPLAY`, `NANODA_SPANS`, `tools/lean/fact_dag.py`).

**Pieces run alone, on their facts.** Each of the 311 pieces was re-run, at the point it starts,
on a fresh cache seeded only with the entries made in the calls it needs (a median 1,326 entries,
max 7,026), and again on an empty cache:

| 311 pieces | Seeded with their facts | Empty cache |
|---|---|---|
| Same result as the whole check | 311 | 311 |
| Median | 2.6 ms | 130 ms |
| 90th percentile | 10.6 ms | 222 ms |
| Max | 49.1 ms | 442 ms |
| Over 50 ms | 0 | 248 |

**Isolated, and in PolkaVM.** Each piece was then written out on its own (`nanoda_lib::piece`: its
call, starting depth, inputs, result and facts, with shared subterms once) and run in a fresh
checker for the declaration, its terms rebuilt with the checker's own constructors, in the
environment of the declaration's traced arguments (620 nodes, 635 KB):

| 311 pieces | |
|---|---|
| Size, facts included | median 100 KB, max 320 KB |
| Same result as the whole check, natively and in PolkaVM | 311 |
| Native run, after rebuilding terms and seeding (~1 ms) | median 2.3 ms, max 49 ms (profiling build) |
| PolkaVM gas, whole check op | median 6.5×10⁸, 90th percentile 9.1×10⁸, max 1.53×10⁹ |
| Of which loading the environment | ~5×10⁸ |

Every piece fits a refine three times over. Sharing the environment load, the 311 pack into 19
work items of 4.5×10⁹ (`lean-check` built with the research-only `pieces` feature;
`lean-host piece`, `piece-args`).

How locals reach the facts a piece hits (670,067 hits on entries made before the piece): 30% of
the facts mention only locals the piece's inputs reach, 66% locals the piece's own binders
rebuild (at or above its starting depth), 2% live context locals the inputs don't mention, and
2.4% (in 19 pieces) a reused level with a different type. All of these are built by the piece's
own computation, which the replays confirm.

**The fact DAG.** Every fact a piece needs is made by a call, which becomes a unit of its own,
with needs of its own; a unit's own work is its call minus the units nested in it, and a unit over
budget gives up its largest sub-calls that fit. Closed to a fixpoint (instrumented times; the whole
check takes 2.09 s here against 1.3 s plain):

| | |
|---|---|
| Units | 70,654, of which 43,783 trivial (3 ms between them) |
| Total work | 2.09 s: the whole check, each call done once |
| Largest unit | 39.6 ms (one top-level call's own work); every other one 30 ms or less |
| Depth | 17 rounds; critical path 77 ms |
| Needs per unit | median 1, 99th percentile 4, max 3,798 |
| Busiest round | 807 units, 712 ms of work |

So the work doesn't grow, and the rounds are few. The cost is the number of units, which have to
be grouped into work items (below).

## Design: trusted facts

The prototype seeds a piece's caches with facts as given. On chain, a check may seed only facts
an earlier attestation checked, and the rest of the design follows from that rule.

**A judgment is a subject.** A *judgment blob* holds cache entries (each a cache, a key and a
value, in the piece format's term tables, shared subterms once) and the hash of the declaration
node they belong to. It's attested and cited like a declaration node: witness already hashes
cited subjects in refine (`push_trusted`) and only lets a check trust subjects the same check
attested, so the Lean check gains a second subject kind, and witness doesn't change.

**What each fact claims.** An entry means what nanoda's cache already means. Each kind is seeded
back into the same cache, so its meaning carries over:

| Cache | Claim | If false |
|---|---|---|
| `infer_cache_check` | `e` is well typed, of type `T` | unsound |
| `infer_cache_no_check` | `T` is `e`'s type, if `e` is well typed | unsound |
| `whnf_cache`, `whnf_no_unfolding_cache` | `e` reduces to `v` | unsound |
| `eq_cache` | `x ≡ y` | unsound |
| `defeq_fail_cache`, `congr_fail_cache` | `x ≢ y`, or congruence fails | a valid proof rejected |

Failure facts should only cost completeness, since every way the kernel accepts goes through
positive judgments. That's worth confirming by review, but they're attested the same way anyway.

**Scope.** Locals are (level, name, type) values, so an entry carries its whole local context. What
it depends on beyond its terms is the environment, the declarations before its own, and the
declaration's universe parameters. The declaration node's hash fixes both, so a check seeds a
judgment only into a checker set up for that same declaration, and refuses one for any other.

**Producing judgments.** A group's op names its units' calls (kind, depth, inputs, as in a
piece), trusts the environment's nodes and the judgments it cites, and has its own judgment blob
as subject. The check:
1. loads the environment and seeds its caches from the cited judgments;
2. runs each unit's call;
3. accepts the subject only if every entry in it is now in the caches with the same value.

Caches only ever hold what the kernel derived or what was seeded from attested judgments, so by
induction over the rounds every attested fact is a kernel judgment. The declaration's own node is
attested last, by the ordinary attest op with its caches seeded from the judgments it cites.

**One gap.** Lazy delta steps aren't cached in nanoda. A unit that is one has no entry for its
parent to be seeded with, so either the check gets a cache for them, or a parent recomputes its
lazy-delta children.

**Adversarial tests**, as for the kernel itself:
- a forged entry, cited without being attested;
- an attested entry from another declaration, or under other universe parameters;
- an entry whose local has the right level but a different type;
- an `infer_cache_no_check` entry presented as `infer_cache_check`;
- a subject listing an entry its calls didn't make;
- a fact cited by an op running a different check.

### Grouping into work items

Within each round, units are packed in call order into groups. A group is one work item: it
attests its units and publishes the facts they make as one blob, cited whole by later groups. The
model (`tools/lean/fact_groups.py`, on the DAG and every needed fact's terms):
- gas is the environment load (5×10⁸), the units' own work (the whole check's gas pro rata), and
  rebuilding the facts the item reads (about 300 gas a byte, from the isolated pieces);
- a group is limited to 4.5×10⁹ gas, 3,000 citations (`MAX_BLOBS`, less the environment) and
  12 MB cited (`MAX_BLOBS_LEN` and the bundle).

| `instIsIsoIndCoimageImageComparison` | |
|---|---|
| Work items | 65, in 17 rounds; none over a limit |
| Citations per item | median 9, max 60 |
| Cited per item | max 6.2 MB |
| Blobs | median 3 KB, max 2 MB |
| Gas, rebuilding every cited fact | 2.5×10¹¹: environment 3.2×10¹⁰, work 1.0×10¹¹, facts 1.1×10¹¹ |
| Gas, rebuilding only needed facts | about 1.4×10¹¹, 1.4× the whole check |

What an item cites is 17× what it needs: 11.5× from facts in the cited blobs it doesn't use, and
1.5× from subterms repeated across blobs. So an item should rebuild only the facts it uses, with a
hint in its witness naming them. Any subset of attested facts is as sound as all of them. Blobs
per unit instead are worse: their subterms repeat (19×), and the citations reach the limit.
Capping a group's blob size helps little (500 KB: 13.9×, 68 items).

So limits aren't the problem: this declaration costs about 65 work items over 17 rounds, and a
few times its own check in gas.

## Open questions

1. **Rebuilding only what's needed.** The 1.4× assumes an item rebuilds just the facts its hint
   names, and that refine's hashing of what it cites is cheap beside that. Both need measuring
   in PolkaVM.
2. **Lazy delta steps.** A cache for them, or recomputing them (see above).
3. **More than one declaration.** Measured on `instIsIsoIndCoimageImageComparison` only.
4. **Chains.** Long reductions (`decide`, big computations) are chains rather than trees. The same
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
- The fact DAG and grouping: `NANODA_SPANS` and `NANODA_HITS` in one run, `tools/lean/fact_dag.py
  DIR OUT`, then a run with `NANODA_PIECES=OUT/facts.txt NANODA_FACTNODES=OUT/factnodes.bin`, then
  `tools/lean/fact_groups.py OUT`.
- Pieces alone: `NANODA_DUMP` with `NANODA_REPLAY` and `NANODA_PIECES`, then `lean-host piece`,
  or `lean-host piece-args` and `witness-sim check` on `lean-check` built with `--features pieces`.
