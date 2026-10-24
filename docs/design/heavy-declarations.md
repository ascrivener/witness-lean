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
mostly sheaf cohomology, Mayer–Vietoris and algebraic geometry.

**All of Mathlib under nanoda** (`lean-host profile`, every node checked once in one environment):

| | |
|---|---|
| Nodes | 717,117: 717,116 check, none fail; 1 left out (`sorryAx`, which nothing uses) |
| Checking | 645 s, about 5.2×10¹³ gas |
| Over one refine (> 56 ms) | 618 nodes, 76 s between them: 551 theorems, 62 definitions, 5 inductives |
| Over 0.5 s | 5 nodes; the heaviest, `Proj.awayι_comp_map`, 2.1 s (about 37 refines) |

The tail is unfolding, not computation: 129 of the 618 are in algebraic geometry, 75 in algebra,
62 in category theory. The 5 inductives are 56–151 ms (at most 2.7 refines): a 104-name mutual
inductive in core's `grind`, and four Riemannian bundle structures.

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

**Mathlib's heaviest.** The same, on the six heaviest theorems, two that look computational and a
definition (instrumented times):

| Declaration | Whole check | Units | Rounds | Largest unit |
|---|---|---|---|---|
| `Proj.awayι_comp_map` | 3.4 s | 71,689 | 14 | 48.4 ms* |
| `WeierstrassCurve…sym2x_add_sub_eq_addSubMap_sym2x._proof_1_8` | 2.9 s | 40,598 | 25 | 47.1 ms* |
| `Sheaf.H.longSequence_exact` | 1.5 s | 30,910 | 18 | 29.5 ms |
| `MayerVietorisSquare.biprodAddEquiv_symm…` | 1.0 s | 19,489 | 14 | 29.2 ms |
| `Ideal.comap_fiberIsoOfBijectiveResidueField_symm` | 0.92 s | 12,764 | 13 | 29.9 ms |
| `CoalgCat.MonoidalCategoryAux.comul_tensorObj_tensorObj_right` | 0.64 s | 10,583 | 13 | 28.9 ms |
| `String.fromUTF8Lossy_surrogate_append._proof_1_10` | 0.39 s | 415 | 7 | 29.5 ms |
| `alternatingGroup.normalClosure_swap_mul_swap_five` | 0.47 s | 1,677 | 9 | 29.9 ms |
| `QuadraticModuleCat.instMonoidalCategoryStruct` (a def) | 0.54 s | 9,773 | 11 | 25.5 ms |

All decompose, and none into long chains: the computational ones are the shallowest. *The two
units over the 30 ms budget are single calls that spent about 48 ms in themselves inside the whole
check, but run alone in PolkaVM, with their facts and the traced environment, each costs at most
7.8×10⁸ gas in all (2.0×10⁸ for the Weierstrass one): they paid for growing nanoda's global term
table, a cost of the one big process, not of the step.

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
it depends on beyond its terms is the declaration's universe parameters and what the constants it
mentions mean. A check seeds a judgment only into a checker for the declaration it names. And as a
node does, a judgment imports the nodes declaring every constant it mentions, and is used only
where each is declared by one of them. The declaration's hash alone doesn't fix that: a statement
node pins what the statement mentions, not the proof, and an op loads only the nodes its check
touches, so a name could mean something else where a judgment is used than where it was made.

**Calls** run from a starting depth above every local their inputs mention, so the binders they
open are fresh and can't capture an input's local.

**Producing judgments.** A group's op names its units' calls (kind, depth, inputs, as in a
piece), trusts the environment's nodes and the judgments it cites, and has its own judgment blob
as subject. The check:
1. loads the environment and seeds its caches from the cited judgments;
2. runs each unit's call;
3. accepts the subject only if every entry in it is now in the caches with the same value.

Caches only ever hold what the kernel derived or what was seeded from attested judgments, so by
induction over the rounds every attested fact is a kernel judgment. The declaration's own node is
attested last, by the ordinary attest op with its caches seeded from the judgments it cites.

**Lazy delta steps** aren't cached in nanoda. A unit that is one runs as a call of its own (call
kind 4), so the entries it makes are attested; its result isn't an entry, so whatever needs it
runs the step again, seeded with those entries.

Why this is sound, and what that rests on: `judgment-soundness.md`.

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

## What was built

**The planner** (`vendor/nanoda/src/plan.rs`, nanoda's `trace` feature) records every infer,
whnf, definitional equality and lazy delta call of a declaration's check, with the cache entries
each made and hit, and cuts the call tree into units by call count. A unit that makes an entry a
later unit hits from outside becomes a unit of its own; a unit over budget gives up its heaviest
subtrees. Rounds are the longest path over what units need. Units are grouped into ops by their
measured replay cost (a first pass writes `costs.json`, a second plans with it), each op's calls
blob kept under witness's witness limit.

**Seeding per call.** An op cites the judgments its calls need and names, for each call, the
entries to seed just before it runs, read lazily from the cited blobs (`judgment::Lazy`), so
only the entries used are rebuilt. An op that would cite more
than 3 MB cites *relays* instead: ops that cite up to 3 MB of judgments and re-attest just the
entries needed, so later ops cite less.

**Inductives** are split by declaration, and an inductive type's check by phase (constructors,
then recursors), only when a block is over budget (`lean-host split-inductive`). A mutual block is
checked once, not once per member (`check_inductive_declar`; proposed upstream as nanoda#69): that alone
took `Lean.Meta.Grind.Arith.Cutsat.EqCnstr` from 1.32×10¹⁰ gas to 1.42×10⁹.

**`instIsIsoIndCoimageImageComparison`**, the heaviest theorem: 1,002 ops (558 of them relays) in
254 rounds, every one passing natively and in PolkaVM. The largest uses 2.55×10⁹ gas, the median
7.1×10⁸; all together 7.2×10¹¹, about 7× the declaration's whole check.

### All of Mathlib

`tools/lean/mathlib_work.py` lays out Mathlib (717,116 nodes) for witness's `attest-batches.py`,
and `scripts/mathlib-sim.sh` attests it in witness-sim:
- 51,090 batches of nodes, planned from `lean-host profile` at 40 ms each (`plan_profile.py`);
- 966 nodes too heavy for one batch (872 theorems, 89 definitions, 5 inductives), split into
  46,446 ops, planned at about 8.7×10¹³ gas: more than every other batch together;
- every batch also trusts the kernel's built-in nodes (the check's pins and what they import, 228
  nodes and 78 KB) attested below its depth (`--trust-builtins`; the converters have since been
  fixed, see the open questions). A string literal's expansion uses `String.ofList`,
  `Char.ofNat` and `List`'s constructors without naming them, so neither a node's imports nor the
  profile's lookups list them: `String.ofList_nil`, about `""`, failed without `Char.ofNat`, which
  nanoda's expansion requires to be loaded even for an empty string.

Every one of the 97,536 batches passes when checked natively (`lean-host batch-args`, then
`lean-host run`: 22 minutes on 7 threads). Two witness changes were needed to attest them:
an attestation's witness can be an extrinsic (a heavy op's calls run to 5.3 MB, and a work
package's payloads to 200 KiB), and `attest-batches.py` resumes a run and builds a sim round at
once. In witness-sim on an 8-core laptop the run attests about 1.5 batches a second, CPU-bound,
with every batch, heavy ops included, accepted the first time; it was 9% through when this was
written.

## Open questions

1. **The overhead of splitting.** A split declaration costs about 7× its whole check, mostly in
   loading the environment for every op and rebuilding cited entries. For Mathlib that's most of
   the gas. Fewer, larger ops where budget allows, and judgments cited by entry rather than by
   blob, are the levers.
2. **Latency.** The heaviest theorem takes 254 rounds, about 25 minutes of 6-second slots even
   with every core free. Rounds come from the longest chain of needs; wider units would shorten it.
3. **Literal dependencies.** The converters now make a node with a literal import what its
   expansion uses (`tools/lean/node_format.md`), so a new layout needs no built-in nodes trusted
   everywhere (`mathlib_work.py --trust-builtins`, kept for packs converted before). That changes
   node hashes, so Mathlib needs converting again to use it.
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
- One heavy declaration's ops: `lean-host pack-args PACK CLOSURE ARGS`, then `lean-host
  judgments ARGS OUT`, `lean-host judgments-ops ARGS OUT` (`VERIFY=1` writes each op's arguments
  and checks them natively), and the same again with `OUT/costs.json`; an inductive block,
  `lean-host split-inductive ARGS OUT`.
- All of Mathlib: `tools/lean/mathlib_work.py PACK PROFILE WORK`, checked natively batch by batch
  with `lean-host batch-args WORK N ARGS` and `lean-host run ARGS`, then attested with
  `WITNESS_DIR=… ATTESTERS=… scripts/mathlib-sim.sh WORK`.
