# Why seeding judgments is sound

A heavy declaration is checked in pieces (`heavy-declarations.md`): judgment ops attest kernel
cache entries, and later ops, and finally the declaration's own check, start with those entries
in their caches. This note argues that this can't make the check accept anything it wouldn't
accept from scratch, and lists what the argument rests on, for review.

**Claim.** If the Lean check attests a declaration D with judgments seeded into its caches, then
nanoda checking D from scratch, in the same environment, accepts D too.

## The argument

**1. The kernel already trusts its caches.** nanoda keeps seven caches (`TcCache`):

| Cache | An entry claims |
|---|---|
| `infer_cache_check` | `e` is well typed, of type `T` |
| `infer_cache_no_check` | `T` is `e`'s type, if `e` is well typed |
| `whnf_cache` | `e`'s weak head normal form is `v` |
| `whnf_no_unfolding_cache` | the same, without unfolding definitions |
| `eq_cache` | `x ≡ y` |
| `defeq_fail_cache` | `x ≢ y`, in eager mode or not |
| `congr_fail_cache` | congruence fails on `x` and `y` |

When a lookup finds an entry, the kernel uses it in place of the computation that made it. So
nanoda's soundness already assumes every entry in its caches is what the kernel would compute.
A check that starts with extra entries, each of which the kernel would compute for D, takes the
same decisions as one without them, only sooner. Everything below shows that every seeded entry
is of that kind: **made by the kernel, and meaning the same where it's seeded as where it was
made.**

**2. Every attested entry was made by the kernel.** A judgment is attested by a judgment op,
which loads D's environment, runs the calls its witness lists (an inference, a whnf, a
definitional equality or a lazy delta step) with nanoda, and accepts its judgment only if each
entry in it is then in the caches with the same value (`Nodes::attest_judgments`, then
`judgment::holds`). An entry gets into the caches in one of three ways:
- the kernel made it, running a call;
- it was seeded before a call from a judgment the op cites: witness lets a check trust only
  subjects it attested itself, and attestations land in order, so by induction on that order
  each was made by the kernel;
- it's a `whnf_no_unfolding_cache` entry no call made (a call can skip it through a cached
  shortcut its traced run couldn't take): the op computes it with nanoda's own
  `whnf_no_unfolding` and keeps it only if the value matches. That cache is a fact about
  reduction alone: no definitions unfolded, no typing.

So an attested judgment holds only entries the kernel derived, directly or from earlier ones.

**3. An entry means the same where it's seeded.** Within one run, an entry is used where it was
made. Seeding moves it to another run, so its meaning must not depend on anything that run could
differ in:
- *The declaration.* A judgment's header names D's node hash, and a check seeds it only into a
  checker for D (`judgments_for`, `attest_judgments`): the same universe parameters and the same
  declaration info.
- *The constants.* A judgment imports the nodes declaring every constant its entries mention. To
  attest it, each mentioned constant must be loaded and declared by one of them; to cite it, each
  loaded one must be (`Nodes::check_imports`). So a constant in an entry can't mean something else
  where it's used: D's hash alone wouldn't fix that, since a statement node pins what the
  statement mentions, not the proof, and an op loads only the nodes it touches.
- *The local context.* A local is a de Bruijn level, a name and a type, so an expression with
  free locals carries what they are. `e : T` about locals holds wherever those same locals are.
- *Fresh binders.* A call runs from a starting depth above every local its inputs mention
  (`judgment::run` refuses one that doesn't), so the binders it opens can't be taken for an
  input's local.
- *Which cache.* An entry goes back into the cache it came from: `infer_cache_no_check` never
  becomes `infer_cache_check`, and a failure in eager mode stays one.

**4. So the claim holds.** The declaration's own attestation is the ordinary attest op, with its
caches seeded from the judgments it cites (`Nodes::check_with`). By 2 and 3, every seeded entry
is one the kernel would compute in D's check, so by 1 it accepts only if checking D from scratch
does.

## What soundness doesn't need

- **Seeding each call just before it runs.** A judgment op seeds each call with only the cited
  entries it hit when traced, just before it runs. Seeding everything first would still be sound
  (every entry is true), but a call could then take shortcuts its traced run didn't, and skip
  making entries the judgment claims: the op would be refused. Just-in-time seeding is for the
  replay to make what the plan says. The declaration's own check seeds everything first.
- **Relays.** A relay op re-attests entries it cites (call kind 5, seeds only) to keep later ops'
  cited bytes down. It adds no entries the kernel didn't make.
- **The planner.** Planning runs off chain and only chooses calls and groups. A bad plan makes
  ops that are refused, never ones that are wrong.

**Failure entries** (`defeq_fail_cache`, `congr_fail_cache`) are attested like the rest, so the
argument covers them. They're also the less dangerous kind: a false failure can make the kernel
reject or try another path, but every way it accepts goes through positive facts. That's worth
confirming by review rather than relying on.

## What the argument rests on

1. **nanoda is sound, its caches included.** Nothing new is trusted here: this is the kernel the
   check already relies on. It passes the Lean Kernel Arena's kernel-bug suite
   (`tools/lean/arena_bugs.py`).
2. **Cache entries are context-free.** Step 3 assumes an entry's truth depends only on its terms,
   the declaration and the constants' meanings. If some kernel path decided something from state
   outside the expressions (a flag, a counter, a lookup into a local context kept elsewhere), an
   entry made under one state could be false under another. This is the step most worth a kernel
   author's review: every place nanoda writes a cache, and what that write depends on.
3. **The judgment code is right.** Reading entries back into a checker, the import checks, the
   depth check and `holds` are new trusted code (`src/judgment.rs`, `src/nodes.rs`).
4. **Witness passes as trusted only what this check attested.** Enforced by witness's rules, with
   their own tests.

## Tests

`check/src/tests.rs`, one per rule:

| Rule | Test |
|---|---|
| An entry the calls didn't make is refused | `entries_must_be_made_by_the_calls` |
| A forged entry is refused as a subject, believed only when cited (attested) | `forged_judgments_are_refused` |
| A computed whnf holds only with its true value | `whnf_without_unfolding_is_computed_if_not_made` |
| A judgment is for one declaration | `judgments_are_for_one_declaration` |
| A judgment imports what it mentions | `judgments_import_what_they_mention` |
| A constant means what the judgment's imports declare | `a_judgment_means_what_its_imports_declare` |
| Attesting needs what the judgment mentions loaded | `attesting_a_judgment_needs_what_it_mentions_loaded` |
| A local with the right level but another type is another local | `locals_carry_their_types` |
| A call seeds only from judgments the op cites | `calls_seed_only_from_cited_judgments` |
