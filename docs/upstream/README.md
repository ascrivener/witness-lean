# Upstream contributions

Contributions to send upstream, not yet posted: two nanoda_lib PRs (the kernel speedups vendored in
`vendor/`) and a lean4export issue. To be submitted from the maintainer's own GitHub account.

## 1. nanoda_lib PR

**Repo:** https://github.com/ammkrn/nanoda_lib (fork it, then branch from `master`, at a3ef25a as of 2026-10-23)

**Patch:** `nanoda-whnf-no-rebuild.patch` (next to this file). Apply it with `git apply nanoda-whnf-no-rebuild.patch`.

**Title:** `whnf_no_unfolding: return the application instead of rebuilding it`

**Body:**

> `whnf_no_unfolding_aux` splits `e` into its head and arguments with `unfold_apps`. When the head doesn't reduce (a stuck projection, a constant with no quotient or recursor reduction, a lambda with no arguments, a local or a literal), it rebuilt the same application with `foldl_apps(e_fun, args)`. Expressions are hash-consed, so the rebuild re-interns every application node only to get back the pointer it started with. This returns `e` directly in those four branches.
>
> Nothing about what's accepted changes: the returned pointer is identical, and the result isn't cached in these branches (`should_cache` is false) either way.
>
> **Timing** (`nanoda_bin`, release, CPU time, paired runs on a 4-core Linux machine):
>
> | export | declarations | before | after |
> |---|---|---|---|
> | Mathlib closure of a calculus lemma | 18,323 | 7.35 / 6.61 / 7.30 s | 6.76 / 6.57 / 7.12 s |
> | Mathlib closure of `Complex.exists_root` | 48,152 | 37.9 / 34.7 / 34.0 s | 37.1 / 31.9 / 31.4 s |
>
> That's about 3–6% overall, faster in every pair. The gain is larger where allocation costs more: running nanoda in a PolkaVM guest (for on-chain proof checking), the heaviest declaration on the way to `Complex.exists_root` (`iteratedFDerivWithin_succ_apply_right`) dropped 13% in metered gas.
>
> `cargo test --release` passes (54 tests). Both exports check with no errors before and after.

## 1b. nanoda_lib PR: telescopes in one pass

**Patch:** `nanoda-telescope.patch` (next to this file, against `master` at a3ef25a, independent of 1). Apply it with `git apply nanoda-telescope.patch`.

**Title:** `Abstract a telescope's binders in one pass`

**Body:**

> `abstr_lambda_telescope` and `abstr_pi_telescope` close a telescope one binder at a time. Each step calls `abstr`, which clears the abstraction cache and walks the whole term built so far. So a telescope of n binders walks the body n times. Recursor rules for a large mutual inductive have dozens of binders (parameters, a motive per type, a minor premise per constructor, then fields), so building them is quadratic.
>
> This abstracts the body over all the binders in one call, then each binder's type over the binders before it, and wraps from the inside out. The result is the same term the binder-at-a-time version builds: that version also reaches each binder's type through the later steps' traversals. `apply_lambda` is then unused and removed. `abstr_pis` had the same binder-at-a-time loop, and `mk_rec_rule1` built four telescopes in a row (constructor arguments, minors, motives, parameters); both now make one.
>
> **Timing** (`nanoda_bin`, release, CPU time):
>
> | export | before | after |
> |---|---|---|
> | Closure of `Lean.Meta.Grind.Arith.Cutsat.EqCnstr` (a 12-type mutual inductive in Lean core; 585 declarations) | 4.08 / 4.03 / 4.19 s | 0.26 / 0.26 / 0.24 s |
> | Mathlib closure of `Complex.exists_root` (48,152 declarations) | 35.7 s | 37.4 s (within run-to-run noise) |
>
> On that block, Lean's own kernel takes 167 ms. `cargo test --release` passes (54 tests), and both exports check with no errors before and after.

## 2. lean4export issue

**Repo:** https://github.com/leanprover/lean4export (checked at df81913)

**Title:** `Exported binder names and binder info depend on what else is exported`

**Body:**

> `Export.lean` deduplicates expressions with `visitedExprs : HashMap Expr Nat`, which uses Lean's `BEq Expr` (α-equivalence: binder names and binder info are ignored). When two expressions differ only in binder names or binder info, whichever is visited first gets an index, and later occurrences reuse it. So the binders printed for a declaration depend on which declarations were exported before it.
>
> **Example.** Exporting `Lean.Grind.not_not` as part of a small closure versus as part of the closure of `Complex.exists_root` (same Mathlib commit, same toolchain) gives different binders for the same declaration: one export has a binder named `a` with one binder info, and the other has `p` with another.
>
> It doesn't affect checking: kernels ignore binder names and info. But it means an export isn't a function of the declaration alone, which breaks anything that hashes or caches exported declarations, or diffs exports. We hit this content-addressing declarations: across those two exports, the binder differences alone changed the hashes of thousands of the 18,322 shared declarations.
>
> **Also:** exporting all of Mathlib at once (`lean4export Mathlib`, no constants listed) stalled for over 20 minutes after about 650k declarations, with lean4export using CPU but writing nothing. Exporting the same constants in chunks of about 6,000 (each chunk's modules, with its constants listed) finished every chunk in under 90 s.
>
> **Possible fix.** Key `visitedExprs` on structural equality (`Expr.equal`), for example through a wrapper whose `BEq` is `Expr.equal`. `Hashable Expr` already ignores binder names, so it can stay. Exports get slightly larger, because α-equivalent copies are no longer shared, but each declaration's export no longer depends on what else is exported.
>
> (We work around it downstream by dropping binder names and info, but other consumers likely want the real names.)
