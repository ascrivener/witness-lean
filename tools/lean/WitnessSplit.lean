/-
Split a theorem's proof into smaller theorems, so each can be checked in its own refine.

    #witness_split Foo 2000 10 60

walks Foo's proof bottom-up. Each sub-proof still at least 2000 expression nodes (counting those
already split off as just their reference) becomes a theorem `Foo.wsplit_<k>` over the local
variables it needs, and is replaced by a reference to it, if the kernel checks the new statement
alone in at most 10 ms: each piece's statement is checked again on its own, so one over expensive
types can cost more than it saves. Only proofs are split off. Any two proofs of a proposition are
definitionally equal, so a reference checks wherever the sub-proof did. The rewritten proof is
`Foo.wsplit`, with Foo's statement.

The split has to fit: every piece (the rewritten proof among them) must check in at most 60% of
the time Foo's own proof takes, the share of a refine Foo is over by. A split that doesn't fit
is tried again finer, with half the budget, down to 64 nodes, so the part of the proof that's
slow comes apart further. The command reports `split` for the first split that fits; or, if none
does, for the one with the fastest slowest piece, if that's at least 5% faster than the whole (it
may still bring the proof under a hard limit); else `kept`, when the proof's cost is one step
that doesn't come apart. Timings are the kernel's, best of two.

`lean_split.py` compiles a file of these commands, exports the results and attaches `Foo.wsplit`'s
proof to Foo's statement node.
-/
import Lean

open Lean Meta Elab Command

namespace WitnessSplit

structure State where
  cache : Std.HashMap Expr (Expr × Nat) := {}
  lemmas : Array Name := #[]

abbrev M := StateRefT State MetaM

/-- The local variables `e` and `type` need, with what those need in turn, in context order. -/
def needed (e type : Expr) : MetaM (Array Expr) := do
  let lctx ← getLCtx
  let mut st := collectFVars (collectFVars {} e) type
  for decl in lctx.decls.toArray.reverse do
    if let some decl := decl then
      if st.fvarSet.contains decl.fvarId then
        st := collectFVars st decl.type
        if let some v := decl.value? then
          st := collectFVars st v
  let mut out := #[]
  for decl in lctx do
    if st.fvarSet.contains decl.fvarId then out := out.push decl.toExpr
  return out

/-- Split `e` off as a theorem, unless checking its statement alone takes the kernel more than
`stmtMs` milliseconds: every split-off theorem's statement is checked again on its own, so one over
expensive types can cost more than it saves. -/
def splitOff (base : Name) (lps : List Name) (stmtMs : Nat) (e : Expr) : M (Option Expr) := do
  let type ← instantiateMVars (← inferType e)
  let fvs ← needed e type
  let name := base ++ Name.mkSimple s!"wsplit_{(← get).lemmas.size}"
  let lemmaType ← instantiateMVars (← mkForallFVars fvs type)
  let t0 ← IO.monoNanosNow
  let ok := match (← getEnv).toKernelEnv.addDecl {}
      (.axiomDecl { name, levelParams := lps, type := lemmaType, isUnsafe := false }) with
    | .ok _ => true
    | .error _ => false
  if !ok || (← IO.monoNanosNow) - t0 > stmtMs * 1000000 then return none
  let value ← instantiateMVars (← mkLambdaFVars fvs e)
  addDecl (.thmDecl { name, levelParams := lps, type := lemmaType, value })
  modify fun s => { s with lemmas := s.lemmas.push name }
  let args ← fvs.filterM fun x => return !(← x.fvarId!.isLetVar)
  return mkAppN (.const name (lps.map .param)) args

/-- `e` with its big sub-proofs split off, and its size after that. -/
partial def visit (base : Name) (lps : List Name) (budget stmtMs : Nat) (e : Expr) : M (Expr × Nat) := do
  if let some r := (← get).cache[e]? then return r
  let go := visit base lps budget stmtMs
  let (e', n) ← match e with
    | .app f a => do
      let (f', n₁) ← go f
      let (a', n₂) ← go a
      pure (mkApp f' a', n₁ + n₂ + 1)
    | .lam x t b bi => withLocalDecl x bi t fun v => do
      let (b', n) ← go (b.instantiate1 v)
      pure (← mkLambdaFVars #[v] b', n + 1)
    | .letE x t v b _ => do
      let (v', n₁) ← go v
      withLetDecl x t v' fun y => do
        let (b', n₂) ← go (b.instantiate1 y)
        pure (← mkLetFVars #[y] b', n₁ + n₂ + 1)
    | .mdata d b => do
      let (b', n) ← go b
      pure (.mdata d b', n)
    | .proj s i b => do
      let (b', n) ← go b
      pure (.proj s i b', n + 1)
    | _ => pure (e, 1)
  let r ← if n ≥ budget && (← isProof e') then
      match ← splitOff base lps stmtMs e' with
      | some ref => pure (ref, 1)
      | none => pure (e', n)
    else pure (e', n)
  modify fun s => { s with cache := s.cache.insert e r }
  return r

/-- Milliseconds the kernel takes to check `decl` (best of two). -/
def kernelMs (decl : Declaration) : CoreM Nat := do
  let mut best := none
  for _ in [0:2] do
    let t0 ← IO.monoNanosNow
    match (← getEnv).toKernelEnv.addDecl {} decl with
    | .ok _ => pure ()
    | .error _ => throwError "witness_split: the kernel rejected {decl.getNames}"
    let ms := ((← IO.monoNanosNow) - t0) / 1000000
    best := some (min ms (best.getD ms))
  return best.getD 0

def thmMs (name : Name) : CoreM Nat := do
  let .thmInfo info ← getConstInfo name | throwError m!"{name} is not a theorem"
  kernelMs (.thmDecl { info with name := name ++ `witness_split_timing })

/-- Split `name`'s proof, splitting off sub-proofs of `budget` nodes or more, and add the result
(`name.wsplit` and the pieces) to the environment. Returns the slowest piece's time and how many
theorems were split off, and logs which piece is slowest. -/
def attempt (name : Name) (info : TheoremVal) (budget stmtMs : Nat) : TermElabM (Nat × Nat) := do
  let ((value, _), st) ← (visit name info.levelParams budget stmtMs info.value).run {}
  let value ← instantiateMVars value
  let split := name ++ `wsplit
  addDecl (.thmDecl { name := split, levelParams := info.levelParams, type := info.type, value })
  let mut most ← thmMs split
  let mut slowest := split
  for l in st.lemmas do
    let t ← thmMs l
    if t > most then (most, slowest) := (t, l)
  logInfo m!"witness_split try {name}: budget {budget}, {st.lemmas.size} theorems, slowest {slowest} at {most} ms"
  return (most, st.lemmas.size)

/-- The smallest budget tried, in expression nodes. -/
def minBudget : Nat := 64

elab "#witness_split " id:ident budget:num stmtMs:num pct:num : command => liftTermElabM do
  let name ← realizeGlobalConstNoOverloadWithInfo id
  let .thmInfo info ← getConstInfo name | throwError m!"{name} is not a theorem"
  let was ← thmMs name
  let target := was * pct.getNat / 100
  let env ← getEnv
  -- The best split so far: its slowest piece, its budget and how many theorems it split off.
  let mut best : Option (Nat × Nat × Nat) := none
  let mut size := budget.getNat
  while size ≥ minBudget do
    setEnv env
    let (most, pieces) ← attempt name info size stmtMs.getNat
    if pieces > 0 then
      if best.all (fun (m, _, _) => most < m) then best := some (most, size, pieces)
      if most ≤ target then break
    size := size / 2
  setEnv env
  match best with
  | some (most, chosen, pieces) =>
    if most * 20 < was * 19 then
      let (most, _) ← attempt name info chosen stmtMs.getNat
      let fits := if most ≤ target then "fits" else "over"
      logInfo m!"witness_split split {name}: {pieces} theorems at budget {chosen}, slowest {most} ms, was {was} ms ({fits} {target} ms)"
      return
    logInfo m!"witness_split kept {name}: best {pieces} theorems at budget {chosen}, slowest {most} ms, was {was} ms"
  | none => logInfo m!"witness_split kept {name}: nothing to split off, {was} ms"

end WitnessSplit
