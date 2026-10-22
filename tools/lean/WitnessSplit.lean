/-
Split a theorem's proof into smaller theorems, so each can be checked in its own refine.

    #witness_split Foo 2000 10

walks Foo's proof bottom-up. Each sub-proof still at least 2000 expression nodes (counting those
already split off as just their reference) becomes a theorem `Foo.wsplit_<k>` over the local
variables it needs, and is replaced by a reference to it, if the kernel checks the new statement
alone in at most 10 ms: each piece's statement is checked again on its own, so one over expensive
types can cost more than it saves. Only proofs are split off. Any two proofs of a proposition are
definitionally equal, so a reference checks wherever the sub-proof did.

The rewritten proof is added as `Foo.wsplit`, with Foo's statement. The command then reports
`split` if the kernel checks every piece in under 80% of the time Foo's own proof takes, else
`kept`: a proof whose cost is one expensive step doesn't come apart.

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

elab "#witness_split " id:ident budget:num stmtMs:num : command => liftTermElabM do
  let name ← realizeGlobalConstNoOverloadWithInfo id
  let .thmInfo info ← getConstInfo name | throwError m!"{name} is not a theorem"
  let ((value, _), st) ← (visit name info.levelParams budget.getNat stmtMs.getNat info.value).run {}
  let value ← instantiateMVars value
  let split := name ++ `wsplit
  addDecl (.thmDecl { name := split, levelParams := info.levelParams, type := info.type, value })
  -- Keep the split only if no piece costs close to what the whole proof did.
  let was ← thmMs name
  let mut most ← thmMs split
  for l in st.lemmas do most := max most (← thmMs l)
  let verdict := if st.lemmas.size > 0 && most * 5 < was * 4 then "split" else "kept"
  logInfo m!"witness_split {verdict} {name}: {st.lemmas.size} theorems, slowest {most} ms, was {was} ms"

end WitnessSplit
