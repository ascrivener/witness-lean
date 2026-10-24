import Lean
open Lean

/-
Re-check every Mathlib theorem with Lean's kernel, timing each, and print the slowest.

    cd check/testdata/primes && lake env lean --run ../../../tools/lean/kernel_times.lean [TOP]

A rough guide to where nanoda's heavy declarations are: Lean's kernel and nanoda find different
things expensive (docs/design/heavy-declarations.md), so profile candidates with nanoda
(`lean-host profile`) before acting on this ranking.
-/

/-- Re-check every Mathlib theorem with the kernel, timing each, and print the slowest. -/
def main (args : List String) : IO Unit := do
  let top := (args.head? >>= String.toNat?).getD 40
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `Mathlib }] {} (trustLevel := 1024) (loadExts := false)
  -- The kernel counts heartbeats across the whole process, so without this every check after
  -- the first few thousand times out.
  let opts : Options := maxHeartbeats.set {} 0
  let mut times : Array (Nat × Name) := #[]
  let mut count := 0
  for (name, info) in env.constants.map₁ do
    let .thmInfo t := info | continue
    let some idx := env.getModuleIdxFor? name | continue
    let some mod := env.header.moduleNames[idx.toNat]? | continue
    unless mod.getRoot == `Mathlib do continue
    let t0 ← IO.monoNanosNow
    match env.toKernelEnv.addDecl opts (.thmDecl { t with name := name ++ `witness_timing }) with
    | .ok _ => pure ()
    | .error e => IO.eprintln s!"rejected: {name}: {(← (e.toMessageData {}).toString).take 120}"
    let us := ((← IO.monoNanosNow) - t0) / 1000
    count := count + 1
    if us ≥ 20000 then times := times.push (us, name)
    if count % 20000 == 0 then IO.eprintln s!"{count} theorems checked"
  let sorted := times.qsort (fun a b => a.1 > b.1)
  IO.println s!"{count} theorems checked; {times.size} took 20 ms or more"
  for (us, name) in sorted.toList.take top do
    IO.println s!"{us / 1000} ms  {name}  ({(env.getModuleIdxFor? name).bind (fun i => env.header.moduleNames[i.toNat]?) |>.getD .anonymous})"
