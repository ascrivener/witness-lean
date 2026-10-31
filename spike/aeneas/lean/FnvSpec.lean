import Fnv
open Aeneas Aeneas.Std Result ControlFlow
namespace fnv

/-- FNV-1a over bytes, on naturals: xor in each byte, then multiply by the FNV prime, mod 2⁶⁴. -/
def fnv1a (h : Nat) : List Std.U8 → Nat
  | [] => h
  | b :: bs => fnv1a ((h ^^^ b.val) * 1099511628211 % 2 ^ 64) bs

theorem write_loop_spec (it : core.slice.iter.Iter Std.U8) (hash : Std.U64)
    (hi : it.i ≤ it.slice.val.length) :
    FnvHasher.Insts.CoreHashHasher.write_loop it hash
      ⦃ r => r.val = fnv1a hash.val (it.slice.val.drop it.i) ⦄ := by
  unfold FnvHasher.Insts.CoreHashHasher.write_loop
  apply loop.spec_decr_nat (fun (x : core.slice.iter.Iter Std.U8 × Std.U64) => it.slice.val.length - x.1.i)
    (fun x => x.1.slice = it.slice ∧ x.1.i ≤ it.slice.val.length ∧
      fnv1a x.2.val (it.slice.val.drop x.1.i) = fnv1a hash.val (it.slice.val.drop it.i))
  · rintro ⟨⟨s, idx⟩, h⟩ ⟨hs, hi', hinv⟩
    simp only at hs hi' hinv
    subst hs
    simp only [FnvHasher.Insts.CoreHashHasher.write_loop.body, core.slice.iter.IteratorSliceIter.next]
    split
    · rename_i hlt
      have hl : idx < it.slice.val.length := by simpa using hlt
      step*
      refine ⟨by omega, ?_, by omega⟩
      rw [← hinv]
      conv_rhs => rw [List.drop_eq_getElem_cons hl]
      simp only [fnv1a]
      congr 1
      simp_all [U64.size, U64.numBits]
      rfl
    · rename_i hge
      have : idx = it.slice.val.length := by scalar_tac
      simp_all [fnv1a]
  · simp [hi]

/-- `FnvHasher::write` computes exactly FNV-1a over the bytes, starting from the hasher's state,
and never panics. -/
theorem write_spec (self : FnvHasher) (bytes : Slice Std.U8) :
    FnvHasher.Insts.CoreHashHasher.write self bytes ⦃ r => r.val = fnv1a self.val bytes.val ⦄ := by
  unfold FnvHasher.Insts.CoreHashHasher.write core.slice.Slice.iter
  step with write_loop_spec
  simp_all

end fnv
