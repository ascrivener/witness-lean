import Leb128
open Aeneas Aeneas.Std Result ControlFlow
namespace leb128

/-- The value of the first `n` bytes of `bs` read as LEB128 digits: 7 bits each, low first. -/
def digits (bs : List Std.U8) : Nat → Nat
  | 0 => 0
  | n + 1 => digits bs n + (bs.getD n 0#u8).val % 128 * 2 ^ (7 * n)

theorem digits_lt (bs : List Std.U8) (n : Nat) : digits bs n < 2 ^ (7 * n) := by
  induction n with
  | zero => simp [digits]
  | succ n ih =>
    simp only [digits]
    have : (bs.getD n 0#u8).val % 128 < 128 := Nat.mod_lt _ (by decide)
    calc digits bs n + (bs.getD n 0#u8).val % 128 * 2 ^ (7 * n)
        < 2 ^ (7 * n) + 127 * 2 ^ (7 * n) := by nlinarith [Nat.pow_pos (n := 7 * n) (by decide : 0 < 2)]
      _ = 2 ^ (7 * (n + 1)) := by ring_nf

theorem digits_succ (bs : List Std.U8) (i : Nat) (h : i < bs.length) :
    digits bs (i + 1) = digits bs i + (bs[i]'h).val % 128 * 2 ^ (7 * i) := by
  simp [digits, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

/-- One step of the loop: OR-ing in the next digit, shifted into place, adds it. -/
theorem step_eq (bs : List Std.U8) (i : Nat) (h : i < bs.length)
    (hlt : (bs[i]'h).val % 128 * 2 ^ (7 * i) < 2 ^ 32) :
    digits bs i ||| ((bs[i]'h).val &&& 127) <<< (7 * i) % U32.size = digits bs (i + 1) := by
  have hand : (bs[i]'h).val &&& 127 = (bs[i]'h).val % 128 :=
    Nat.and_two_pow_sub_one_eq_mod _ 7
  rw [hand, Nat.shiftLeft_eq, U32.size, Nat.mod_eq_of_lt (by simpa [U32.numBits] using hlt), Nat.or_comm,
    Nat.mul_comm, ← Nat.two_pow_add_eq_or_of_lt (digits_lt bs i), digits_succ bs i h]
  ring

theorem lt_128 : ∀ n < 256, n &&& 128 = 0 → n < 128 := by decide +kernel
theorem ge_128 : ∀ n < 256, ¬n &&& 128 = 0 → 128 ≤ n := by decide +kernel

/-- When `decode_u32` decodes a value, it's exactly the LEB128 value of the bytes it took: every
byte but the last has its continuation bit set, the last doesn't, and the digits add up. -/
theorem decode_u32_correct (buf : Slice Std.U8) :
    decode_u32 buf ⦃ r => ∀ v n, r = some (v, n) →
      v.val = digits buf.val n ∧ (buf.val.getD (n.val - 1) 0#u8).val < 128 ∧
      ∀ k < n.val - 1, 128 ≤ (buf.val.getD k 0#u8).val ⦄ := by
  unfold decode_u32 decode_u32_loop
  apply loop.spec_decr_nat (fun (x : Std.U32 × Std.U32 × Std.Usize) => 5 - x.2.2.val)
    (fun x => x.2.1.val = 7 * x.2.2.val ∧ x.2.2.val ≤ 5 ∧ x.1.val = digits buf.val x.2.2.val ∧
      ∀ k < x.2.2.val, 128 ≤ (buf.val.getD k 0#u8).val)
  · rintro ⟨value, shift, i⟩ ⟨h1, h2, h3, h4⟩
    unfold decode_u32_loop.body
    step*
    all_goals simp_all
    all_goals
      have hi : (i : Nat) < buf.val.length := by scalar_tac
      have hb : ((buf.val)[(i : Nat)]'hi).val < 256 := by scalar_tac
      have hm : ((buf.val)[(i : Nat)]'hi).val % 128 < 128 := Nat.mod_lt _ (by decide)
      have hg : (buf.val[(i : Nat)]?.getD 0#u8) = buf.val[(i : Nat)]'hi := by
        simp [List.getElem?_eq_getElem hi]
      have hand : ((buf.val)[(i : Nat)]'hi).val &&& 127 = ((buf.val)[(i : Nat)]'hi).val % 128 :=
        Nat.and_two_pow_sub_one_eq_mod _ 7
      have key := step_eq buf.val i hi
      rw [hand] at key ⊢
      try rw [show (28 : Nat) = 7 * (i : Nat) by omega]
      have hlt : ((buf.val)[(i : Nat)]'hi).val % 128 * 2 ^ (7 * (i : Nat)) < 2 ^ 32 := by
        simp only [hand] at *
        rcases (show (i : Nat) = 4 ∨ (i : Nat) ≤ 3 by omega) with h | h
        · have hp : 2 ^ (7 * (i : Nat)) = 2 ^ 28 := by rw [h]
          rw [hp]; omega
        · have hp : 2 ^ (7 * (i : Nat)) ≤ 2 ^ 21 := Nat.pow_le_pow_right (by decide) (by omega)
          nlinarith
      rw [key hlt]
      have l128 := lt_128 _ hb
      have g128 := ge_128 _ hb
      simp only [hg]
      and_intros
      all_goals first
        | trivial
        | omega
        | exact l128 (by simp_all)
        | (intro k hk
           rcases Nat.lt_or_eq_of_le hk with hk | rfl
           · exact h4 k hk
           · simpa [hg] using g128 (by simp_all))

  · simp [digits]
