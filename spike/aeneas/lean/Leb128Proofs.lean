import Leb128
open Aeneas Aeneas.Std Result ControlFlow
namespace leb128

/-- `decode_u32` never panics or overflows on any input, and when it decodes a value it took
between 1 and 5 bytes, all within `buf`. -/
theorem decode_u32_spec (buf : Slice Std.U8) :
    decode_u32 buf ⦃ r => ∀ v n, r = some (v, n) → 1 ≤ n.val ∧ n.val ≤ 5 ∧ n.val ≤ buf.length ⦄ := by
  unfold decode_u32 decode_u32_loop
  apply loop.spec_decr_nat (fun (x : Std.U32 × Std.U32 × Std.Usize) => 5 - x.2.2.val)
    (fun x => x.2.1.val = 7 * x.2.2.val ∧ x.2.2.val ≤ 5)
  · rintro ⟨value, shift, i⟩ ⟨h1, h2⟩
    unfold decode_u32_loop.body
    step* <;> simp_all <;> scalar_tac
  · simp

