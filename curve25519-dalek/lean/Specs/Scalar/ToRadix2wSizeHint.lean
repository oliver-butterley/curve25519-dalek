module
public import Curve25519
public import Curve25519Dalek.Funs
public import Specs.Defs
public import Specs.Backend.Serial.U64.Defs
public import Subtle
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open curve25519_dalek.scalar (Scalar HalfWidthScalar)
open curve25519_dalek.backend.serial.u64.scalar (montgomeryRadix)

namespace curve25519_dalek.scalar.Scalar

@[step]
theorem to_radix_2w_size_hint_spec (w : Usize) (hw : 4 ≤ w.val ∧ w.val ≤ 8) :
    to_radix_2w_size_hint w ⦃ (r : Usize) =>
      (w.val = 4 → r.val = 64) ∧ (w.val = 5 → r.val = 52) ∧ (w.val = 6 → r.val = 43) ∧
      (w.val = 7 → r.val = 37) ∧ (w.val = 8 → r.val = 33) ⦄ := by
  unfold to_radix_2w_size_hint
  step
  step
  simp only [show 4#usize ≤ w by scalar_tac, if_true]
  by_cases h7 : w.val ≤ 7
  · simp only [show w ≤ 7#usize by scalar_tac, if_true]
    step as ⟨d, hd⟩
    have hcases : w.val = 4 ∨ w.val = 5 ∨ w.val = 6 ∨ w.val = 7 := by scalar_tac
    have hd64 : d.val ≤ 64 := by
      rw [hd]
      rcases hcases with h | h | h | h <;> simp [h]
    step
    rcases hcases with h | h | h | h <;> simp [h, hd]
  · have h8 : w.val = 8 := by scalar_tac
    simp only [show ¬ w ≤ 7#usize by scalar_tac, if_false, h8]
    step as ⟨d, hd⟩
    have hd32 : d.val = 32 := by simp [hd, h8]
    step as ⟨c, hc⟩
    step
    simp [hc, hd32]

end curve25519_dalek.scalar.Scalar
