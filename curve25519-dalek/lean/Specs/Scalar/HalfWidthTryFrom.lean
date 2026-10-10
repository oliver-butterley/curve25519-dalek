module
public import Curve25519
public import Curve25519Dalek.Funs
public import Specs.Defs
public import Specs.Backend.Serial.U64.Defs
public import Subtle
public import Specs.Lemmas.Bytes
public import Specs.Lemmas.Array
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open curve25519_dalek.scalar (Scalar HalfWidthScalar)
open curve25519_dalek.backend.serial.u64.scalar (montgomeryRadix)

namespace curve25519_dalek.scalar.HalfWidthScalar.Insts.CoreConvertTryFromScalarTuple

/-- The loop of `try_from` checks that the bytes from `i` to `31` are zero. -/
@[local step]
private theorem try_from_loop_spec (value : Scalar) (i : Usize) (hi : 16 ≤ i.val ∧ i.val ≤ 32)
    (hz : ∀ j, 16 ≤ j → j < i.val → value.bytes[j]!.val = 0) :
    try_from_loop value i ⦃ (r : core.result.Result HalfWidthScalar Unit) =>
      ((∀ j, 16 ≤ j → j < 32 → value.bytes[j]!.val = 0) → r = .Ok value) ∧
      (¬ (∀ j, 16 ≤ j → j < 32 → value.bytes[j]!.val = 0) → r = .Err ()) ⦄ := by
  unfold try_from_loop
  apply loop.spec_decr_nat (measure := fun i => 32 - i.val)
    (inv := fun i => (16 ≤ i.val ∧ i.val ≤ 32) ∧
      ∀ j, 16 ≤ j → j < i.val → value.bytes[j]!.val = 0)
  · rintro k ⟨hk, hzk⟩
    unfold try_from_loop.body
    by_cases hlt : k.val < 32
    · simp only [show k < 32#usize by scalar_tac, if_true]
      step with Array.index_usize_getElem!_spec as ⟨x, hx⟩
      by_cases hx0 : x = 0#u8
      · simp only [hx0, bne_self_eq_false, Bool.false_eq_true, if_false]
        step as ⟨k1, hk1⟩
        refine ⟨by scalar_tac, by scalar_tac, fun j hj hjk => ?_, by scalar_tac⟩
        by_cases hjk' : j = k.val
        · rw [hjk', ← hx, hx0]
          rfl
        · exact hzk j hj (by scalar_tac)
      · simp only [bne_iff_ne, ne_eq, hx0, not_false_eq_true, if_true, WP.spec_ok]
        refine ⟨fun hall => absurd ?_ hx0, fun _ => trivial⟩
        rw [hx]
        exact UScalar.eq_of_val_eq (hall k.val hk.1 hlt)
    · simp only [show ¬ k < 32#usize by scalar_tac, if_false, WP.spec_ok]
      exact ⟨fun _ => trivial, fun hn => absurd (fun j hj hj32 => hzk j hj (by scalar_tac)) hn⟩
  · exact ⟨hi, hz⟩

@[step]
theorem try_from_spec (value : Scalar) :
    try_from value ⦃ (r : core.result.Result HalfWidthScalar Unit) =>
      (value.asNat < 2 ^ 128 → r = .Ok value) ∧ (2 ^ 128 ≤ value.asNat → r = .Err ()) ⦄ := by
  unfold try_from
  step with try_from_loop_spec as ⟨r, hok, herr⟩
  have hiff := Array.asNat_lt_pow_iff 8 16 value.bytes (by simp)
    fun j _ => (value.bytes[j]!).hBounds
  refine ⟨fun hlt => hok (hiff.mp hlt), fun hge => herr fun hall => ?_⟩
  exact absurd (hiff.mpr hall) (Nat.not_lt.mpr hge)

end curve25519_dalek.scalar.HalfWidthScalar.Insts.CoreConvertTryFromScalarTuple
