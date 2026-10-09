module
public import Curve25519
public import Curve25519Dalek.Funs
public import Specs.Backend.Serial.U64.Defs
public import Subtle
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open curve25519_dalek.backend.serial.u64.field (FieldElement51)

namespace curve25519_dalek.backend.serial.u64.field
theorem SIXTEEN_P_spec :
    FieldElement51.asNat SIXTEEN_P = 16 * p ∧
      (∀ i < 5, 2 ^ 55 ≤ SIXTEEN_P[i]!.val + 304) ∧ ∀ i < 5, SIXTEEN_P[i]!.val < 2 ^ 55 := by
  unfold SIXTEEN_P
  refine ⟨?_, by decide⟩
  apply Nat.add_right_cancel (m := 16 * 19)
  rw [← Nat.mul_add, p_add_nineteen]
  decide
end curve25519_dalek.backend.serial.u64.field
