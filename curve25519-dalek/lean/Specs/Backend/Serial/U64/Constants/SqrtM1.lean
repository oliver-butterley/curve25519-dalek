module
public import Curve25519
public import Curve25519Dalek.Funs
public import Specs.Backend.Serial.U64.Defs
public import Specs.Backend.Serial.U64.Field.FromLimbs
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open curve25519_dalek.backend.serial.u64.field (FieldElement51)
open curve25519_dalek.backend.serial.u64.scalar (Scalar52)
open curve25519 (p a d A)
open curve25519 (sqrtM1 sqrtM1_eq_limbs)

namespace curve25519_dalek.backend.serial.u64.constants

@[step]
theorem SQRT_M1_spec :
    SQRT_M1 ⦃ (r : FieldElement51) =>
      r.asNat = sqrtM1 ∧ ∀ i < 5, r[i]!.val < 2 ^ 51 ⦄ := by
  unfold SQRT_M1
  step*
  subst_vars
  refine ⟨?_, by decide⟩
  rw [sqrtM1_eq_limbs]
  decide

end curve25519_dalek.backend.serial.u64.constants
