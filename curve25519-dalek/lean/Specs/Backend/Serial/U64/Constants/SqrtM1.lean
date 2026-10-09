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
open curve25519 (lt_p_iff mod_p_fold mod_p_of_lt)

namespace curve25519_dalek.backend.serial.u64.constants

@[step]
theorem SQRT_M1_spec :
    SQRT_M1 ⦃ (r : FieldElement51) =>
      r.asNat < p ∧ (r.asNat ^ 2 + 1) % p = 0 ∧ ∀ i < 5, r[i]!.val < 2 ^ 51 ⦄ := by
  unfold SQRT_M1
  step*
  subst_vars
  refine ⟨lt_p_iff.mpr (by decide), ?_, by decide⟩
  rw [mod_p_fold, mod_p_fold, mod_p_of_lt] <;> decide

end curve25519_dalek.backend.serial.u64.constants
