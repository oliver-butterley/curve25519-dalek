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
open curve25519 (p_add_nineteen)

namespace curve25519_dalek.backend.serial.u64.constants

@[step]
theorem MINUS_ONE_spec :
    MINUS_ONE ⦃ (r : FieldElement51) =>
      r.asNat + 1 = p ∧ ∀ i < 5, r[i]!.val < 2 ^ 51 ⦄ := by
  unfold MINUS_ONE
  step*
  subst_vars
  refine ⟨?_, by decide⟩
  apply Nat.add_right_cancel (m := 19)
  rw [p_add_nineteen]
  decide

end curve25519_dalek.backend.serial.u64.constants
