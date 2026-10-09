module
public import Curve25519
public import Curve25519Dalek.Funs
public import Specs.Backend.Serial.U64.Defs
public import Subtle
public import Specs.Backend.Serial.U64.Field.FromLimbs
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open curve25519_dalek.backend.serial.u64.field (FieldElement51)

namespace curve25519_dalek.backend.serial.u64.field.FieldElement51
@[step]
theorem ZERO_spec :
    ZERO ⦃ (r : FieldElement51) =>
      r.asNat = 0 ∧ ∀ i < 5, r[i]!.val < 2 ^ 51 ⦄ := by
  unfold ZERO
  step*
  subst_vars
  decide
end curve25519_dalek.backend.serial.u64.field.FieldElement51
