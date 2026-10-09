module
public import Curve25519
public import Curve25519Dalek.Funs
public import Specs.Backend.Serial.U64.Defs
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open curve25519_dalek.backend.serial.u64.field (FieldElement51)
open curve25519_dalek.backend.serial.u64.scalar (Scalar52)
open curve25519 (p a d A)

namespace curve25519_dalek.backend.serial.u64.constants

@[step]
theorem SQRT_AD_MINUS_ONE_spec :
    SQRT_AD_MINUS_ONE ⦃ (r : FieldElement51) =>
      r.asNat < p ∧
      r.asNat ^ 2 % p = (a * d - 1).val ∧ ∀ i < 5, r[i]!.val < 2 ^ 51 ⦄ := by
  sorry

end curve25519_dalek.backend.serial.u64.constants
