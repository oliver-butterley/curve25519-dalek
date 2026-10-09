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
theorem INVSQRT_A_MINUS_D_spec :
    INVSQRT_A_MINUS_D ⦃ (r : FieldElement51) =>
      r.asNat < p ∧
      r.asNat ^ 2 * (a - d).val % p = 1 ∧ ∀ i < 5, r[i]!.val < 2 ^ 51 ⦄ := by
  sorry

end curve25519_dalek.backend.serial.u64.constants
