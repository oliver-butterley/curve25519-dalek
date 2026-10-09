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
theorem APLUS2_OVER_FOUR_spec :
    APLUS2_OVER_FOUR ⦃ (r : FieldElement51) =>
      r.asNat * 4 = A + 2 ∧ ∀ i < 5, r[i]!.val < 2 ^ 51 ⦄ := by
  sorry

end curve25519_dalek.backend.serial.u64.constants
