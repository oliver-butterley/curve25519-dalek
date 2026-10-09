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

theorem LFACTOR_spec :
    LFACTOR.val < 2 ^ 52 ∧ (LFACTOR.val * curve25519.L + 1) % 2 ^ 52 = 0 := by
  sorry

end curve25519_dalek.backend.serial.u64.constants
