module
public import Curve25519
public import Curve25519Dalek.Funs
public import Specs.Backend.Serial.U64.Defs
public import Subtle
public section
set_option linter.style.longLine false

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open curve25519_dalek.backend.serial.u64.field (FieldElement51)

namespace curve25519_dalek.backend.serial.u64.field
theorem SIXTEEN_P_spec :
    FieldElement51.asNat SIXTEEN_P = 16 * p ∧
      (∀ i < 5, 2 ^ 55 ≤ SIXTEEN_P[i]!.val + 304) ∧ ∀ i < 5, SIXTEEN_P[i]!.val < 2 ^ 55 := by
  sorry
end curve25519_dalek.backend.serial.u64.field
