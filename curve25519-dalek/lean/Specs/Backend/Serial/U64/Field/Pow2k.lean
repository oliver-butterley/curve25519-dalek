module
public import Curve25519
public import Curve25519Dalek.Funs
public import Specs.Backend.Serial.U64.Defs
public import Subtle
public section
set_option linter.style.longLine false

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open curve25519_dalek.backend.serial.u64.field (FieldElement51)

namespace curve25519_dalek.backend.serial.u64.field.FieldElement51
@[step]
theorem pow2k_spec (self : FieldElement51) (k : U32) (hk : 0 < k.val)
    (hself : ∀ i < 5, self[i]!.val < 2 ^ 54) :
    pow2k self k ⦃ (r : FieldElement51) =>
      r.asNat % p = self.asNat ^ 2 ^ k.val % p ∧ ∀ i < 5, r[i]!.val < 2 ^ 52 ⦄ := by
  sorry
end curve25519_dalek.backend.serial.u64.field.FieldElement51
