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
@[step]
theorem square_limbs_spec (a : Array U64 5#usize) (ha : ∀ i < 5, a[i]!.val < 2 ^ 54) :
    square_limbs a ⦃ (r : Array U64 5#usize) =>
      FieldElement51.asNat r % p = FieldElement51.asNat a ^ 2 % p ∧
      ∀ i < 5, r[i]!.val < 2 ^ 52 ⦄ := by
  sorry
end curve25519_dalek.backend.serial.u64.field

namespace curve25519_dalek.backend.serial.u64.field.square_limbs
@[step]
theorem m_spec (x y : U64) :
    m x y ⦃ (r : U128) =>
      r.val = x.val * y.val ⦄ := by
  sorry
end curve25519_dalek.backend.serial.u64.field.square_limbs
