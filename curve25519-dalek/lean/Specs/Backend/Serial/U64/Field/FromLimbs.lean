module
public import Curve25519
public import Curve25519Dalek.Funs
public import Specs.Backend.Serial.U64.Defs
public import Subtle
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open curve25519_dalek.backend.serial.u64.field (FieldElement51)

namespace curve25519_dalek.backend.serial.u64.field.FieldElement51
@[step]
theorem from_limbs_spec (limbs : Array U64 5#usize) :
    from_limbs limbs ⦃ (r : FieldElement51) =>
      r = limbs ⦄ := by
  unfold from_limbs
  step*
end curve25519_dalek.backend.serial.u64.field.FieldElement51
