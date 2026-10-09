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
theorem to_bytes_spec (self : FieldElement51) :
    to_bytes self ⦃ (r : Array U8 32#usize) =>
      r.asNat = self.asNat % p ⦄ := by
  sorry
end curve25519_dalek.backend.serial.u64.field.FieldElement51
