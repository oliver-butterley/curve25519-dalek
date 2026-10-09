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
theorem from_bytes_spec (bytes : Array U8 32#usize) :
    from_bytes bytes ⦃ (r : FieldElement51) =>
      r.asNat = bytes.asNat % 2 ^ 255 ∧ ∀ i < 5, r[i]!.val < 2 ^ 51 ⦄ := by
  sorry
end curve25519_dalek.backend.serial.u64.field.FieldElement51

namespace curve25519_dalek.backend.serial.u64.field.FieldElement51.from_bytes
@[step]
theorem load8_at_spec (input : Slice U8) (i : Usize) (hi : i.val + 8 ≤ input.length) :
    load8_at input i ⦃ (r : U64) =>
      r.val = ∑ j ∈ Finset.range 8, 2 ^ (8 * j) * input[i.val + j]!.val ⦄ := by
  sorry
end curve25519_dalek.backend.serial.u64.field.FieldElement51.from_bytes
