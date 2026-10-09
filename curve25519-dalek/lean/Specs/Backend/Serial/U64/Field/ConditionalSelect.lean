module
public import Curve25519
public import Curve25519Dalek.Funs
public import Specs.Backend.Serial.U64.Defs
public import Subtle
public section
set_option linter.style.longLine false

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open curve25519_dalek.backend.serial.u64.field (FieldElement51)

namespace curve25519_dalek.backend.serial.u64.field.FieldElement51.Insts.SubtleConditionallySelectable
@[step]
theorem conditional_select_spec (a b : FieldElement51) (choice : subtle.Choice) :
    conditional_select a b choice ⦃ (r : FieldElement51) =>
      (choice = 0#u8 → r = a) ∧ (choice = 1#u8 → r = b) ⦄ := by
  sorry
end curve25519_dalek.backend.serial.u64.field.FieldElement51.Insts.SubtleConditionallySelectable
