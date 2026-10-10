module
public import Curve25519
public import Curve25519Dalek.Funs
public import Specs.Backend.Serial.U64.Defs
public import Specs.Lemmas.ArrayGetElem
public import Subtle
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open curve25519_dalek.backend.serial.u64.field (FieldElement51)

namespace curve25519_dalek.backend.serial.u64.field.FieldElement51.Insts
namespace SubtleConditionallySelectable
@[step]
theorem conditional_swap_spec (a b : FieldElement51) (choice : subtle.Choice)
    (hchoice : choice.IsValid) :
    conditional_swap a b choice ⦃ (a' : FieldElement51) (b' : FieldElement51) =>
      (choice = 0#u8 → a' = a ∧ b' = b) ∧ (choice = 1#u8 → a' = b ∧ b' = a) ⦄ := by
  unfold conditional_swap
  step*
  constructor
  · intro hc
    simp [*, Array.set_getElem_five]
  · intro hc
    simp [*, Array.set_getElem_five]
end curve25519_dalek.backend.serial.u64.field.FieldElement51.Insts.SubtleConditionallySelectable
