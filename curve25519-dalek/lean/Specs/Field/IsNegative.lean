module
public import Curve25519
public import Curve25519Dalek.Funs
public import Specs.Backend.Serial.U64.Defs
public import Subtle
public import Specs.Backend.Serial.U64.Field.ToBytes
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open curve25519_dalek.backend.serial.u64.field (FieldElement51)

namespace curve25519_dalek.field.FieldElement51

/-- The parity of a little-endian byte string's value is that of its first byte. -/
private theorem ofDigits_mod_two (l : List U8) (h : 0 < l.length) :
    Nat.ofDigits (2 ^ 8) (l.map (·.val)) % 2 = (l[0]'h).val % 2 := by
  cases l with
  | nil => simp at h
  | cons x l =>
    simp only [List.map_cons, Nat.ofDigits_cons, List.getElem_cons_zero]
    omega

@[step]
theorem is_negative_spec (self : FieldElement51) :
    is_negative self ⦃ (c : subtle.Choice) =>
      c.IsValid ∧ c.val = self.asNat % p % 2 ⦄ := by
  unfold is_negative
  step as ⟨bytes, hbytes⟩
  step as ⟨i, hi⟩
  step as ⟨i1, hi1, hi1bv⟩
  step as ⟨c, hcv, hc⟩
  · refine (subtle.Choice.isValid_iff i1).mpr ?_
    rw [hi1, UScalar.val_and]
    exact Nat.and_le_right
  refine ⟨hcv, ?_⟩
  rw [hc, hi1, UScalar.val_and]
  change i.val &&& 1 = _
  rw [Nat.and_one_is_mod, ← hbytes, hi]
  exact (ofDigits_mod_two bytes.val _).symm

end curve25519_dalek.field.FieldElement51
