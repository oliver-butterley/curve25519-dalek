module
public import Curve25519
public import Curve25519Dalek.Funs
public import Specs.Backend.Serial.U64.Defs
public import Subtle
public import Specs.Backend.Serial.U64.Field.ToBytes
public import Specs.Lemmas.AsNatInj
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open curve25519_dalek.backend.serial.u64.field (FieldElement51)

namespace curve25519_dalek.field.FieldElement51

@[step]
theorem is_zero_spec (self : FieldElement51) :
    is_zero self ⦃ (c : subtle.Choice) =>
      c.IsValid ∧ (self.asNat % p = 0 → c = 1#u8) ∧ (self.asNat % p ≠ 0 → c = 0#u8) ⦄ := by
  unfold is_zero
  step as ⟨bytes, hbytes⟩
  step as ⟨s, hs⟩
  step as ⟨s1, hs1⟩
  step as ⟨c, hcv, hc1, hc0⟩
  subst hs hs1
  have hzero : (Array.repeat 32#usize 0#u8).asNat 8 = 0 := by decide
  refine ⟨hcv, fun h => hc1 ?_, fun h => hc0 fun hss => h ?_⟩
  · exact congrArg Array.to_slice (Array.eq_of_asNat_eq (hbytes.trans (h.trans hzero.symm)))
  · rw [← hbytes, Array.eq_of_to_slice_eq hss, hzero]

end curve25519_dalek.field.FieldElement51
