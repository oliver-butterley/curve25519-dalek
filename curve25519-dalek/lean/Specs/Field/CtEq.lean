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

namespace curve25519_dalek.backend.serial.u64.field.FieldElement51.Insts.SubtleConstantTimeEq

@[step]
theorem ct_eq_spec (self other : FieldElement51) :
    ct_eq self other ⦃ (c : subtle.Choice) =>
      c.IsValid ∧ (self.asNat % p = other.asNat % p → c = 1#u8) ∧
      (self.asNat % p ≠ other.asNat % p → c = 0#u8) ⦄ := by
  unfold ct_eq
  step as ⟨a, ha⟩
  step as ⟨s, hs⟩
  step as ⟨a1, ha1⟩
  step as ⟨s1, hs1⟩
  step as ⟨c, hcv, hc1, hc0⟩
  subst hs hs1
  refine ⟨hcv, fun h => hc1 ?_, fun h => hc0 fun hss => h ?_⟩
  · exact congrArg Array.to_slice (Array.eq_of_asNat_eq (ha.trans (h.trans ha1.symm)))
  · rw [← ha, ← ha1, Array.eq_of_to_slice_eq hss]

end curve25519_dalek.backend.serial.u64.field.FieldElement51.Insts.SubtleConstantTimeEq
