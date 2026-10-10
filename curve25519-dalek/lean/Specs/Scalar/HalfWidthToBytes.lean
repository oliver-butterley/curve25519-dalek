module
public import Curve25519
public import Curve25519Dalek.Funs
public import Specs.Defs
public import Specs.Backend.Serial.U64.Defs
public import Subtle
public import Specs.Lemmas.Bytes
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.scalar (Scalar HalfWidthScalar)
open Curve25519Dalek.backend.serial.u64.scalar (montgomeryRadix)

namespace Curve25519Dalek.scalar.HalfWidthScalar

@[step]
theorem to_bytes_spec (self : HalfWidthScalar) :
    to_bytes self ⦃ (r : Array U8 16#usize) =>
      r.asNat 8 = self.asNat % 2 ^ 128 ⦄ := by
  unfold to_bytes
  step as ⟨s, back, hs, hback⟩
  step as ⟨s1, hs1, hs1len⟩
  step as ⟨s2, hs2⟩
  rw [HalfWidthScalar.asNat, Scalar.asNat]
  refine (Array.asNat_mod_of_prefix 8 self.bytes _ (by simp) (fun j hj => ?_)
    (fun j _ => (self.bytes[j]!).hBounds)).symm
  have hj16 : j < 16 := by simpa using hj
  simp [hback, hs2, hs1, Array.from_slice, List.getElem?_take_of_lt hj16]

end Curve25519Dalek.scalar.HalfWidthScalar
