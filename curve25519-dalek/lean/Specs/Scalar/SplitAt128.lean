module
public import Curve25519
public import Curve25519Dalek.Funs
public import Specs.Defs
public import Specs.Backend.Serial.U64.Defs
public import Subtle
public import Specs.Lemmas.Bytes
public import Specs.Scalar.HalfWidthFromBytes
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open curve25519_dalek.scalar (Scalar HalfWidthScalar)
open curve25519_dalek.backend.serial.u64.scalar (montgomeryRadix)

namespace curve25519_dalek.scalar.Scalar

@[step]
theorem split_at_128_spec (self : Scalar) :
    split_at_128 self ⦃ (lo hi : HalfWidthScalar) =>
      lo.asNat + 2 ^ 128 * hi.asNat = self.asNat ∧ lo.asNat < 2 ^ 128 ∧ hi.asNat < 2 ^ 128 ⦄ := by
  unfold split_at_128
  step as ⟨s, back, hs, hback⟩
  step as ⟨s1, hs1, hs1len⟩
  step as ⟨s2, hs2⟩
  step as ⟨s3, back1, hs3, hback1⟩
  step as ⟨s4, hs4, hs4len⟩
  step as ⟨s5, hs5⟩
  step as ⟨lo, hlo⟩
  step as ⟨hi, hhi⟩
  have hsplit := Array.asNat_eq_split 8 self.bytes (back s2) (back1 s5) (by simp)
    (fun j hj => ?_) (fun j hj => ?_)
  · rw [hlo, hhi, Scalar.asNat, hsplit]
    have hlt (a : Array U8 16#usize) : a.asNat 8 < 2 ^ 128 :=
      Array.asNat_lt 8 a fun j _ => (a[j]!).hBounds
    exact ⟨rfl, hlt _, hlt _⟩
  · have hj16 : j < 16 := by simpa using hj
    simp [hback, hs2, hs1, Array.from_slice, List.getElem?_take_of_lt hj16]
  · simp [hback1, hs5, hs4, Array.from_slice]

end curve25519_dalek.scalar.Scalar
