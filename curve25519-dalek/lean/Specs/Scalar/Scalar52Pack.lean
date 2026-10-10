module
public import Curve25519
public import Curve25519Dalek.Funs
public import Specs.Defs
public import Specs.Backend.Serial.U64.Defs
public import Subtle
public import Specs.Backend.Serial.U64.Scalar.ToBytes
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open curve25519_dalek.scalar (Scalar HalfWidthScalar)
open curve25519_dalek.backend.serial.u64.scalar (montgomeryRadix)

namespace curve25519_dalek.scalar.Scalar52

@[step]
theorem pack_spec (self : backend.serial.u64.scalar.Scalar52)
    (hself : ∀ i < 5, self[i]!.val < 2 ^ 52) (hself' : self.asNat < 2 ^ 256) :
    pack self ⦃ (r : Scalar) =>
      r.asNat = self.asNat ⦄ := by
  unfold pack
  step as ⟨r, hr⟩
  exact hr

end curve25519_dalek.scalar.Scalar52
