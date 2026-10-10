module
public import Curve25519
public import Curve25519Dalek.Funs
public import Specs.Defs
public import Specs.Backend.Serial.U64.Defs
public import Subtle
public import Zeroize.Instances
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open curve25519_dalek.scalar (Scalar HalfWidthScalar)
open curve25519_dalek.backend.serial.u64.scalar (montgomeryRadix)

namespace curve25519_dalek.scalar.HalfWidthScalar.Insts.ZeroizeZeroize

@[step]
theorem zeroize_spec (self : HalfWidthScalar) :
    zeroize self ⦃ (r : HalfWidthScalar) =>
      r.asNat = 0 ⦄ := by
  unfold zeroize
  step*
  simp [HalfWidthScalar.asNat, Scalar.asNat, Array.asNat, Nat.ofDigits, *]

end curve25519_dalek.scalar.HalfWidthScalar.Insts.ZeroizeZeroize
