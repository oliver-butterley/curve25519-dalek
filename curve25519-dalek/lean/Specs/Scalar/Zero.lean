module
public import Curve25519
public import Curve25519Dalek.Funs
public import Specs.Defs
public import Specs.Backend.Serial.U64.Defs
public import Subtle
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open curve25519_dalek.scalar (Scalar HalfWidthScalar)
open curve25519_dalek.backend.serial.u64.scalar (montgomeryRadix)

namespace curve25519_dalek.scalar.Scalar

theorem ZERO_spec :
    Scalar.asNat ZERO = 0 := by
  simp [Scalar.asNat, Array.asNat, ZERO, Nat.ofDigits]

end curve25519_dalek.scalar.Scalar
