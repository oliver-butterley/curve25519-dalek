module
public import Curve25519
public import Curve25519Dalek.Funs
public import Specs.Defs
public import Specs.Backend.Serial.U64.Defs
public import Subtle
public import Specs.Scalar.Zero
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open curve25519_dalek.scalar (Scalar HalfWidthScalar)
open curve25519_dalek.backend.serial.u64.scalar (montgomeryRadix)

namespace curve25519_dalek.scalar.HalfWidthScalar

theorem ZERO_spec :
    HalfWidthScalar.asNat ZERO = 0 := by
  simp [HalfWidthScalar.asNat, ZERO, Scalar.ZERO_spec]

end curve25519_dalek.scalar.HalfWidthScalar
