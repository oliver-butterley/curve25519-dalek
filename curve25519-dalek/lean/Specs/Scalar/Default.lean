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

namespace curve25519_dalek.scalar.Scalar.Insts.CoreDefaultDefault

@[step]
theorem default_spec :
    default ⦃ (r : Scalar) =>
      r.asNat = 0 ⦄ := by
  unfold default
  simp [ZERO_spec]

end curve25519_dalek.scalar.Scalar.Insts.CoreDefaultDefault
