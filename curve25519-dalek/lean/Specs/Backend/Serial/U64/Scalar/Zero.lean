module
public import Curve25519
public import Curve25519Dalek.Funs
public import Specs.Backend.Serial.U64.Defs
public import Subtle
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open curve25519_dalek.backend.serial.u64.scalar (Scalar52)

namespace curve25519_dalek.backend.serial.u64.scalar.Scalar52

theorem ZERO_spec :
    Scalar52.asNat ZERO = 0 ∧ ∀ i < 5, ZERO[i]!.val < 2 ^ 52 := by
  unfold ZERO
  decide

end curve25519_dalek.backend.serial.u64.scalar.Scalar52
