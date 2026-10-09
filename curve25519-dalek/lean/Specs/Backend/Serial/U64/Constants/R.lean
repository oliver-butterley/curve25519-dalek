module
public import Curve25519
public import Curve25519Dalek.Funs
public import Specs.Backend.Serial.U64.Defs
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open curve25519_dalek.backend.serial.u64.field (FieldElement51)
open curve25519_dalek.backend.serial.u64.scalar (Scalar52)
open curve25519 (p a d A)
open curve25519 (two_pow_260_mod_L)

namespace curve25519_dalek.backend.serial.u64.constants

theorem R_spec :
    Scalar52.asNat R = 2 ^ 260 % curve25519.L ∧ ∀ i < 5, R[i]!.val < 2 ^ 52 := by
  unfold R
  rw [two_pow_260_mod_L]
  decide

end curve25519_dalek.backend.serial.u64.constants
