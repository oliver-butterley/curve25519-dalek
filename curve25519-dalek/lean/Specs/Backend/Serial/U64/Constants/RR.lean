module
public import Curve25519
public import Curve25519Dalek.Funs
public import Specs.Backend.Serial.U64.Defs
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open curve25519_dalek.backend.serial.u64.field (FieldElement51)
open curve25519_dalek.backend.serial.u64.scalar (Scalar52)
open curve25519 (p a d A)
open curve25519 (two_pow_520_mod_L)

namespace curve25519_dalek.backend.serial.u64.constants

theorem RR_spec :
    Scalar52.asNat RR = 2 ^ 520 % curve25519.L ∧ ∀ i < 5, RR[i]!.val < 2 ^ 52 := by
  unfold RR
  rw [two_pow_520_mod_L]
  decide

end curve25519_dalek.backend.serial.u64.constants
