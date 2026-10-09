module
public import Curve25519
public import Curve25519Dalek.Funs
public import Specs.Backend.Serial.U64.Defs
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open curve25519_dalek.backend.serial.u64.field (FieldElement51)
open curve25519_dalek.backend.serial.u64.scalar (Scalar52)
open curve25519 (p a d A)
open curve25519 (L_eq_limbs)

namespace curve25519_dalek.backend.serial.u64.constants

theorem L_spec :
    Scalar52.asNat L = curve25519.L ∧ ∀ i < 5, L[i]!.val < 2 ^ 52 := by
  unfold L
  refine ⟨?_, by decide⟩
  rw [L_eq_limbs]
  decide

end curve25519_dalek.backend.serial.u64.constants
