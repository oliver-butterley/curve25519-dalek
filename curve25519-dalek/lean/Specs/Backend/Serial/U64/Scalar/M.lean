module
public import Curve25519
public import Curve25519Dalek.Funs
public import Specs.Backend.Serial.U64.Defs
public import Subtle
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open curve25519_dalek.backend.serial.u64.scalar (Scalar52)

namespace curve25519_dalek.backend.serial.u64.scalar

@[step]
theorem m_spec (x y : U64) :
    m x y ⦃ (r : U128) =>
      r.val = x.val * y.val ⦄ := by
  unfold m
  step*

/-- `m` on a 53-bit and a 52-bit factor, with the bound on the product (for `local step` in the
limb products). -/
theorem m_lt_spec (x y : U64) (hx : x.val < 2 ^ 53) (hy : y.val < 2 ^ 52) :
    m x y ⦃ (r : U128) => r.val = x.val * y.val ∧ r.val < 2 ^ 105 ⦄ := by
  step*

end curve25519_dalek.backend.serial.u64.scalar
