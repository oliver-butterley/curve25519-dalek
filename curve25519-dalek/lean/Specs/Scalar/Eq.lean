module
public import Curve25519
public import Curve25519Dalek.Funs
public import Specs.Defs
public import Specs.Backend.Serial.U64.Defs
public import Subtle
public import Specs.Scalar.CtEq
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open curve25519_dalek.scalar (Scalar HalfWidthScalar)
open curve25519_dalek.backend.serial.u64.scalar (montgomeryRadix)

namespace curve25519_dalek.scalar.Scalar.Insts.CoreCmpPartialEqScalar

@[step]
theorem eq_spec (self other : Scalar) :
    eq self other ⦃ (b : Bool) =>
      (b = true ↔ self = other) ⦄ := by
  unfold eq
  step as ⟨c, _, hc1, hc0⟩
  step as ⟨b, hb⟩
  subst hb
  by_cases h : self = other
  · simp [h, hc1 h]
  · simp [h, hc0 h]

end curve25519_dalek.scalar.Scalar.Insts.CoreCmpPartialEqScalar
