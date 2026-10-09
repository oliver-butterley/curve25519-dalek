module
public import Curve25519Dalek.Types
public import Specs.Defs
@[expose] public section

/-! # Spec definitions for the u64 backend (audited) -/

open Aeneas.Std

namespace curve25519_dalek.backend.serial.u64

/-- The natural number represented by the five radix-2^51 limbs. The limbs may exceed 51 bits. -/
@[nolint defsWithUnderscore]
def field.FieldElement51.asNat (self : field.FieldElement51) : ℕ :=
  Array.asNat 51 self

/-- The natural number represented by the five radix-2^52 limbs. -/
@[nolint defsWithUnderscore]
def scalar.Scalar52.asNat (self : scalar.Scalar52) : ℕ :=
  Array.asNat 52 self

end curve25519_dalek.backend.serial.u64
