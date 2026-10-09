module
public import Curve25519Dalek.Types
public import Specs.Defs
@[expose] public section

/-! # Spec definitions for the u64 backend (audited) -/

open Aeneas.Std


namespace curve25519_dalek.backend.serial.u64

/-- The natural number represented by the five radix-2^51 limbs:
`∑ i, 2^(51 i) · self[i]`. The limbs may exceed 51 bits. -/
@[nolint defsWithUnderscore]
def field.FieldElement51.asNat (self : field.FieldElement51) : ℕ :=
  ∑ i ∈ Finset.range 5, 2 ^ (51 * i) * self[i]!.val

/-- The natural number represented by the five radix-2^52 limbs:
`∑ i, 2^(52 i) · self[i]`. -/
@[nolint defsWithUnderscore]
def scalar.Scalar52.asNat (self : scalar.Scalar52) : ℕ :=
  ∑ i ∈ Finset.range 5, 2 ^ (52 * i) * self[i]!.val

end curve25519_dalek.backend.serial.u64
