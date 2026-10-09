module
public import Aeneas
public import Mathlib.Data.Nat.Digits.Defs
@[expose] public section

/-! # Spec definitions used across the crate (audited) -/

open Aeneas.Std

/-- The natural number with the array's elements as little-endian digits in radix `2^bits`:
`a[0] + 2^bits · a[1] + 2^(2 bits) · a[2] + …`. The digits may exceed `2^bits`.
Bytes use `bits = 8`. -/
def Aeneas.Std.Array.asNat {ty : UScalarTy} {n : Usize} (bits : ℕ) (a : Array (UScalar ty) n) : ℕ :=
  Nat.ofDigits (2 ^ bits) (a.val.map (·.val))
