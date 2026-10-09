module
public import Aeneas
@[expose] public section

/-! # Spec definitions used across the crate (audited) -/

open Aeneas.Std

/-- The natural number encoded little-endian by an array of bytes:
`∑ i, 2^(8 i) · bytes[i]`. -/
def Aeneas.Std.Array.asNat {n : Usize} (bytes : Array U8 n) : ℕ :=
  ∑ i ∈ Finset.range n.val, 2 ^ (8 * i) * bytes[i]!.val
