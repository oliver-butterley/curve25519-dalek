module
public import Specs.Defs
public section

/-! # Injectivity of `Array.asNat` and `Array.to_slice` -/

open Aeneas Aeneas.Std

namespace Aeneas.Std.Array

/-- An array of `n`-bit scalars is determined by its value in radix `2 ^ n`. -/
theorem eq_of_asNat_eq {ty : UScalarTy} {n : Usize} {a b : Array (UScalar ty) n}
    (h : a.asNat ty.numBits = b.asNat ty.numBits) : a = b := by
  have hlt : ∀ (l : List (UScalar ty)), ∀ x ∈ l.map (·.val), x < 2 ^ ty.numBits := by
    intro l x hx
    obtain ⟨y, -, rfl⟩ := List.mem_map.mp hx
    exact y.hBounds
  have hbits : ty.numBits ≠ 0 := by
    rcases System.Platform.numBits_eq with hnb | hnb <;> cases ty <;> simp [hnb]
  have hmap := Nat.ofDigits_inj_of_len_eq (Nat.one_lt_two_pow hbits)
    (by simp) (hlt a.val) (hlt b.val) h
  exact Array.ext a b
    (List.map_injective_iff.mpr (fun x y hxy => UScalar.eq_of_val_eq hxy) hmap)

/-- Arrays are equal when their slices are. -/
theorem eq_of_to_slice_eq {α : Type} {n : Usize} {a b : Array α n}
    (h : a.to_slice = b.to_slice) : a = b := by
  have hval := congrArg Slice.val h
  simp only [Array.val_to_slice] at hval
  exact Array.ext a b hval

end Aeneas.Std.Array
