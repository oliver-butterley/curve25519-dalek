module
public import Specs.Backend.Serial.U64.Defs
public section

/-! # Lemmas about `Array.asNat` -/

open Aeneas Aeneas.Std

namespace Aeneas.Std.Array

theorem asNat_eq_sum {ty : UScalarTy} {n : Usize} (bits : ℕ) (a : Array (UScalar ty) n) :
    a.asNat bits = ∑ i ∈ Finset.range n.val, 2 ^ (bits * i) * a[i]!.val := by
  have h : a.val.length = n.val := by simp
  simp only [Array.asNat, Array.getElem!_Nat_eq]
  rw [← h]
  generalize a.val = l
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.length_cons, Finset.sum_range_succ']
    simp [Nat.ofDigits, ih, pow_succ, pow_mul, Finset.mul_sum]
    ring_nf

/-- `asNat` is additive limb by limb. -/
theorem asNat_add_eq {ty : UScalarTy} {n : Usize} (bits : ℕ) (a b c : Array (UScalar ty) n)
    (h : ∀ i < n.val, a[i]!.val + b[i]!.val = c[i]!.val) :
    a.asNat bits + b.asNat bits = c.asNat bits := by
  simp only [asNat_eq_sum, ← Finset.sum_add_distrib, ← mul_add]
  exact Finset.sum_congr rfl fun i hi => by rw [h i (Finset.mem_range.mp hi)]

/-- `asNat` is additive limb by limb, with a sum on both sides. -/
theorem asNat_add_eq_add {ty : UScalarTy} {n : Usize} (bits : ℕ) (a b c d : Array (UScalar ty) n)
    (h : ∀ i < n.val, a[i]!.val + b[i]!.val = c[i]!.val + d[i]!.val) :
    a.asNat bits + b.asNat bits = c.asNat bits + d.asNat bits := by
  simp only [asNat_eq_sum, ← Finset.sum_add_distrib, ← mul_add]
  exact Finset.sum_congr rfl fun i hi => by rw [h i (Finset.mem_range.mp hi)]

theorem asNat_five {ty : UScalarTy} (bits : ℕ) (a : Array (UScalar ty) 5#usize) :
    a.asNat bits = a[0]!.val + 2 ^ bits * a[1]!.val + 2 ^ (2 * bits) * a[2]!.val
      + 2 ^ (3 * bits) * a[3]!.val + 2 ^ (4 * bits) * a[4]!.val := by
  have h : a.val.length = 5 := by simp
  simp only [Array.asNat, Array.getElem!_Nat_eq]
  generalize a.val = l at h ⊢
  match l, h with
  | [x0, x1, x2, x3, x4], _ =>
    simp only [Nat.ofDigits, List.map_cons, List.map_nil, Nat.cast_id, List.getElem!_cons_zero,
      List.getElem!_cons_succ]
    ring

end Aeneas.Std.Array

namespace curve25519_dalek.backend.serial.u64

theorem field.FieldElement51.asNat_eq (a : field.FieldElement51) :
    a.asNat = a[0]!.val + 2 ^ 51 * a[1]!.val + 2 ^ 102 * a[2]!.val + 2 ^ 153 * a[3]!.val
      + 2 ^ 204 * a[4]!.val := by
  simp only [field.FieldElement51.asNat, Array.asNat_five]

theorem scalar.Scalar52.asNat_eq (a : scalar.Scalar52) :
    a.asNat = a[0]!.val + 2 ^ 52 * a[1]!.val + 2 ^ 104 * a[2]!.val + 2 ^ 156 * a[3]!.val
      + 2 ^ 208 * a[4]!.val := by
  simp only [scalar.Scalar52.asNat, Array.asNat_five]

end curve25519_dalek.backend.serial.u64
