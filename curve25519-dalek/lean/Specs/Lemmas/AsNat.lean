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

/-- Modulo any `m` dividing the radix `2^bits`, the value of a nonempty array is that of its first
digit (e.g. the parity of a byte string is the parity of its first byte). -/
theorem asNat_mod_of_dvd {ty : UScalarTy} {n : Usize} (bits : ℕ) {m : ℕ} (hm : m ∣ 2 ^ bits)
    (a : Array (UScalar ty) n) (hn : 0 < n.val) : a.asNat bits % m = a[0]!.val % m := by
  have h : a.val.length = n.val := by simp
  simp only [Array.asNat, Array.getElem!_Nat_eq]
  generalize a.val = l at h ⊢
  match l, h with
  | [], h => simp at h; omega
  | x :: l, _ =>
    obtain ⟨k, hk⟩ := hm
    simp only [List.map_cons, Nat.ofDigits_cons, List.getElem!_cons_zero]
    rw [hk, Nat.mul_assoc, Nat.add_mul_mod_self_left]

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

theorem asNat_nine {ty : UScalarTy} (bits : ℕ) (a : Array (UScalar ty) 9#usize) :
    a.asNat bits = a[0]!.val + 2 ^ bits * a[1]!.val + 2 ^ (2 * bits) * a[2]!.val
      + 2 ^ (3 * bits) * a[3]!.val + 2 ^ (4 * bits) * a[4]!.val + 2 ^ (5 * bits) * a[5]!.val
      + 2 ^ (6 * bits) * a[6]!.val + 2 ^ (7 * bits) * a[7]!.val
      + 2 ^ (8 * bits) * a[8]!.val := by
  have h : a.val.length = 9 := by simp
  simp only [Array.asNat, Array.getElem!_Nat_eq]
  generalize a.val = l at h ⊢
  match l, h with
  | [x0, x1, x2, x3, x4, x5, x6, x7, x8], _ =>
    simp only [Nat.ofDigits, List.map_cons, List.map_nil, Nat.cast_id, List.getElem!_cons_zero,
      List.getElem!_cons_succ]
    ring

end Aeneas.Std.Array

namespace Curve25519Dalek.backend.serial.u64

theorem field.FieldElement51.asNat_eq (a : field.FieldElement51) :
    a.asNat = a[0]!.val + 2 ^ 51 * a[1]!.val + 2 ^ 102 * a[2]!.val + 2 ^ 153 * a[3]!.val
      + 2 ^ 204 * a[4]!.val := by
  simp only [field.FieldElement51.asNat, Array.asNat_five]

theorem scalar.Scalar52.asNat_eq (a : scalar.Scalar52) :
    a.asNat = a[0]!.val + 2 ^ 52 * a[1]!.val + 2 ^ 104 * a[2]!.val + 2 ^ 156 * a[3]!.val
      + 2 ^ 208 * a[4]!.val := by
  simp only [scalar.Scalar52.asNat, Array.asNat_five]

end Curve25519Dalek.backend.serial.u64

namespace Aeneas.Std.Array

/-- A little-endian number with `k` digits below `2 ^ bits` is below `2 ^ (bits * k)`. -/
theorem sum_pow_mul_lt (bits k : ℕ) (x : ℕ → ℕ) (hx : ∀ j < k, x j < 2 ^ bits) :
    ∑ j ∈ Finset.range k, 2 ^ (bits * j) * x j < 2 ^ (bits * k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, Nat.mul_succ, Nat.pow_add]
    calc ∑ j ∈ Finset.range k, 2 ^ (bits * j) * x j + 2 ^ (bits * k) * x k
        < 2 ^ (bits * k) + 2 ^ (bits * k) * x k :=
          Nat.add_lt_add_right (ih fun j hj => hx j (by omega)) _
      _ = 2 ^ (bits * k) * (x k + 1) := by ring
      _ ≤ 2 ^ (bits * k) * 2 ^ bits := Nat.mul_le_mul_left _ (hx k (by omega))

/-- An array with digits below `2 ^ bits` represents a number below `2 ^ (bits * n)`. -/
theorem asNat_lt {ty : UScalarTy} {n : Usize} (bits : ℕ) (a : Array (UScalar ty) n)
    (h : ∀ i < n.val, a[i]!.val < 2 ^ bits) :
    a.asNat bits < 2 ^ (bits * n.val) := by
  rw [asNat_eq_sum]
  exact sum_pow_mul_lt bits n.val (fun j => a[j]!.val) h

/-- The digit sum of the first `k + 1` digits after setting digit `k` to `x`. -/
theorem sum_range_succ_set {ty : UScalarTy} {n : Usize} (bits : ℕ) (a : Array (UScalar ty) n)
    (k : Usize) (x : UScalar ty) (hk : k.val < n.val) :
    ∑ j ∈ Finset.range (k.val + 1), 2 ^ (bits * j) * (a.set k x)[j]!.val
      = ∑ j ∈ Finset.range k.val, 2 ^ (bits * j) * a[j]!.val + 2 ^ (bits * k.val) * x.val := by
  rw [Finset.sum_range_succ, Array.getElem!_Nat_set_eq _ _ _ _ ⟨rfl, by simpa using hk⟩]
  refine congrArg (· + _) (Finset.sum_congr rfl fun j hj => ?_)
  rw [Array.getElem!_Nat_set_ne _ _ _ _ (by simp at hj; omega)]


/-- Grouping the digits of an array into `m` blocks of `w` digits. -/
theorem asNat_eq_sum_blocks {ty : UScalarTy} {n : Usize} (bits w m : ℕ) (a : Array (UScalar ty) n)
    (h : w * m = n.val) :
    a.asNat bits = ∑ k ∈ Finset.range m,
      2 ^ (bits * w * k) * ∑ j ∈ Finset.range w, 2 ^ (bits * j) * a[w * k + j]!.val := by
  rw [asNat_eq_sum, ← h]
  clear h
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih, Finset.sum_range_succ, Finset.mul_sum]
    refine congrArg (_ + ·) (Finset.sum_congr rfl fun j _ => ?_)
    rw [← Nat.mul_assoc, ← Nat.pow_add]
    ring_nf

end Aeneas.Std.Array
