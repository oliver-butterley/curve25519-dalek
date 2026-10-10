module
public import Specs.Lemmas.AsNat
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public section

/-! # Lemmas about `Array.asInt` -/

open Aeneas Aeneas.Std

namespace Aeneas.Std.Array

/-- `asInt` as a weighted sum of the digits. -/
theorem asInt_eq_sum {ty : IScalarTy} {n : Usize} (bits : ℕ) (a : Array (IScalar ty) n) :
    a.asInt bits = ∑ i ∈ Finset.range n.val, 2 ^ (bits * i) * a[i]!.val := by
  have h : a.val.length = n.val := by simp
  simp only [Array.asInt, Array.getElem!_Nat_eq]
  rw [← h]
  generalize a.val = l
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.length_cons, Finset.sum_range_succ']
    simp only [List.map_cons, List.foldr_cons, ih, List.getElem!_cons_succ, List.getElem!_cons_zero,
      Finset.mul_sum]
    rw [Nat.mul_zero, pow_zero, one_mul, add_comm]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Nat.mul_succ, pow_add]
    ring

/-- Setting digit `k` changes `asInt` by the change of the digit, weighted by `2 ^ (bits * k)`. -/
theorem asInt_set {ty : IScalarTy} {n : Usize} (bits : ℕ) (a : Array (IScalar ty) n) (k : Usize)
    (x : IScalar ty) (hk : k.val < n.val) :
    (a.set k x).asInt bits = a.asInt bits + 2 ^ (bits * k.val) * (x.val - a[k.val]!.val) := by
  have hmem : k.val ∈ Finset.range n.val := Finset.mem_range.mpr hk
  rw [asInt_eq_sum, asInt_eq_sum, ← Finset.add_sum_erase _ _ hmem,
    ← Finset.add_sum_erase _ _ hmem,
    Array.getElem!_Nat_set_eq _ _ _ _ ⟨rfl, by simpa using hk⟩]
  have hrest : ∑ j ∈ (Finset.range n.val).erase k.val, 2 ^ (bits * j) * (a.set k x)[j]!.val
      = ∑ j ∈ (Finset.range n.val).erase k.val, 2 ^ (bits * j) * a[j]!.val :=
    Finset.sum_congr rfl fun j hj => by
      rw [Array.getElem!_Nat_set_ne _ _ _ _ (Ne.symm (Finset.ne_of_mem_erase hj))]
  rw [hrest]
  ring

/-- A sum over `2 m` terms, grouped in consecutive pairs. -/
theorem _root_.Finset.sum_range_two_mul {M : Type*} [AddCommMonoid M] (m : ℕ) (f : ℕ → M) :
    ∑ j ∈ Finset.range (2 * m), f j =
      ∑ i ∈ Finset.range m, (f (2 * i) + f (2 * i + 1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      Finset.sum_range_succ, add_assoc]

/-- Signed digits in radix `2 ^ bits` whose consecutive pairs combine to the digits of `b` in radix
`2 ^ (2 bits)` have the value of `b`. -/
theorem asInt_eq_asNat_of_pairs {tyI : IScalarTy} {tyU : UScalarTy} {n m : Usize} (bits : ℕ)
    (a : Array (IScalar tyI) n) (b : Array (UScalar tyU) m) (h : n.val = 2 * m.val)
    (hab : ∀ i < m.val, a[2 * i]!.val + 2 ^ bits * a[2 * i + 1]!.val = b[i]!.val) :
    a.asInt bits = b.asNat (2 * bits) := by
  rw [asInt_eq_sum, asNat_eq_sum, h, Finset.sum_range_two_mul]
  push_cast
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [← hab i (Finset.mem_range.mp hi)]
  ring

/-- The entries of `Array.repeat n x` below `n`. -/
theorem getElem!_repeat {α : Type} [Inhabited α] {n : Usize} (x : α) {j : ℕ} (hj : j < n.val) :
    (Array.repeat n x)[j]! = x := by
  rw [Array.getElem!_Nat_eq, Array.repeat_val, List.getElem!_replicate _ hj]

/-- An array of zero digits has value `0`. -/
theorem asInt_repeat_zero {ty : IScalarTy} {n : Usize} (bits : ℕ) (z : IScalar ty)
    (hz : z.val = 0) :
    (Array.repeat n z).asInt bits = 0 := by
  rw [asInt_eq_sum]
  exact Finset.sum_eq_zero fun j hj => by
    rw [getElem!_repeat z (Finset.mem_range.mp hj), hz, mul_zero]

end Aeneas.Std.Array
