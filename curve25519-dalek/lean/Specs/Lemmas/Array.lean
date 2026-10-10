module
public import Aeneas
public section

/-! # Lemmas about Aeneas arrays -/

open Aeneas Aeneas.Std

namespace Aeneas.Std.Array

/-- `index_usize` with the result as `getElem!`, which `simp_lists` and `agrind` handle well on
chains of `set`. Activated with `open scoped Specs.IndexStep Specs.UpdateStep`. -/
theorem index_usize_getElem!_spec {α : Type} [Inhabited α] {n : Usize} (v : Array α n) (i : Usize)
    (hi : i.val < n.val) :
    v.index_usize i ⦃ (x : α) => x = v[i.val]! ⦄ := by
  step*
  simp_lists [*]

/-- `Slice.index_usize` with the result as `getElem!`. Activated with
`open scoped Specs.IndexStep Specs.UpdateStep`. -/
theorem _root_.Aeneas.Std.Slice.index_usize_getElem!_spec {α : Type} [Inhabited α] (s : Slice α)
    (i : Usize) (hi : i.val < s.length) :
    s.index_usize i ⦃ (x : α) => x = s[i.val]! ⦄ := by
  step*
  simp_lists [*]

/-- `update` described elementwise with `getElem!`, which `agrind` can chain through several
updates. Activated with `open scoped Specs.IndexStep Specs.UpdateStep`. -/
theorem update_getElem!_spec {α : Type} [Inhabited α] {n : Usize} (v : Array α n) (i : Usize)
    (x : α) (hi : i.val < n.val) :
    v.update i x ⦃ (nv : Array α n) => nv[i.val]! = x ∧ ∀ j ≠ i.val, nv[j]! = v[j]! ⦄ := by
  step*
  subst_vars
  exact ⟨Array.getElem!_Nat_set_eq _ _ _ _ ⟨rfl, by simpa using hi⟩,
    fun j hj => Array.getElem!_Nat_set_ne _ _ _ _ (Ne.symm hj)⟩

/-- The entries of an array literal `Array.make n l`. -/
theorem getElem!_make {α : Type} [Inhabited α] {n : Usize} (l : List α) (hl : l.length = n.val)
    (i : ℕ) : (Array.make n l hl)[i]! = l[i]! := by
  simp only [Array.getElem!_Nat_eq, Array.make_val]

/-- `index_usize` on an array literal `Array.make n l`, with the result as `l[i]!`. -/
theorem index_usize_make_spec {α : Type} [Inhabited α] {n : Usize} (l : List α)
    (hl : l.length = n.val) (i : Usize) (hi : i.val < n.val) :
    (Array.make n l hl).index_usize i ⦃ (x : α) => x = l[i.val]! ⦄ := by
  step*
  simp_lists [*, Array.make_val]

/-- A bound on five limbs, unfolded into its five instances (for `simp_lists`). -/
theorem _root_.Nat.forall_lt_five {P : ℕ → Prop} :
    (∀ i < 5, P i) ↔ P 0 ∧ P 1 ∧ P 2 ∧ P 3 ∧ P 4 := by
  constructor
  · intro h
    exact ⟨h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide)⟩
  · rintro ⟨h0, h1, h2, h3, h4⟩ i hi
    match i, hi with
    | 0, _ => exact h0
    | 1, _ => exact h1
    | 2, _ => exact h2
    | 3, _ => exact h3
    | 4, _ => exact h4

end Aeneas.Std.Array
