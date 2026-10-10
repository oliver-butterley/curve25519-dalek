module
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.LinearCombination
public section

/-! # Lemmas about `ZMod` -/

namespace ZMod

theorem natCast_eq_natCast_of_mod_eq {n x y : ℕ} (h : x % n = y) : (x : ZMod n) = y := by
  rw [← natCast_mod, h]

theorem eq_val_of_natCast_eq {n x : ℕ} {X : ZMod n} (hx : x < n) (h : (x : ZMod n) = X) :
    x = X.val := by
  rw [← h, val_natCast_of_lt hx]

theorem natCast_eq_zero_iff_mod {n a : ℕ} : (a : ZMod n) = 0 ↔ a % n = 0 := by
  rw [natCast_eq_zero_iff, Nat.dvd_iff_mod_eq_zero]

end ZMod

/-- In a field containing a square root `i` of `-1`, the fourth roots of unity are `±1`, `±i`. -/
theorem eq_one_or_neg_one_or_of_pow_four_eq_one {K : Type*} [Field K] {t i : K}
    (hi : i ^ 2 = -1) (ht : t ^ 4 = 1) : t = 1 ∨ t = -1 ∨ t = i ∨ t = -i := by
  have h : (t - 1) * (t + 1) * ((t - i) * (t + i)) = 0 := by
    linear_combination ht - (t ^ 2 - 1) * hi
  simp only [mul_eq_zero, sub_eq_zero, add_eq_zero_iff_eq_neg] at h
  tauto
