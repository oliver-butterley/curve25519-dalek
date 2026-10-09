module
public import Mathlib.Data.ZMod.Basic
public section

/-! # Lemmas about `ZMod` -/

namespace ZMod

theorem natCast_eq_natCast_of_mod_eq {n x y : ℕ} (h : x % n = y) : (x : ZMod n) = y := by
  rw [← natCast_mod, h]

theorem eq_val_of_natCast_eq {n x : ℕ} {X : ZMod n} (hx : x < n) (h : (x : ZMod n) = X) :
    x = X.val := by
  rw [← h, val_natCast_of_lt hx]

end ZMod
