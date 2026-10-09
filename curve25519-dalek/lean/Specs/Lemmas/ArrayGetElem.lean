module
public import Aeneas
public section

/-! # Lemmas about reading and rebuilding Aeneas arrays elementwise -/

open Aeneas Aeneas.Std

namespace Aeneas.Std.Array

/-- A five-element array rebuilt from its own elements is the array itself. -/
theorem make_getElem_five {α : Type} (a : Array α 5#usize)
    (h : [a.val[0], a.val[1], a.val[2], a.val[3], a.val[4]].length = (5#usize).val) :
    Array.make 5#usize [a.val[0], a.val[1], a.val[2], a.val[3], a.val[4]] h = a := by
  ext : 1
  rw [Array.make_val]
  apply List.ext_getElem (by simp)
  grind

/-- Overwriting all five elements of `a` with those of `b` gives `b`. -/
theorem set_getElem_five {α : Type} (a b : Array α 5#usize) :
    ((((a.set 0#usize b.val[0]).set 1#usize b.val[1]).set 2#usize b.val[2]).set 3#usize
      b.val[3]).set 4#usize b.val[4] = b := by
  ext : 1
  simp only [Array.set_val_eq]
  apply List.ext_getElem (by simp)
  grind

end Aeneas.Std.Array
