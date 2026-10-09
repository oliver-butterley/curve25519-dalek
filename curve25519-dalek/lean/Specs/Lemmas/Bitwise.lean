module
public import Aeneas
public section

/-! # Lemmas about bitwise operations on machine integers -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP

namespace Aeneas.Std

/-- Masking with `2 ^ n - 1` keeps the low `n` bits. Activated with
`open scoped Specs.MaskStep` (see `Specs.Lemmas.StepSpecs`). -/
theorem UScalar.and_two_pow_sub_one_spec {ty : UScalarTy} (x m : UScalar ty) (n : ℕ)
    (hm : m.val = 2 ^ n - 1) :
    lift (x &&& m) ⦃ (r : UScalar ty) => r.val = x.val % 2 ^ n ⦄ := by
  step*
  simp only [*, UScalar.val_and, Nat.and_two_pow_sub_one_eq_mod]

end Aeneas.Std
