module
public import Specs.Backend.Serial.U64.Defs
public import Specs.Lemmas.AsNat
public import Specs.Lemmas.Array
public import Mathlib.Data.Nat.ModEq
public section

/-! # Lemmas shared by the proofs of `scalar.rs`

Five 52-bit limbs stay below the Montgomery radix `R = montgomeryRadix` (`Scalar52.asNat_lt`).
Modulo `L`, `R` can be cancelled (`mod_L_of_mul_montgomeryRadix`), and a Montgomery product with
`RR = R^2 mod L` multiplies by `R` (`mod_L_of_mul_montgomeryRadix_eq_mul_RR`). Five limbs
written over a `Scalar52` give its value (`Scalar52.asNat_set_five`) and its limb bounds
(`Scalar52.getElem!_set_five_lt`). -/

open Aeneas Aeneas.Std curve25519

namespace Curve25519Dalek.backend.serial.u64.scalar

/-- Five limbs below `2 ^ 52` represent a number below the Montgomery radix. -/
theorem Scalar52.asNat_lt (a : Scalar52) (h : ∀ i < 5, a[i]!.val < 2 ^ 52) :
    a.asNat < montgomeryRadix :=
  (Array.asNat_lt 52 a h).trans_eq
    ((congrArg (2 ^ ·) (show 52 * (5#usize).val = 260 from rfl)).trans montgomeryRadix_eq.symm)

/-- Multiplication by the Montgomery radix can be cancelled modulo `L`. -/
theorem mod_L_of_mul_montgomeryRadix {x y : ℕ}
    (h : x * montgomeryRadix % L = y * montgomeryRadix % L) : x % L = y % L :=
  Nat.ModEq.cancel_right_of_coprime montgomeryRadix_coprime_L.symm h

/-- A Montgomery product with `RR = R^2 mod L` multiplies by `R` modulo `L`. -/
theorem mod_L_of_mul_montgomeryRadix_eq_mul_RR {r x : ℕ}
    (h : r * montgomeryRadix % L = x * (montgomeryRadix ^ 2 % L) % L) :
    r % L = x * montgomeryRadix % L := by
  rw [← Nat.mod_mod (x * montgomeryRadix) L]
  apply mod_L_of_mul_montgomeryRadix
  rw [h, Nat.mul_mod_mod, Nat.mod_mul_mod, Nat.mul_assoc, ← Nat.pow_two]

/-- The value of five limbs written over a `Scalar52`. -/
theorem Scalar52.asNat_set_five {r : Scalar52} (a : Scalar52) (x0 x1 x2 x3 x4 : U64)
    (hr : r = ((((a.set 0#usize x0).set 1#usize x1).set 2#usize x2).set 3#usize x3).set
      4#usize x4) :
    r.asNat = x0.val + 2 ^ 52 * x1.val + 2 ^ 104 * x2.val + 2 ^ 156 * x3.val
      + 2 ^ 208 * x4.val := by
  rw [hr, Scalar52.asNat_eq]
  simp_lists

/-- The limbs of five values written over a `Scalar52` are below a common bound. -/
theorem Scalar52.getElem!_set_five_lt {r : Scalar52} (a : Scalar52) (x0 x1 x2 x3 x4 : U64)
    {B : ℕ} (hr : r = ((((a.set 0#usize x0).set 1#usize x1).set 2#usize x2).set 3#usize x3).set
      4#usize x4)
    (h0 : x0.val < B) (h1 : x1.val < B) (h2 : x2.val < B) (h3 : x3.val < B) (h4 : x4.val < B) :
    ∀ i < 5, r[i]!.val < B := by
  rw [Nat.forall_lt_five, hr]
  simp_lists
  exact ⟨h0, h1, h2, h3, h4⟩

end Curve25519Dalek.backend.serial.u64.scalar
