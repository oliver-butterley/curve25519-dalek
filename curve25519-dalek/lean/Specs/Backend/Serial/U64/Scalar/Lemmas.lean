module
public import Specs.Backend.Serial.U64.Defs
public import Specs.Lemmas.AsNat
public import Mathlib.Data.Nat.ModEq
public section

/-! # Lemmas shared by the proofs of `scalar.rs`

Five 52-bit limbs stay below the Montgomery radix `R = montgomeryRadix` (`Scalar52.asNat_lt`).
Modulo `L`, `R` can be cancelled (`mod_L_of_mul_montgomeryRadix`), and a Montgomery product with
`RR = R^2 mod L` multiplies by `R` (`mod_L_of_mul_montgomeryRadix_eq_mul_RR`). -/

open Aeneas Aeneas.Std curve25519

namespace curve25519_dalek.backend.serial.u64.scalar

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

end curve25519_dalek.backend.serial.u64.scalar
