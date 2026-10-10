module
public import Mathlib.Data.Nat.Bitwise
public section

/-! # Windows of bits of a number stored in 64-bit limbs

`X / 2 ^ (64 * u) % 2 ^ 64` is limb `u` of `X`. The window of `w` bits of `X` at bit `64 * u + b` is
read from limb `u` alone when `b + w ≤ 64`, and from limbs `u` and `u + 1` otherwise. -/

namespace Nat

/-- A window of bits inside one limb. -/
theorem window_in_limb (X u b w : ℕ) (h : b + w ≤ 64) :
    X / 2 ^ (64 * u) % 2 ^ 64 / 2 ^ b % 2 ^ w = X / 2 ^ (64 * u + b) % 2 ^ w := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  by_cases hi : i < w
  · have hib : i + b < 64 := by omega
    simp only [hi, hib, decide_true, Bool.true_and]
    congr 1
    omega
  · simp [hi]

/-- A window of bits across two limbs: the high bits of limb `u` or-ed with the low bits of limb
`u + 1` shifted up. -/
theorem window_across (X u b w : ℕ) (hb : b < 64) (hw : w ≤ 64) :
    (X / 2 ^ (64 * u) % 2 ^ 64 / 2 ^ b ||| X / 2 ^ (64 * (u + 1)) % 2 ^ 64 * 2 ^ (64 - b) % 2 ^ 64)
      % 2 ^ w = X / 2 ^ (64 * u + b) % 2 ^ w := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.testBit_or,
    Nat.testBit_mul_two_pow]
  by_cases hi : i < w
  · have hi64 : i < 64 := by omega
    simp only [hi, hi64, decide_true, Bool.true_and]
    by_cases hib : i + b < 64
    · have hnb : ¬ 64 - b ≤ i := by omega
      simp only [hib, hnb, decide_true, decide_false, Bool.true_and, Bool.false_and, Bool.or_false]
      congr 1
      omega
    · have hnb : 64 - b ≤ i := by omega
      have hlt : i - (64 - b) < 64 := by omega
      simp only [hib, hnb, hlt, decide_true, decide_false, Bool.true_and, Bool.false_and,
        Bool.false_or]
      congr 1
      omega
  · simp [hi]

end Nat
