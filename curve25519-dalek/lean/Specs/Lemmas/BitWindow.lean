module
public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public section

/-! # Windows of bits of a number stored in 64-bit limbs

`X / 2 ^ (64 * u) % 2 ^ 64` is limb `u` of `X`. The window of `w` bits of `X` at bit `64 * u + b` is
read from limb `u` alone when `b + w ≤ 64`, and from limbs `u` and `u + 1` otherwise.

The other lemmas cut a number into bytes or limbs: a bit is masked off, a run of digits is
read with shifts, and two words are joined with a shift and an or. -/

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

/-- Bit `k` of a number below `2 ^ k` is clear. -/
theorem and_two_pow_eq_zero_of_lt {x k : ℕ} (hx : x < 2 ^ k) : x &&& 2 ^ k = 0 := by
  rw [Nat.and_two_pow, Nat.testBit_lt_two_pow hx, Bool.toNat_false, Nat.zero_mul]

/-- The bits of `x` from bit `a` on, when there are at most `n` of them. -/
theorem shiftRight_mod_eq_of_lt {x a n : ℕ} (hx : x < 2 ^ (a + n)) :
    x >>> a % 2 ^ n = x / 2 ^ a := by
  rw [Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt]
  rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos a), ← Nat.pow_add, Nat.add_comm]
  exact hx

/-- The bits of `x` from bit `a` on, split at bit `a + n`. -/
theorem shiftRight_mod_add_mul_div (x a n : ℕ) :
    x >>> a % 2 ^ n + 2 ^ n * (x / 2 ^ (a + n)) = x / 2 ^ a := by
  rw [Nat.shiftRight_eq_div_pow, Nat.pow_add, ← Nat.div_div_eq_div_mul, Nat.mod_add_div]

/-- The bits of `x` from bit `a` on (fewer than `b` of them) or-ed with `y` shifted up by `b`, cut
to `m + b` bits: the shifted `y` may first be reduced modulo any multiple `M` of `2 ^ (m + b)`. -/
theorem shiftRight_or_shiftLeft_mod {x a b m M : ℕ} (y : ℕ) (hx : x < 2 ^ (a + b))
    (hM : 2 ^ (m + b) ∣ M) :
    (x >>> a ||| y <<< b % M) % 2 ^ (m + b) = x / 2 ^ a + 2 ^ b * (y % 2 ^ m) := by
  have hlt : x / 2 ^ a < 2 ^ b := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos a), ← Nat.pow_add, Nat.add_comm]
    exact hx
  rw [Nat.or_mod_two_pow, Nat.mod_mod_of_dvd _ hM, ← Nat.or_mod_two_pow, Nat.mul_comm,
    ← Nat.shiftLeft_eq, Nat.add_comm (x / 2 ^ a), Nat.shiftLeft_add_eq_or_of_lt hlt, Nat.or_comm]
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_or, Nat.testBit_shiftRight,
    Nat.testBit_shiftLeft, Nat.testBit_div_two_pow]
  by_cases hi : i < m + b
  · by_cases hb : b ≤ i
    · have hbm : i - b < m := by omega
      simp [hi, hb, hbm, Nat.add_comm a i]
    · simp [hi, hb, Nat.add_comm a i]
  · have hbm : ¬ i - b < m := by omega
    have hxa : x.testBit (a + i) = false :=
      Nat.testBit_lt_two_pow (hx.trans_le (Nat.pow_le_pow_right (by omega) (by omega)))
    simp [hi, hbm, Nat.add_comm i a, hxa]

/-- `k` digits in radix `2 ^ w` of `x`, from bit `a` on, give the next `w * k` bits of `x`. -/
theorem sum_shiftRight_mod (x a w k : ℕ) :
    ∑ j ∈ Finset.range k, 2 ^ (w * j) * (x >>> (a + w * j) % 2 ^ w) = x >>> a % 2 ^ (w * k) := by
  induction k with
  | zero => simp [Nat.mod_one]
  | succ k ih =>
    rw [Finset.sum_range_succ, ih, Nat.mul_succ, Nat.pow_add, Nat.mod_mul, Nat.shiftRight_add,
      Nat.shiftRight_eq_div_pow (x >>> a)]

end Nat
