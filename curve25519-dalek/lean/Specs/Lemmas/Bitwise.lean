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

namespace Aeneas.Std

/-- The value of a left shift with wrap-around, as a bit vector (for `bvify` goals). -/
theorem U64.ofNat_shiftLeft_mod_size_eq (x : U64) (k : ℕ) :
    BitVec.ofNat 64 (x.val <<< k % U64.size) = x.bv <<< k := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_shiftLeft, U64.size, U64.numBits]

end Aeneas.Std

/-- Or-ing in a value shifted above all bits of `acc` is addition. -/
theorem Nat.or_shiftLeft_eq_add_pow_mul {acc k : ℕ} (b : ℕ) (hacc : acc < 2 ^ k) :
    acc ||| b <<< k = acc + 2 ^ k * b := by
  rw [Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt hacc, Nat.shiftLeft_eq, Nat.mul_comm,
    Nat.add_comm]

/-- A byte shifted by fewer than 8 bytes fits in 64 bits. -/
theorem Nat.byte_mul_two_pow_lt {x k : ℕ} (hx : x < 2 ^ 8) (hk : k < 8) :
    x * 2 ^ (8 * k) < 2 ^ 64 :=
  calc x * 2 ^ (8 * k) < 2 ^ 8 * 2 ^ (8 * k) := Nat.mul_lt_mul_of_pos_right hx (by positivity)
    _ = 2 ^ (8 * (k + 1)) := by ring
    _ ≤ 2 ^ 64 := Nat.pow_le_pow_right (by norm_num) (by omega)
