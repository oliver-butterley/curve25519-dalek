module
public import Curve25519
public import Curve25519Dalek.Funs
public import Specs.Backend.Serial.U64.Defs
public import Subtle
public import Specs.Lemmas.StepSpecs
public import Specs.Lemmas.AsNat
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open curve25519_dalek.backend.serial.u64.field (FieldElement51)

/-- Or-ing in a value shifted above all bits of `a` is addition. -/
private theorem Nat.or_shiftLeft_eq_add {a k : ℕ} (b : ℕ) (ha : a < 2 ^ k) :
    a ||| b <<< k = a + 2 ^ k * b := by
  rw [Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt ha, Nat.shiftLeft_eq, Nat.mul_comm,
    Nat.add_comm]

namespace Aeneas.Std.Array

/-- A little-endian number with `m` digits below `2 ^ b` is below `2 ^ (b * m)`. -/
private theorem sum_digits_lt (b m : ℕ) (x : ℕ → ℕ) (hx : ∀ k < m, x k < 2 ^ b) :
    ∑ k ∈ Finset.range m, 2 ^ (b * k) * x k < 2 ^ (b * m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, Nat.mul_succ, Nat.pow_add]
    calc ∑ k ∈ Finset.range m, 2 ^ (b * k) * x k + 2 ^ (b * m) * x m
        < 2 ^ (b * m) + 2 ^ (b * m) * x m :=
          Nat.add_lt_add_right (ih fun k hk => hx k (by agrind)) _
      _ = 2 ^ (b * m) * (x m + 1) := by ring
      _ ≤ 2 ^ (b * m) * 2 ^ b := Nat.mul_le_mul_left _ (hx m (by agrind))

/-- The `w` bytes of `a` from offset `o` form bytes `o, …, o + w - 1` of `a.asNat 8`. -/
private theorem sum_window_eq {n : Usize} (a : Array U8 n) (o w : ℕ) (h : o + w ≤ n.val) :
    ∑ j ∈ Finset.range w, 2 ^ (8 * j) * a[o + j]!.val
      = a.asNat 8 / 2 ^ (8 * o) % 2 ^ (8 * w) := by
  have hbyte : ∀ k : ℕ, a[k]!.val < 2 ^ 8 := fun k => by scalar_tac
  set M := ∑ j ∈ Finset.range w, 2 ^ (8 * j) * a[o + j]!.val
  set U := ∑ j ∈ Finset.range (n.val - (o + w)), 2 ^ (8 * j) * a[o + w + j]!.val
  have hL := sum_digits_lt 8 o (fun k => a[k]!.val) fun k _ => hbyte k
  have hM : M < 2 ^ (8 * w) := sum_digits_lt 8 w (fun j => a[o + j]!.val) fun j _ => hbyte _
  have hsplit : a.asNat 8 = ∑ k ∈ Finset.range o, 2 ^ (8 * k) * a[k]!.val
      + 2 ^ (8 * o) * (M + 2 ^ (8 * w) * U) := by
    rw [Array.asNat_eq_sum, show n.val = o + w + (n.val - (o + w)) by agrind,
      Finset.sum_range_add, Finset.sum_range_add]
    simp only [M, U, Finset.mul_sum, Nat.mul_add, Nat.pow_add, Nat.add_assoc]
    ring_nf
  rw [hsplit, Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hL, Nat.zero_add,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hM]


/-- A 51-bit limb read from 8 bytes at offset `o`, shifted right by `s`, is bits
`8 o + s, …, 8 o + s + 50` of `a.asNat 8`. -/
private theorem limb_of_window {n : Usize} (a : Array U8 n) (o s : ℕ) (h : o + 8 ≤ n.val)
    (hs : s + 51 ≤ 64) :
    (∑ j ∈ Finset.range 8, 2 ^ (8 * j) * a[o + j]!.val) / 2 ^ s % 2 ^ 51
      = a.asNat 8 / 2 ^ (8 * o + s) % 2 ^ 51 := by
  rw [sum_window_eq a o 8 h, show 8 * 8 = s + (64 - s) by agrind, Nat.pow_add,
    Nat.mod_mul_right_div_self, Nat.div_div_eq_div_mul, ← Nat.pow_add,
    Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by agrind))]

/-- The low 51 bits of 8 bytes at offset `o` are bits `8 o, …, 8 o + 50` of `a.asNat 8`. -/
private theorem limb_of_window_zero {n : Usize} (a : Array U8 n) (o : ℕ) (h : o + 8 ≤ n.val) :
    (∑ j ∈ Finset.range 8, 2 ^ (8 * j) * a[o + j]!.val) % 2 ^ 51
      = a.asNat 8 / 2 ^ (8 * o) % 2 ^ 51 := by
  simpa using limb_of_window a o 0 h (by agrind)

private theorem getElem!_to_slice {α : Type} [Inhabited α] {n : Usize} (a : Array α n) (i : ℕ) :
    a.to_slice[i]! = a[i]! := by
  simp [Slice.getElem!_Nat_eq, Array.getElem!_Nat_eq, Array.val_to_slice]

end Aeneas.Std.Array

/-- Five 51-bit limbs of `x` reassemble `x % 2 ^ 255`. -/
private theorem Nat.limbs51_eq_mod (x : ℕ) :
    x % 2 ^ 51 + 2 ^ 51 * (x / 2 ^ 51 % 2 ^ 51) + 2 ^ 102 * (x / 2 ^ 102 % 2 ^ 51)
      + 2 ^ 153 * (x / 2 ^ 153 % 2 ^ 51) + 2 ^ 204 * (x / 2 ^ 204 % 2 ^ 51) = x % 2 ^ 255 := by
  rw [show 2 ^ 255 = 2 ^ 204 * 2 ^ 51 by norm_num, Nat.mod_mul,
    show 2 ^ 204 = 2 ^ 153 * 2 ^ 51 by norm_num, Nat.mod_mul,
    show 2 ^ 153 = 2 ^ 102 * 2 ^ 51 by norm_num, Nat.mod_mul,
    show 2 ^ 102 = 2 ^ 51 * 2 ^ 51 by norm_num, Nat.mod_mul]

namespace curve25519_dalek.backend.serial.u64.field.FieldElement51.from_bytes

open scoped Specs.IndexStep Specs.UpdateStep

@[step]
theorem load8_at_spec (input : Slice U8) (i : Usize) (hi : i.val + 8 ≤ input.length) :
    load8_at input i ⦃ (r : U64) =>
      r.val = ∑ j ∈ Finset.range 8, 2 ^ (8 * j) * input[i.val + j]!.val ⦄ := by
  unfold load8_at
  step*
  simp only [*, UScalar.val_or, UScalar.cast_val_eq, Finset.sum_range_succ, Finset.sum_range_zero]
  clear * -
  simp_scalar
  simp (disch := scalar_tac) only [Nat.or_shiftLeft_eq_add]
  ring
end curve25519_dalek.backend.serial.u64.field.FieldElement51.from_bytes

namespace curve25519_dalek.backend.serial.u64.field.FieldElement51

open scoped Specs.MaskStep

@[step]
theorem from_bytes_spec (bytes : Array U8 32#usize) :
    from_bytes bytes ⦃ (r : FieldElement51) =>
      r.asNat = bytes.asNat 8 % 2 ^ 255 ∧ ∀ i < 5, r[i]!.val < 2 ^ 51 ⦄ := by
  unfold from_bytes
  step as ⟨two_pow_51, h_two_pow_51⟩
  step as ⟨mask, h_mask⟩
  have h_mask' : mask.val = 2 ^ 51 - 1 := by scalar_tac
  step*
  rw [FieldElement51.asNat_eq, Nat.forall_lt_five]
  simp_lists
  simp only [*, Nat.shiftRight_eq_div_pow, Array.getElem!_to_slice]
  rw [Array.limb_of_window_zero bytes 0 (by scalar_tac),
    Array.limb_of_window bytes 6 3 (by scalar_tac) (by agrind),
    Array.limb_of_window bytes 12 6 (by scalar_tac) (by agrind),
    Array.limb_of_window bytes 19 1 (by scalar_tac) (by agrind),
    Array.limb_of_window bytes 24 12 (by scalar_tac) (by agrind)]
  simp only [Nat.reduceMul, Nat.reduceAdd, pow_zero, Nat.div_one]
  exact ⟨Nat.limbs51_eq_mod _, Nat.mod_lt _ (by positivity), Nat.mod_lt _ (by positivity),
    Nat.mod_lt _ (by positivity), Nat.mod_lt _ (by positivity), Nat.mod_lt _ (by positivity)⟩
end curve25519_dalek.backend.serial.u64.field.FieldElement51
