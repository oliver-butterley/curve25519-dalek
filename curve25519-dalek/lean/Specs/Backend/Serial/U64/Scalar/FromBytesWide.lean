module
public import Curve25519
public import Curve25519Dalek.Funs
public import Specs.Backend.Serial.U64.Defs
public import Subtle
public import Specs.Backend.Serial.U64.Scalar.Zero
public import Specs.Backend.Serial.U64.Scalar.IndexMut
public import Specs.Backend.Serial.U64.Scalar.MontgomeryMul
public import Specs.Backend.Serial.U64.Scalar.Add
public import Specs.Backend.Serial.U64.Constants.R
public import Specs.Backend.Serial.U64.Constants.RR
public import Specs.Lemmas.AsNat
public import Specs.Lemmas.StepSpecs
public import Mathlib.Tactic.LinearCombination
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open curve25519_dalek.backend.serial.u64.scalar (Scalar52)

namespace curve25519_dalek.backend.serial.u64.scalar.Scalar52

open scoped Specs.GetElemSteps Specs.MaskStep

/-- The inner loop of `from_bytes_wide` packs the 8 bytes of word `i` little-endian. -/
@[step]
theorem from_bytes_wide_loop0_loop0_spec (bytes : Array U8 64#usize) (words : Array U64 8#usize)
    (i : Usize) (hi : i.val < 8) (hw : words[i.val]!.val = 0) :
    from_bytes_wide_loop0_loop0 { start := 0#usize, «end» := 8#usize } bytes words i
    ⦃ (r : Array U64 8#usize) =>
      r[i.val]!.val = ∑ j ∈ Finset.range 8, 2 ^ (8 * j) * bytes[8 * i.val + j]!.val ∧
      ∀ k ≠ i.val, r[k]! = words[k]! ⦄ := by
  unfold from_bytes_wide_loop0_loop0
  apply loop.spec_decr_nat (measure := fun (iter, _) => 8 - iter.start.val)
    (inv := fun (iter, w) => iter.end = 8#usize ∧ iter.start.val ≤ 8 ∧
      w[i.val]!.val = ∑ j ∈ Finset.range iter.start.val, 2 ^ (8 * j) * bytes[8 * i.val + j]!.val ∧
      ∀ k ≠ i.val, w[k]! = words[k]!)
  · rintro ⟨iter, w⟩ ⟨hend, hstart, hwi, hrest⟩
    unfold from_bytes_wide_loop0_loop0.body
    by_cases hlt : iter.start.val < 8
    · step with core.iter.range.IteratorRange.next_Usize_some_spec as ⟨o, iter1, ho, hstart1, hend1⟩
      subst ho
      step as ⟨i1, hi1⟩
      step as ⟨i2, hi2⟩
      step as ⟨b, hb⟩
      step as ⟨b64, hb64⟩
      step as ⟨sh, hsh⟩
      step as ⟨shifted, hshifted, _⟩
      step as ⟨acc, hacc⟩
      step as ⟨acc', hacc', _⟩
      step as ⟨w', hw'i, hw'rest⟩
      have hbyte : b64.val = bytes[8 * i.val + iter.start.val]!.val := by
        rw [hb64, UScalar.cast_val_eq, hb, hi2, hi1, Nat.mul_comm]
        exact Nat.mod_eq_of_lt (by scalar_tac)
      have hb_lt : b64.val < 2 ^ 8 := by rw [hbyte]; scalar_tac
      have hshift : shifted.val = b64.val <<< (8 * iter.start.val) := by
        rw [hshifted, hsh, Nat.mul_comm, Nat.mod_eq_of_lt]
        rw [Nat.shiftLeft_eq, show U64.size = 2 ^ 64 by simp [U64.size, U64.numBits]]
        exact Nat.byte_mul_two_pow_lt hb_lt hlt
      have hacc_lt : acc.val < 2 ^ (8 * iter.start.val) := by
        rw [hacc, hwi]
        exact Array.sum_pow_mul_lt 8 _ _ fun j _ => by scalar_tac
      refine ⟨by rw [hend1, hend], by scalar_tac, ?_, fun k hk => (hw'rest k hk).trans (hrest k hk),
        by scalar_tac⟩
      rw [hw'i, hacc', UScalar.val_or, hshift, Nat.or_shiftLeft_eq_add_pow_mul _ hacc_lt, hacc, hwi,
        hstart1, Finset.sum_range_succ, hbyte]
    · step with core.iter.range.IteratorRange.next_Usize_none_spec as ⟨o, iter1, ho, hiter1⟩
      subst ho
      have hk : iter.start.val = 8 := by scalar_tac
      rw [hk] at hwi
      simp only [WP.spec_ok]
      exact ⟨hwi, hrest⟩
  · exact ⟨rfl, by simp, by simpa using hw, fun _ _ => rfl⟩

/-- The outer loop of `from_bytes_wide` packs the 64 bytes into eight little-endian words. -/
@[step]
theorem from_bytes_wide_loop0_spec (bytes : Array U8 64#usize) :
    from_bytes_wide_loop0 { start := 0#usize, «end» := 8#usize } bytes (Array.repeat 8#usize 0#u64)
    ⦃ (w : Array U64 8#usize) =>
      ∀ k < 8, w[k]!.val = ∑ j ∈ Finset.range 8, 2 ^ (8 * j) * bytes[8 * k + j]!.val ⦄ := by
  unfold from_bytes_wide_loop0
  apply loop.spec_decr_nat (measure := fun (iter, _) => 8 - iter.start.val)
    (inv := fun (iter, w) => iter.end = 8#usize ∧ iter.start.val ≤ 8 ∧
      (∀ k < iter.start.val,
        w[k]!.val = ∑ j ∈ Finset.range 8, 2 ^ (8 * j) * bytes[8 * k + j]!.val) ∧
      ∀ k < 8, iter.start.val ≤ k → w[k]!.val = 0)
  · rintro ⟨iter, w⟩ ⟨hend, hstart, hdone, hzero⟩
    unfold from_bytes_wide_loop0.body
    by_cases hlt : iter.start.val < 8
    · step with core.iter.range.IteratorRange.next_Usize_some_spec as ⟨o, iter1, ho, hstart1, hend1⟩
      subst ho
      step with from_bytes_wide_loop0_loop0_spec as ⟨w', hw'i, hw'rest⟩
      refine ⟨by rw [hend1, hend], by scalar_tac, fun k hk => ?_, fun k hk hsk => ?_, by scalar_tac⟩
      · by_cases hki : k = iter.start.val
        · rw [hki, hw'i]
        · rw [hw'rest k hki]
          exact hdone k (by scalar_tac)
      · rw [hw'rest k (by scalar_tac)]
        exact hzero k hk (by scalar_tac)
    · step with core.iter.range.IteratorRange.next_Usize_none_spec as ⟨o, iter1, ho, hiter1⟩
      subst ho
      have hk : iter.start.val = 8 := by scalar_tac
      rw [hk] at hdone
      simp only [WP.spec_ok]
      exact hdone
  · refine ⟨rfl, by simp, fun _ hk => absurd hk (by simp), fun k hk _ => ?_⟩
    match k, hk with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ => rfl


/-- Limb 1: word 0 without its low 52 bits, and the low 40 bits of word 1. -/
private theorem from_bytes_wide.limb_1 (w0 w1 : U64) :
    (w0.val >>> 52 ||| w1.val <<< 12 % U64.size) % 2 ^ 52
      = w0.val / 2 ^ 52 + 2 ^ 12 * (w1.val % 2 ^ 40) := by
  bvify 64
  simp only [U64.ofNat_shiftLeft_mod_size_eq]
  bv_decide

/-- Limb 2: word 1 without its low 40 bits, and the low 28 bits of word 2. -/
private theorem from_bytes_wide.limb_2 (w1 w2 : U64) :
    (w1.val >>> 40 ||| w2.val <<< 24 % U64.size) % 2 ^ 52
      = w1.val / 2 ^ 40 + 2 ^ 24 * (w2.val % 2 ^ 28) := by
  bvify 64
  simp only [U64.ofNat_shiftLeft_mod_size_eq]
  bv_decide

/-- Limb 3: word 2 without its low 28 bits, and the low 16 bits of word 3. -/
private theorem from_bytes_wide.limb_3 (w2 w3 : U64) :
    (w2.val >>> 28 ||| w3.val <<< 36 % U64.size) % 2 ^ 52
      = w2.val / 2 ^ 28 + 2 ^ 36 * (w3.val % 2 ^ 16) := by
  bvify 64
  simp only [U64.ofNat_shiftLeft_mod_size_eq]
  bv_decide

/-- Limb 4: word 3 without its low 16 bits, and the low 4 bits of word 4. -/
private theorem from_bytes_wide.limb_4 (w3 w4 : U64) :
    (w3.val >>> 16 ||| w4.val <<< 48 % U64.size) % 2 ^ 52
      = w3.val / 2 ^ 16 + 2 ^ 48 * (w4.val % 2 ^ 4) := by
  bvify 64
  simp only [U64.ofNat_shiftLeft_mod_size_eq]
  bv_decide

/-- Limb 5: bits 4 to 55 of word 4. -/
private theorem from_bytes_wide.limb_5 (w4 : U64) :
    w4.val >>> 4 % 2 ^ 52 + 2 ^ 52 * (w4.val / 2 ^ 56) = w4.val / 2 ^ 4 := by
  bvify 64
  bv_decide

/-- Limb 6: word 4 without its low 56 bits, and the low 44 bits of word 5. -/
private theorem from_bytes_wide.limb_6 (w4 w5 : U64) :
    (w4.val >>> 56 ||| w5.val <<< 8 % U64.size) % 2 ^ 52
      = w4.val / 2 ^ 56 + 2 ^ 8 * (w5.val % 2 ^ 44) := by
  bvify 64
  simp only [U64.ofNat_shiftLeft_mod_size_eq]
  bv_decide

/-- Limb 7: word 5 without its low 44 bits, and the low 32 bits of word 6. -/
private theorem from_bytes_wide.limb_7 (w5 w6 : U64) :
    (w5.val >>> 44 ||| w6.val <<< 20 % U64.size) % 2 ^ 52
      = w5.val / 2 ^ 44 + 2 ^ 20 * (w6.val % 2 ^ 32) := by
  bvify 64
  simp only [U64.ofNat_shiftLeft_mod_size_eq]
  bv_decide

/-- Limb 8: word 6 without its low 32 bits, and the low 20 bits of word 7. -/
private theorem from_bytes_wide.limb_8 (w6 w7 : U64) :
    (w6.val >>> 32 ||| w7.val <<< 32 % U64.size) % 2 ^ 52
      = w6.val / 2 ^ 32 + 2 ^ 32 * (w7.val % 2 ^ 20) := by
  bvify 64
  simp only [U64.ofNat_shiftLeft_mod_size_eq]
  bv_decide

/-- The low five limbs represent the low 260 bits of the eight words. -/
private theorem from_bytes_wide.lo_eq (w0 w1 w2 w3 w4 : U64) :
    w0.val % 2 ^ 52 + 2 ^ 52 * ((w0.val >>> 52 ||| w1.val <<< 12 % U64.size) % 2 ^ 52)
      + 2 ^ 104 * ((w1.val >>> 40 ||| w2.val <<< 24 % U64.size) % 2 ^ 52)
      + 2 ^ 156 * ((w2.val >>> 28 ||| w3.val <<< 36 % U64.size) % 2 ^ 52)
      + 2 ^ 208 * ((w3.val >>> 16 ||| w4.val <<< 48 % U64.size) % 2 ^ 52)
      = w0.val + 2 ^ 64 * w1.val + 2 ^ 128 * w2.val + 2 ^ 192 * w3.val
        + 2 ^ 256 * (w4.val % 2 ^ 4) := by
  have g1 := from_bytes_wide.limb_1 w0 w1
  have g2 := from_bytes_wide.limb_2 w1 w2
  have g3 := from_bytes_wide.limb_3 w2 w3
  have g4 := from_bytes_wide.limb_4 w3 w4
  have d0 := Nat.div_add_mod w0.val (2 ^ 52)
  have d1 := Nat.div_add_mod w1.val (2 ^ 40)
  have d2 := Nat.div_add_mod w2.val (2 ^ 28)
  have d3 := Nat.div_add_mod w3.val (2 ^ 16)
  zify at g1 g2 g3 g4 d0 d1 d2 d3 ⊢
  linear_combination 2 ^ 52 * g1 + 2 ^ 104 * g2 + 2 ^ 156 * g3 + 2 ^ 208 * g4 + d0
    + 2 ^ 64 * d1 + 2 ^ 128 * d2 + 2 ^ 192 * d3

/-- The high five limbs represent the eight words shifted right by 260 bits. -/
private theorem from_bytes_wide.hi_eq (w4 w5 w6 w7 : U64) :
    w4.val >>> 4 % 2 ^ 52 + 2 ^ 52 * ((w4.val >>> 56 ||| w5.val <<< 8 % U64.size) % 2 ^ 52)
      + 2 ^ 104 * ((w5.val >>> 44 ||| w6.val <<< 20 % U64.size) % 2 ^ 52)
      + 2 ^ 156 * ((w6.val >>> 32 ||| w7.val <<< 32 % U64.size) % 2 ^ 52)
      + 2 ^ 208 * (w7.val >>> 20)
      = w4.val / 2 ^ 4 + 2 ^ 60 * w5.val + 2 ^ 124 * w6.val + 2 ^ 188 * w7.val := by
  have g5 := from_bytes_wide.limb_5 w4
  have g6 := from_bytes_wide.limb_6 w4 w5
  have g7 := from_bytes_wide.limb_7 w5 w6
  have g8 := from_bytes_wide.limb_8 w6 w7
  have g9 : w7.val >>> 20 = w7.val / 2 ^ 20 := Nat.shiftRight_eq_div_pow _ _
  have d5 := Nat.div_add_mod w5.val (2 ^ 44)
  have d6 := Nat.div_add_mod w6.val (2 ^ 32)
  have d7 := Nat.div_add_mod w7.val (2 ^ 20)
  zify at g5 g6 g7 g8 g9 d5 d6 d7 ⊢
  linear_combination g5 + 2 ^ 52 * g6 + 2 ^ 104 * g7 + 2 ^ 156 * g8 + 2 ^ 208 * g9
    + 2 ^ 60 * d5 + 2 ^ 124 * d6 + 2 ^ 188 * d7


set_option exponentiation.threshold 448 in
/-- The ten limbs cut from eight words: the low five plus `2 ^ 260` times the high five. -/
private theorem from_bytes_wide.limbs_eq (w0 w1 w2 w3 w4 w5 w6 w7 : U64) :
    (w4.val >>> 4 % 2 ^ 52 + 2 ^ 52 * ((w4.val >>> 56 ||| w5.val <<< 8 % U64.size) % 2 ^ 52)
      + 2 ^ 104 * ((w5.val >>> 44 ||| w6.val <<< 20 % U64.size) % 2 ^ 52)
      + 2 ^ 156 * ((w6.val >>> 32 ||| w7.val <<< 32 % U64.size) % 2 ^ 52)
      + 2 ^ 208 * (w7.val >>> 20)) * 2 ^ 260
    + (w0.val % 2 ^ 52 + 2 ^ 52 * ((w0.val >>> 52 ||| w1.val <<< 12 % U64.size) % 2 ^ 52)
      + 2 ^ 104 * ((w1.val >>> 40 ||| w2.val <<< 24 % U64.size) % 2 ^ 52)
      + 2 ^ 156 * ((w2.val >>> 28 ||| w3.val <<< 36 % U64.size) % 2 ^ 52)
      + 2 ^ 208 * ((w3.val >>> 16 ||| w4.val <<< 48 % U64.size) % 2 ^ 52))
      = w0.val + 2 ^ 64 * (w1.val + 2 ^ 64 * (w2.val + 2 ^ 64 * (w3.val + 2 ^ 64 * (w4.val
        + 2 ^ 64 * (w5.val + 2 ^ 64 * (w6.val + 2 ^ 64 * w7.val)))))) := by
  rw [from_bytes_wide.lo_eq, from_bytes_wide.hi_eq]
  have d4 := Nat.div_add_mod w4.val (2 ^ 4)
  zify at d4 ⊢
  linear_combination 2 ^ 256 * d4

/-- `L` is odd, so powers of two are invertible modulo `L`. -/
private theorem coprime_L_two_pow (k : ℕ) : Nat.Coprime L (2 ^ k) := by
  have hodd : L % 2 = 1 := by
    rw [← Nat.mod_mod_of_dvd L (show 2 ∣ 2 ^ 52 by norm_num), L_mod_two_pow_52]
  exact Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr (Nat.odd_iff.mpr hodd))

/-- Cancelling the Montgomery factor `2 ^ 260` modulo `L`. -/
private theorem mod_L_cancel {x y : ℕ} (h : x * 2 ^ 260 % L = y * 2 ^ 260 % L) :
    x % L = y % L :=
  Nat.ModEq.cancel_right_of_coprime (coprime_L_two_pow 260) h

/-- `montgomery_mul` by `R = 2 ^ 260 mod L` reduces modulo `L`. -/
private theorem montgomery_mul_R_spec (a : Scalar52) (ha : ∀ i < 5, a[i]!.val < 2 ^ 52) :
    montgomery_mul a constants.R ⦃ (r : Scalar52) =>
      r.asNat % L = a.asNat % L ∧ r.asNat < L ∧ ∀ i < 5, r[i]!.val < 2 ^ 52 ⦄ := by
  obtain ⟨hR, hR_limbs⟩ := constants.R_spec
  have hR_lt : constants.R.asNat < L := hR ▸ Nat.mod_lt _ L_pos
  apply spec_mono (montgomery_mul_spec a _ ha hR_limbs
    (Nat.mul_lt_mul'' (Scalar52.asNat_lt a ha) hR_lt))
  rintro r ⟨hr, hr_lt, hr_limbs⟩
  refine ⟨mod_L_cancel ?_, hr_lt, hr_limbs⟩
  rw [hr, hR, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]

/-- `montgomery_mul` by `RR = 2 ^ 520 mod L` multiplies by `R = 2 ^ 260 mod L` modulo `L`. -/
private theorem montgomery_mul_RR_spec (a : Scalar52) (ha : ∀ i < 5, a[i]!.val < 2 ^ 52) :
    montgomery_mul a constants.RR ⦃ (r : Scalar52) =>
      r.asNat % L = a.asNat * constants.R.asNat % L ∧ r.asNat < L ∧
      ∀ i < 5, r[i]!.val < 2 ^ 52 ⦄ := by
  obtain ⟨hRR, hRR_limbs⟩ := constants.RR_spec
  have hRR_lt : constants.RR.asNat < L := hRR ▸ Nat.mod_lt _ L_pos
  apply spec_mono (montgomery_mul_spec a _ ha hRR_limbs
    (Nat.mul_lt_mul'' (Scalar52.asNat_lt a ha) hRR_lt))
  rintro r ⟨hr, hr_lt, hr_limbs⟩
  refine ⟨mod_L_cancel ?_, hr_lt, hr_limbs⟩
  have e1 : a.asNat * (2 ^ 520 % L) % L = a.asNat * 2 ^ 520 % L := (Nat.mod_modEq _ L).mul_left _
  have e2 : a.asNat * (2 ^ 260 % L) * 2 ^ 260 % L = a.asNat * 2 ^ 260 * 2 ^ 260 % L :=
    ((Nat.mod_modEq _ L).mul_left _).mul_right _
  rw [hr, hRR, constants.R_spec.1, e1, e2, Nat.mul_assoc, ← Nat.pow_add,
    show 260 + 260 = 520 from rfl]

set_option exponentiation.threshold 448 in
/-- The 64 bytes as eight little-endian words, in Horner form. -/
private theorem from_bytes_wide.bytes_eq (bytes : Array U8 64#usize) (w : Array U64 8#usize)
    (hw : ∀ k < 8, w[k]!.val = ∑ j ∈ Finset.range 8, 2 ^ (8 * j) * bytes[8 * k + j]!.val) :
    bytes.asNat 8 = w[0]!.val + 2 ^ 64 * (w[1]!.val + 2 ^ 64 * (w[2]!.val + 2 ^ 64 * (w[3]!.val
      + 2 ^ 64 * (w[4]!.val + 2 ^ 64 * (w[5]!.val + 2 ^ 64 * (w[6]!.val
      + 2 ^ 64 * w[7]!.val)))))) := by
  rw [Array.asNat_eq_sum_blocks 8 8 8 bytes rfl, Finset.sum_range_succ (n := 7),
    Finset.sum_range_succ (n := 6), Finset.sum_range_succ (n := 5),
    Finset.sum_range_succ (n := 4), Finset.sum_range_succ (n := 3),
    Finset.sum_range_succ (n := 2), Finset.sum_range_succ (n := 1), Finset.sum_range_one,
    ← hw 0 (by norm_num), ← hw 1 (by norm_num), ← hw 2 (by norm_num), ← hw 3 (by norm_num),
    ← hw 4 (by norm_num), ← hw 5 (by norm_num), ← hw 6 (by norm_num), ← hw 7 (by norm_num)]
  ring

/-- The value of five limbs written over a `Scalar52`. -/
private theorem asNat_set_five (a : Scalar52) (x0 x1 x2 x3 x4 : U64) :
    Scalar52.asNat ((((((a.set 0#usize x0).set 1#usize x1).set 2#usize x2).set 3#usize x3).set
      4#usize x4))
      = x0.val + 2 ^ 52 * x1.val + 2 ^ 104 * x2.val + 2 ^ 156 * x3.val + 2 ^ 208 * x4.val := by
  rw [Scalar52.asNat_eq]
  simp_lists

@[step]
theorem from_bytes_wide_spec (bytes : Array U8 64#usize) :
    from_bytes_wide bytes ⦃ (r : Scalar52) =>
      r.asNat = bytes.asNat 8 % L ∧ ∀ i < 5, r[i]!.val < 2 ^ 52 ⦄ := by
  unfold from_bytes_wide
  step with from_bytes_wide_loop0_spec as ⟨w, hw⟩
  have hbytes := from_bytes_wide.bytes_eq bytes w hw
  clear hw
  generalize hw0 : w[0]! = w0 at hbytes
  generalize hw1 : w[1]! = w1 at hbytes
  generalize hw2 : w[2]! = w2 at hbytes
  generalize hw3 : w[3]! = w3 at hbytes
  generalize hw4 : w[4]! = w4 at hbytes
  generalize hw5 : w[5]! = w5 at hbytes
  generalize hw6 : w[6]! = w6 at hbytes
  generalize hw7 : w[7]! = w7 at hbytes
  have hw7_lt : w7.val < 2 ^ 64 := by scalar_tac
  step as ⟨two_pow_52, htwo_pow_52⟩
  step as ⟨mask, hmask⟩
  have hmask' : mask.val = 2 ^ 52 - 1 := by scalar_tac
  step* 49
  step with montgomery_mul_R_spec as ⟨lo, hlo, hlo_lt, hlo_limbs⟩
  · clear hbytes
    rw [Nat.forall_lt_five]
    simp only [*]
    simp_lists
    simp only [*, UScalar.val_or]
    exact ⟨Nat.mod_lt _ (by norm_num), Nat.mod_lt _ (by norm_num), Nat.mod_lt _ (by norm_num),
      Nat.mod_lt _ (by norm_num), Nat.mod_lt _ (by norm_num)⟩
  step with montgomery_mul_RR_spec as ⟨hi, hhi, hhi_lt, hhi_limbs⟩
  · clear hlo hlo_lt hlo_limbs hbytes
    rw [Nat.forall_lt_five]
    simp only [*]
    simp_lists
    simp only [*, UScalar.val_or]
    refine ⟨Nat.mod_lt _ (by norm_num), Nat.mod_lt _ (by norm_num), Nat.mod_lt _ (by norm_num),
      Nat.mod_lt _ (by norm_num), ?_⟩
    rw [Nat.shiftRight_eq_div_pow]
    exact Nat.div_lt_of_lt_mul (hw7_lt.trans (by norm_num))
  step as ⟨r, hr, hr_limbs⟩
  refine ⟨?_, hr_limbs⟩
  have e : ∀ x, x * constants.R.asNat % L = x * 2 ^ 260 % L := fun x => by
    rw [constants.R_spec.1]
    exact (Nat.mod_modEq _ L).mul_left _
  rw [hr, Nat.add_mod, hhi, e, hlo, ← Nat.add_mod]
  refine congrArg (· % L) ?_
  rw [hbytes]
  clear hr hhi hlo hbytes
  simp only [*]
  rw [asNat_set_five, asNat_set_five]
  simp only [*, UScalar.val_or]
  exact from_bytes_wide.limbs_eq w0 w1 w2 w3 w4 w5 w6 w7

end curve25519_dalek.backend.serial.u64.scalar.Scalar52
