module
public import Curve25519
public import Curve25519Dalek.Funs
public import Specs.Defs
public import Specs.Backend.Serial.U64.Defs
public import Subtle
public import Specs.Lemmas.Bytes
public import Specs.Lemmas.BitWindow
public import Specs.Lemmas.AsInt
public import Specs.Lemmas.Array
public import Specs.Scalar.ReadLeU64Into
public import Specs.Scalar.AsRadix16
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.IntervalCases
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open curve25519_dalek.scalar (Scalar HalfWidthScalar)
open curve25519_dalek.backend.serial.u64.scalar (montgomeryRadix)

namespace curve25519_dalek.scalar.Scalar

set_option linter.hashCommand false in
#decompose as_radix_2w_loop.body as_radix_2w_loop.body_eq
  letAt 1 (branch 1 (letRange 6 9)) => as_radix_2w_loop.body.digit

attribute [nolint docBlame defsWithUnderscore] as_radix_2w_loop.body.digit

/-- The bit buffer of `as_radix_2w`: its low `w` bits are the bits `64 u + b …` of `X`. -/
private theorem radix_bit_buf_spec (x : Array U64 4#usize) (X : ℕ) (hX : x.asNat 64 = X)
    (w u b t : Usize) (hw : w.val ≤ 8) (hu : u.val ≤ 3) (hb : b.val < 64)
    (ht : t.val = 64 - w.val) (iter : core.ops.range.Range Usize) :
    (if b < t
      then
        do
        let i2 ← Array.index_usize x u
        let bit_buf1 ← i2 >>> b
        ok (iter, bit_buf1)
      else
        do
        let i2 ←
          if u = 3#usize
          then
            do
            let i3 ← Array.index_usize x u
            i3 >>> b
          else
            do
            let i3 ← Array.index_usize x u
            let i4 ← i3 >>> b
            let i5 ← 1#usize + u
            let i6 ← Array.index_usize x i5
            let i7 ← 64#usize - b
            let i8 ← i6 <<< i7
            ok (i4 ||| i8)
        ok (iter, i2)) ⦃ (iter' : core.ops.range.Range Usize) (bb : U64) =>
      iter' = iter ∧ bb.val % 2 ^ w.val = X / 2 ^ (64 * u.val + b.val) % 2 ^ w.val ⦄ := by
  have hlimb (j : ℕ) : X / 2 ^ (64 * j) % 2 ^ 64 = x[j]!.val := by
    rw [← hX]
    exact Array.asNat_div_pow_mod 64 x (fun i _ => by simpa using (x[i]!).hBounds) j
  have hX256 : X < 2 ^ 256 := by
    rw [← hX]
    exact Array.asNat_lt 64 x (fun i _ => by simpa using (x[i]!).hBounds)
  split_ifs with hbt hu3
  · step with Array.index_usize_getElem!_spec as ⟨l, hl⟩
    step as ⟨r, hr, hrbv⟩
    rw [hr, Nat.shiftRight_eq_div_pow, hl, ← hlimb]
    exact Nat.window_in_limb X u.val b.val w.val (by scalar_tac)
  · step with Array.index_usize_getElem!_spec as ⟨l, hl⟩
    step as ⟨r, hr, hrbv⟩
    rw [hr, Nat.shiftRight_eq_div_pow, hl, ← hlimb]
    have hu3' : u.val = 3 := by rw [hu3]; rfl
    have hlt : X / 2 ^ (64 * u.val) < 2 ^ 64 := by
      rw [hu3', Nat.div_lt_iff_lt_mul (by positivity), ← Nat.pow_add]
      exact hX256
    rw [Nat.mod_eq_of_lt hlt, Nat.div_div_eq_div_mul, ← Nat.pow_add]
  · step with Array.index_usize_getElem!_spec as ⟨l, hl⟩
    step as ⟨r, hr, hrbv⟩
    step as ⟨u1, hu1⟩
    step with Array.index_usize_getElem!_spec as ⟨l1, hl1⟩
    step as ⟨k, hk⟩
    step as ⟨r1, hr1, hr1bv⟩
    rw [UScalar.val_or, hr, hr1, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, hl, hl1, hu1, hk,
      ← hlimb, ← hlimb]
    have := Nat.window_across X u.val b.val w.val hb (by scalar_tac)
    rw [Nat.add_comm 1 u.val]
    simpa [U64.size, U64.numBits] using this
/-- The recentred digit of a window `coef ≤ 2 P` (`2 ^ w = 2 P`) and its carry. -/
private theorem radix_digit {coef P : ℕ} (hP : 1 ≤ P) (hcoef : coef ≤ 2 * P) :
    ((coef + P) / (2 * P) = 0 ∧ coef < P) ∨ ((coef + P) / (2 * P) = 1 ∧ P ≤ coef) := by
  by_cases h : coef < P
  · exact Or.inl ⟨Nat.div_eq_of_lt (by omega), h⟩
  · exact Or.inr ⟨Nat.div_eq_of_lt_le (by omega) (by omega), by omega⟩

/-- Near the top (`252 ≤ pos`), the window of a number below `2 ^ 255` plus a carry is at most
`8`. -/
private theorem radix_top_window {X pos c w : ℕ} (hX : X < 2 ^ 255) (hpos : 252 ≤ pos)
    (hc : c ≤ 1) :
    c + X / 2 ^ pos % 2 ^ w ≤ 8 := by
  have hY : X / 2 ^ pos < 2 ^ 3 := by
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← Nat.pow_add]
    exact lt_of_lt_of_le hX (Nat.pow_le_pow_right (by norm_num) (by omega))
  have := Nat.mod_le (X / 2 ^ pos) (2 ^ w)
  norm_num at hY
  omega

/-- A digit step: digit `d` and carry `c'` of the window at `pos`. -/
private theorem digit_step {Y c c' w pos : ℕ} {d : ℤ}
    (hd : d + 2 ^ w * c' = ((c + Y % 2 ^ w : ℕ) : ℤ)) :
    (2 : ℤ) ^ pos * (c + Y : ℕ) = 2 ^ pos * d + 2 ^ (pos + w) * (c' + Y / 2 ^ w : ℕ) := by
  have hY := Nat.mod_add_div Y (2 ^ w)
  zify at hY
  push_cast at hd ⊢
  rw [pow_add]
  linear_combination (-(2 : ℤ) ^ pos) * hd - (2 : ℤ) ^ pos * hY

/-- The number of digits of width `w`: digit `k` starts below bit `256` iff `k < ⌈256 / w⌉`. -/
private theorem lt_digits_count {k w : ℕ} (hw : 1 ≤ w) :
    k < (256 + w - 1) / w ↔ k * w < 256 := by
  rw [← Nat.succ_le_iff, Nat.le_div_iff_mul_le (by omega), Nat.succ_mul]
  omega

/-- The invariant of the loop of `as_radix_2w` after `k` digits with carry `carry`: the digits so
far and the remaining value `carry + X / 2 ^ (w k)` make up `X`; the digits so far are in
`[-2 ^ (w - 1), 2 ^ (w - 1))`, the others zero; no carry once the window starts at bit `252`
(for `w ≥ 5`). -/
private def RadixInv (X w : ℕ) (digits : Array I8 64#usize) (k carry : ℕ) : Prop :=
  carry ≤ 1 ∧ (5 ≤ w → 252 + w ≤ w * k → carry = 0) ∧
  digits.asInt w + 2 ^ (w * k) * ((carry + X / 2 ^ (w * k) : ℕ) : ℤ) = X ∧
  (∀ j < k, -2 ^ w ≤ 2 * digits[j]!.val ∧ 2 * digits[j]!.val < 2 ^ w) ∧
  ∀ j, k ≤ j → j < 64 → digits[j]!.val = 0

/-- Appending digit `d` with carry `c'` keeps the invariant. -/
private theorem radix_inv_step {X w : ℕ} {digits : Array I8 64#usize} {k c c' : ℕ} {d : I8}
    (hk : k < 64) (hinv : RadixInv X w digits k c) (hc' : c' ≤ 1)
    (hc'0 : 5 ≤ w → 252 + w ≤ w * (k + 1) → c' = 0)
    (hd : d.val + 2 ^ w * (c' : ℤ) = ((c + X / 2 ^ (w * k) % 2 ^ w : ℕ) : ℤ))
    (hdb : -2 ^ w ≤ 2 * d.val ∧ 2 * d.val < 2 ^ w) (p : Usize) (hp : p.val = k) :
    RadixInv X w (digits.set p d) (k + 1) c' := by
  obtain ⟨-, -, hval, hlow, hzero⟩ := hinv
  refine ⟨hc', hc'0, ?_, fun j hj => ?_, fun j hj hj64 => ?_⟩
  · have hv := digit_step (pos := w * k) hd
    rw [Nat.div_div_eq_div_mul, ← Nat.pow_add, ← Nat.mul_succ] at hv
    rw [Array.asInt_set w digits p d (by simp [hp, hk]), hp, hzero k le_rfl hk, sub_zero, ← hval,
      hv, add_assoc]
  · by_cases hjk : j = k
    · rw [Array.getElem!_Nat_set_eq _ _ _ _ ⟨by rw [hp, hjk], by simp [hjk, hk]⟩]
      exact hdb
    · rw [Array.getElem!_Nat_set_ne _ _ _ _ (by rw [hp]; exact Ne.symm hjk)]
      exact hlow j (by omega)
  · rw [Array.getElem!_Nat_set_ne _ _ _ _ (by rw [hp]; exact Nat.ne_of_lt hj)]
    exact hzero j (Nat.le_of_succ_le hj) hj64

/-- The digit of the window `m` with incoming carry `carry`: in `[-2 ^ (w - 1), 2 ^ (w - 1))`, with
outgoing carry `c1 ≤ 1`, which is `0` for a window below `2 ^ (w - 1)`. -/
@[local step]
private theorem digit_spec (w : Usize) (radix carry m : U64) (hw : 4 ≤ w.val ∧ w.val ≤ 8)
    (hradix : radix.val = 2 ^ w.val) (hc : carry.val ≤ 1) (hm : m.val < 2 ^ w.val) :
    as_radix_2w_loop.body.digit w radix carry m ⦃ (c1 : U64) (d : I8) =>
      c1.val ≤ 1 ∧ d.val + 2 ^ w.val * (c1.val : ℤ) = ((carry.val + m.val : ℕ) : ℤ) ∧
      -2 ^ w.val ≤ 2 * d.val ∧ 2 * d.val < 2 ^ w.val ∧
      (carry.val + m.val < 2 ^ (w.val - 1) → c1.val = 0) ⦄ := by
  unfold as_radix_2w_loop.body.digit
  obtain ⟨P, hPdef⟩ : ∃ P, 2 ^ (w.val - 1) = P := ⟨_, rfl⟩
  have hP : 2 ^ w.val = 2 * P := by
    rw [← hPdef, ← pow_succ']
    congr 1
    scalar_tac
  have hP8 : 8 ≤ P ∧ P ≤ 128 := by
    rw [← hPdef]
    exact ⟨(by norm_num : 8 ≤ 2 ^ 3).trans (Nat.pow_le_pow_right (by norm_num) (by scalar_tac)),
      (Nat.pow_le_pow_right (by norm_num) (by scalar_tac : w.val - 1 ≤ 7)).trans (by norm_num)⟩
  step as ⟨coef, hcoef⟩
  have hcoef2 : coef.val ≤ 2 * P := by
    rw [← hP]
    scalar_tac
  step as ⟨h2, hh2⟩
  have hh2v : h2.val = P := by
    rw [hh2, hradix, hP]
    exact Nat.mul_div_cancel_left P (by norm_num)
  clear hh2
  step as ⟨i4, hi4⟩
  step as ⟨c1, hc1, hc1bv⟩
  rw [Nat.shiftRight_eq_div_pow, hi4, hh2v, hP] at hc1
  have hdig := radix_digit (by scalar_tac) hcoef2
  rw [← hc1] at hdig
  have hc1le : c1.val ≤ 1 := by rcases hdig with h | h <;> scalar_tac
  have hi6le : c1.val * (2 * P) ≤ 256 :=
    (Nat.mul_le_mul_right _ hc1le).trans (by scalar_tac)
  step with UScalar.hcast_inBounds_spec .I64 coef (by scalar_tac) as ⟨i5, hi5⟩
  step as ⟨i6, hi6, hi6bv⟩
  have hi6v : i6.val = c1.val * (2 * P) := by
    rw [hi6, Nat.shiftLeft_eq, hP]
    exact Nat.mod_eq_of_lt (by
      simp only [U64.size, U64.numBits, UScalarTy.U64_numBits_eq, Nat.reducePow]
      scalar_tac)
  step with UScalar.hcast_inBounds_spec .I64 i6 (by scalar_tac) as ⟨i7, hi7⟩
  step as ⟨i8, hi8⟩
  have hi8v : i8.val = (coef.val : ℤ) - c1.val * (2 * P) := by
    rw [hi8, hi5, hi7, hi6v]
    push_cast
    ring
  have hi8b : -(P : ℤ) ≤ i8.val ∧ i8.val < P := by
    rw [hi8v]
    rcases hdig with ⟨h0, hlt⟩ | ⟨h1, hge⟩
    · rw [h0]; constructor <;> push_cast <;> scalar_tac
    · rw [h1]; constructor <;> push_cast <;> scalar_tac
  step with IScalar.cast_inBounds_spec .I8 i8 (by scalar_tac) as ⟨i9, hi9⟩
  have hPz : (2 : ℤ) ^ w.val = 2 * (P : ℤ) := by exact_mod_cast hP
  refine ⟨hc1le, ?_, ?_, ?_, fun hlt => ?_⟩
  · rw [hi9, hi8v, hPz, ← hcoef]
    ring
  · rw [hi9, hPz]
    scalar_tac
  · rw [hi9, hPz]
    scalar_tac
  · rw [hPdef, ← hcoef] at hlt
    rcases hdig with ⟨h0, -⟩ | ⟨-, hge⟩
    · exact h0
    · exact absurd hge (Nat.not_le.mpr hlt)

/-- One step of the loop of `as_radix_2w`: digit `k` from the window at bit `w k`. -/
private theorem radix_body_spec (w : Usize) (x : Array U64 4#usize) (radix mask : U64) (X : ℕ)
    (hX : x.asNat 64 = X) (hX255 : X < 2 ^ 255) (hw : 4 ≤ w.val ∧ w.val ≤ 8)
    (hradix : radix.val = 2 ^ w.val) (hmask : mask.val = 2 ^ w.val - 1)
    (iter : core.ops.range.Range Usize) (carry : U64) (digits : Array I8 64#usize)
    (hlt : iter.start.val < iter.end.val) (hk : iter.start.val * w.val < 256)
    (hinv : RadixInv X w.val digits iter.start.val carry.val) :
    as_radix_2w_loop.body w x radix mask iter carry digits ⦃ r =>
      ∃ iter' carry' digits', r = .cont (iter', carry', digits') ∧
        iter'.start.val = iter.start.val + 1 ∧ iter'.end = iter.end ∧
        RadixInv X w.val digits' iter'.start.val carry'.val ⦄ := by
  have hc := hinv.1
  have hk64 : iter.start.val < 64 := by
    have := Nat.mul_le_mul_left iter.start.val hw.1
    scalar_tac
  rw [as_radix_2w_loop.body_eq]
  step with core.iter.range.IteratorRange.next_Usize_some_spec as ⟨o, iter1, ho, hstart1, hend1⟩
  subst ho
  step as ⟨bo, hbo⟩
  step as ⟨u, hu⟩
  step as ⟨b, hb⟩
  step as ⟨t, ht⟩
  step with radix_bit_buf_spec x X hX w u b t (by scalar_tac) (by scalar_tac) (by scalar_tac) ht
    iter1 as ⟨iter2, bb, hiter2, hbb⟩
  have hub : 64 * u.val + b.val = w.val * iter.start.val := by
    rw [hu, hb, Nat.div_add_mod, hbo, Nat.mul_comm]
  rw [hub] at hbb
  step with UScalar.and_two_pow_sub_one_spec bb mask w.val hmask as ⟨m, hm⟩
  rw [hbb] at hm
  have hmlt : m.val < 2 ^ w.val := by
    rw [hm]
    exact Nat.mod_lt _ (by positivity)
  step as ⟨c1, d, hc1, hd, hdl, hdu, hc10⟩
  step as ⟨digits1, hdigits1⟩
  refine ⟨iter2, c1, digits1, rfl, by rw [hiter2]; exact hstart1, by rw [hiter2]; exact hend1,
    ?_⟩
  rw [hdigits1, hiter2, hstart1]
  refine radix_inv_step hk64 hinv hc1 (fun h5 h252 => hc10 ?_) (by rw [hd, hm]) ⟨hdl, hdu⟩
    iter.start rfl
  have h252' : 252 ≤ w.val * iter.start.val := by
    rw [Nat.mul_succ] at h252
    scalar_tac
  have htop := radix_top_window (w := w.val) (pos := w.val * iter.start.val) hX255 h252' hc
  have hP16 : 16 ≤ 2 ^ (w.val - 1) :=
    (by norm_num : 16 ≤ 2 ^ 4).trans (Nat.pow_le_pow_right (by norm_num) (by scalar_tac))
  rw [hm]
  scalar_tac

/-- The invariant holds initially. -/
private theorem radix_inv_init (X w : ℕ) : RadixInv X w (Array.repeat 64#usize 0#i8) 0 0 := by
  unfold RadixInv
  refine ⟨Nat.zero_le _, fun _ h => absurd h (by omega), ?_, fun j hj => absurd hj (by omega),
    fun j _ hj => ?_⟩
  · rw [Array.asInt_repeat_zero w _ (by simp)]
    simp
  · rw [Array.getElem!_repeat _ (by simpa using hj)]
    rfl

/-- The loop of `as_radix_2w` computes the `⌈256 / w⌉` digits. -/
private theorem radix_loop_spec (w : Usize) (x : Array U64 4#usize) (radix mask : U64) (X : ℕ)
    (hX : x.asNat 64 = X) (hX255 : X < 2 ^ 255) (hw : 4 ≤ w.val ∧ w.val ≤ 8)
    (hradix : radix.val = 2 ^ w.val) (hmask : mask.val = 2 ^ w.val - 1) (dc : Usize)
    (hdc : dc.val = (256 + w.val - 1) / w.val) :
    as_radix_2w_loop { start := 0#usize, «end» := dc } w x radix mask 0#u64
      (Array.repeat 64#usize 0#i8) ⦃ (carry : U64) (digits : Array I8 64#usize) =>
      RadixInv X w.val digits dc.val carry.val ⦄ := by
  unfold as_radix_2w_loop
  apply loop.spec_decr_nat (measure := fun (iter, _, _) => dc.val - iter.start.val)
    (inv := fun (iter, carry, digits) => iter.end = dc ∧ iter.start.val ≤ dc.val ∧
      RadixInv X w.val digits iter.start.val carry.val)
  · rintro ⟨iter, carry, digits⟩ ⟨hend, hstart, hinv⟩
    by_cases hlt : iter.start.val < dc.val
    · have hk : iter.start.val * w.val < 256 := by
        rw [hdc] at hlt
        exact (lt_digits_count (by scalar_tac)).mp hlt
      apply spec_mono (radix_body_spec w x radix mask X hX hX255 hw hradix hmask iter carry digits
        (by rw [hend]; exact hlt) hk hinv)
      rintro r ⟨iter', carry', digits', rfl, hstart', hend', hinv'⟩
      refine ⟨⟨hend'.trans hend, by rw [hstart']; exact hlt, hinv'⟩, ?_⟩
      dsimp only
      rw [hstart']
      exact Nat.sub_lt_sub_left hlt (Nat.lt_succ_self _)
    · unfold as_radix_2w_loop.body
      step*
  · exact ⟨rfl, Nat.zero_le _, radix_inv_init X w.val⟩

/-- The number of digits `⌈256 / w⌉` for `4 ≤ w ≤ 8`. -/
private theorem digits_count_facts {w : ℕ} (hw : 4 ≤ w ∧ w ≤ 8) :
    256 ≤ w * ((256 + w - 1) / w) ∧ (256 + w - 1) / w ≤ 64 ∧
    (w = 8 → (256 + w - 1) / w = 32) ∧
    (5 ≤ w → w < 8 → 252 + w ≤ w * ((256 + w - 1) / w)) := by
  obtain ⟨h1, h2⟩ := hw
  interval_cases w <;> decide

/-- The final carry for `w = 8` goes into digit `32`. -/
private theorem radix_tail8_spec (w : Usize) (X : ℕ) (hX255 : X < 2 ^ 255) (hw8 : w.val = 8)
    (dc : Usize) (hdc : dc.val = 32) (carry : U64) (digits : Array I8 64#usize)
    (hinv : RadixInv X w.val digits dc.val carry.val) :
    (do
      let i ← lift (UScalar.hcast IScalarTy.I8 carry)
      let i1 ← digits.index_usize dc
      let i2 ← i1 + i
      digits.update dc i2) ⦃ (r : Array I8 64#usize) =>
      r.asInt w.val = X ∧
      (∀ i < 64, (i + 1) * w.val < 256 →
        -2 ^ w.val ≤ 2 * r[i]!.val ∧ 2 * r[i]!.val < 2 ^ w.val) ∧
      (∀ i < 64, -2 ^ w.val ≤ 2 * r[i]!.val ∧ 2 * r[i]!.val ≤ 2 ^ w.val) ∧
      ∀ i < 64, 256 < i * w.val → r[i]!.val = 0 ⦄ := by
  obtain ⟨hc, -, hval, hlow, hzero⟩ := hinv
  rw [hw8] at hval hlow ⊢
  rw [hdc] at hval hlow hzero
  step with UScalar.hcast_inBounds_spec .I8 carry (by scalar_tac) as ⟨i, hi⟩
  step with Array.index_usize_getElem!_spec as ⟨i1, hi1⟩
  have hi1z : i1.val = 0 := by rw [hi1, hdc]; exact hzero 32 le_rfl (by norm_num)
  step as ⟨i2, hi2⟩
  step as ⟨r, hr⟩
  have hq : X / 2 ^ (8 * 32) = 0 := Nat.div_eq_of_lt (lt_of_lt_of_le hX255 (by norm_num))
  have hr32 : r[32]!.val = carry.val := by
    rw [hr, Array.getElem!_Nat_set_eq _ _ _ _ ⟨hdc, by simp⟩, hi2, hi1z, hi]
    simp
  have hrj (j : ℕ) (hj : j ≠ 32) : r[j]! = digits[j]! := by
    rw [hr, Array.getElem!_Nat_set_ne _ _ _ _ (by rw [hdc]; exact Ne.symm hj)]
  refine ⟨?_, fun j hj h => ?_, fun j hj => ?_, fun j hj h => ?_⟩
  · rw [hr, Array.asInt_set 8 digits dc i2 (by scalar_tac), hdc, hi2, ← hval, hq]
    rw [hdc] at hi1
    rw [← hi1, hi1z, hi]
    push_cast
    ring
  · rw [hrj j (by scalar_tac)]
    exact hlow j (by scalar_tac)
  · by_cases hj32 : j = 32
    · rw [hj32, hr32]
      scalar_tac
    · rw [hrj j hj32]
      by_cases hjlt : j < 32
      · have := hlow j hjlt
        scalar_tac
      · rw [hzero j (by scalar_tac) hj]
        norm_num
  · rw [hrj j (by scalar_tac)]
    exact hzero j (by scalar_tac) hj

/-- For `w < 8` the final carry is zero: the last digit is unchanged. -/
private theorem radix_tail_spec (w : Usize) (X : ℕ) (hX255 : X < 2 ^ 255)
    (hw : 5 ≤ w.val ∧ w.val < 8) (dc : Usize) (hdc : dc.val = (256 + w.val - 1) / w.val)
    (carry : U64) (digits : Array I8 64#usize) (hinv : RadixInv X w.val digits dc.val carry.val) :
    (do
      let i ← carry <<< w
      let i1 ← lift (UScalar.hcast IScalarTy.I8 i)
      let i2 ← dc - 1#usize
      let i3 ← digits.index_usize i2
      let i4 ← i3 + i1
      digits.update i2 i4) ⦃ (r : Array I8 64#usize) =>
      r.asInt w.val = X ∧
      (∀ i < 64, (i + 1) * w.val < 256 →
        -2 ^ w.val ≤ 2 * r[i]!.val ∧ 2 * r[i]!.val < 2 ^ w.val) ∧
      (∀ i < 64, -2 ^ w.val ≤ 2 * r[i]!.val ∧ 2 * r[i]!.val ≤ 2 ^ w.val) ∧
      ∀ i < 64, 256 < i * w.val → r[i]!.val = 0 ⦄ := by
  obtain ⟨h256, h64, -, h252⟩ :=
    digits_count_facts (w := w.val) ⟨by scalar_tac, by scalar_tac⟩
  rw [← hdc] at h256 h64 h252
  obtain ⟨-, hc0, hval, hlow, hzero⟩ := hinv
  have hc : carry.val = 0 := hc0 hw.1 (h252 hw.1 hw.2)
  have hq : X / 2 ^ (w.val * dc.val) = 0 := Nat.div_eq_of_lt (lt_of_lt_of_le hX255
    (Nat.pow_le_pow_right (by norm_num) (le_trans (by norm_num) h256)))
  rw [hc, hq, Nat.add_zero, Nat.cast_zero, mul_zero, add_zero] at hval
  have hlt (j : ℕ) : j < dc.val ↔ j * w.val < 256 := by
    rw [hdc]
    exact lt_digits_count (by scalar_tac)
  clear hdc
  have hdc1 : 1 ≤ dc.val := by
    rcases Nat.eq_zero_or_pos dc.val with h | h
    · rw [h] at h256; scalar_tac
    · exact h
  step as ⟨i, hi, hibv⟩
  have hi0 : i.val = 0 := by rw [hi, hc]; simp
  clear hi hibv hq
  step with UScalar.hcast_inBounds_spec .I8 i (by rw [hi0]; scalar_tac) as ⟨i1, hi1⟩
  rw [hi0] at hi1
  step as ⟨k, hk⟩
  step with Array.index_usize_getElem!_spec as ⟨i3, hi3⟩
  step as ⟨i4, hi4⟩
  step as ⟨r, hr⟩
  have hi4v : i4.val = digits[k.val]!.val := by rw [hi4, hi1, hi3]; simp
  clear hi4 hi3 hi1
  have hk64 : k.val < 64 := by scalar_tac
  have hrj (j : ℕ) : r[j]!.val = digits[j]!.val := by
    rw [hr]
    by_cases hjk : j = k.val
    · rw [Array.getElem!_Nat_set_eq _ _ _ _ ⟨hjk.symm, by simp [hjk, hk64]⟩, hi4v, hjk]
    · rw [Array.getElem!_Nat_set_ne _ _ _ _ (Ne.symm hjk)]
  refine ⟨?_, fun j hj h => ?_, fun j hj => ?_, fun j hj h => ?_⟩
  · rw [hr, Array.asInt_set w.val digits k i4 (by simp [hk64]), hi4v, sub_self, mul_zero,
      add_zero, hval]
  · rw [hrj]
    exact hlow j ((hlt j).mpr (by rw [Nat.succ_mul] at h; scalar_tac))
  · rw [hrj]
    by_cases hj' : j < dc.val
    · have := hlow j hj'
      scalar_tac
    · rw [hzero j (by scalar_tac) hj, mul_zero]
      exact ⟨neg_nonpos.mpr (by positivity), by positivity⟩
  · rw [hrj]
    exact hzero j (by have := (hlt j).not.mpr (by scalar_tac); scalar_tac) hj

@[step]
theorem as_radix_2w_spec (self : Scalar) (w : Usize) (hw : 4 ≤ w.val ∧ w.val ≤ 8)
    (hself : self.asNat < 2 ^ 255) :
    as_radix_2w self w ⦃ (r : Array I8 64#usize) =>
      r.asInt w.val = self.asNat ∧
      (∀ i < 64, (i + 1) * w.val < 256 → -2 ^ w.val ≤ 2 * r[i]!.val ∧ 2 * r[i]!.val < 2 ^ w.val) ∧
      (∀ i < 64, -2 ^ w.val ≤ 2 * r[i]!.val ∧ 2 * r[i]!.val ≤ 2 ^ w.val) ∧
      ∀ i < 64, 256 < i * w.val → r[i]!.val = 0 ⦄ := by
  unfold as_radix_2w
  step
  step
  split_ifs with hw4
  · have hw4v : w.val = 4 := by rw [hw4]; rfl
    have hb31 : self.bytes[31]!.val ≤ 127 := by
      have hsplit : self.asNat = ∑ j ∈ Finset.range 31, 2 ^ (8 * j) * self.bytes[j]!.val
          + 2 ^ (8 * 31) * self.bytes[31]!.val := by
        rw [Scalar.asNat, Array.asNat_eq_sum, show (32#usize).val = 31 + 1 from rfl,
          Finset.sum_range_succ]
      rw [hsplit] at hself
      scalar_tac
    step with as_radix_16_spec self hb31 as ⟨r, hval, hlow, h63l, h63u⟩
    rw [hw4v]
    refine ⟨hval, fun i hi h => ?_, fun i hi => ?_, fun i hi h => ?_⟩
    · have := hlow i (by scalar_tac)
      scalar_tac
    · by_cases hi63 : i < 63
      · have := hlow i hi63
        scalar_tac
      · have hi63' : i = 63 := by scalar_tac
        rw [hi63']
        scalar_tac
    · scalar_tac
  · step as ⟨s, hs⟩
    step as ⟨s1, back, hs1, hs1len, hback⟩
    step as ⟨s2, hs2len, hs2⟩
    step as ⟨radix, hrv, hrbv⟩
    have hradix : radix.val = 2 ^ w.val := by
      rw [hrv, Nat.shiftLeft_eq, Nat.one_mul]
      exact Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.pow_le_pow_right (by norm_num) hw.2)
        (by simp [U64.size, U64.numBits]))
    have h1r : (1#u64).val ≤ radix.val := by
      rw [hradix]
      exact Nat.one_le_two_pow
    step as ⟨mask, hmask⟩
    step as ⟨dc, hdc⟩
    have hs1l : s1.length = 4 := by simpa using hs1len
    have hlimb (i : ℕ) (hi : i < 4) : (back s2)[i]! = s2[i]! := by
      have hlen : i < (Array.repeat 4#usize 0#u64).val.length := by
        simp only [Array.repeat_val, List.length_replicate]
        scalar_tac
      rw [Array.getElem!_Nat_eq, hback, List.getElem!_setSlice!_middle _ _ _ _
        ⟨Nat.zero_le _, by simp [hs2len, hs1l, hi], hlen⟩, Nat.sub_zero, Slice.getElem!_Nat_eq]
    have hXeq : (back s2).asNat 64 = self.asNat :=
      Array.asNat_limbs_eq 8 4 (back s2) self.bytes (by simp) (by simp)
        (fun i _ => by simpa using ((back s2)[i]!).hBounds)
        (fun i hi j hj => by
          rw [hlimb i hi, hs2 i (by rw [hs1l]; exact hi) j hj, hs, Slice.getElem!_Nat_eq,
            Array.getElem!_Nat_eq, Array.val_to_slice])
        (fun i hi hi4 => absurd hi4 (by scalar_tac))
    step with radix_loop_spec w (back s2) radix mask self.asNat hXeq hself hw hradix
      (by rw [hmask, hradix]) dc hdc as ⟨carry, digits, hinv⟩
    obtain ⟨-, -, hdc8, -⟩ := digits_count_facts (w := w.val) hw
    rw [← hdc] at hdc8
    split
    next _ hw8 => exact radix_tail8_spec w _ hself hw8 dc (hdc8 hw8) carry digits hinv
    next _ hw8 =>
      exact radix_tail_spec w _ hself ⟨by scalar_tac, by scalar_tac⟩ dc hdc carry digits hinv

end curve25519_dalek.scalar.Scalar
