module
public import Curve25519
public import Curve25519Dalek.Funs
public import Specs.Defs
public import Specs.Backend.Serial.U64.Defs
public import Subtle
public import Specs.Lemmas.AsInt
public import Specs.Lemmas.AsNat
public import Specs.Scalar.Index
public import Specs.Lemmas.Array
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open curve25519_dalek.scalar (Scalar HalfWidthScalar)
open curve25519_dalek.backend.serial.u64.scalar (montgomeryRadix)

namespace curve25519_dalek.scalar.Scalar.as_radix_16

@[step]
theorem bot_half_spec (x : U8) :
    bot_half x ⦃ (r : U8) =>
      r.val = x.val % 16 ⦄ := by
  unfold bot_half
  step as ⟨i, hi, hibv⟩
  simp only [UScalar.val_and, hi]
  exact Nat.and_two_pow_sub_one_eq_mod _ 4

end curve25519_dalek.scalar.Scalar.as_radix_16

namespace curve25519_dalek.scalar.Scalar.as_radix_16

@[step]
theorem top_half_spec (x : U8) :
    top_half x ⦃ (r : U8) =>
      16 * r.val + x.val % 16 = x.val ⦄ := by
  unfold top_half
  step as ⟨i, hi, hibv⟩
  simp only [UScalar.val_and, hi]
  rw [show (15#u8).val = 2 ^ 4 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
    Nat.shiftRight_eq_div_pow]
  scalar_tac

end curve25519_dalek.scalar.Scalar.as_radix_16

namespace curve25519_dalek.scalar.Scalar

/-- The first loop of `as_radix_16` splits each byte into its two nibbles. -/
@[local step]
private theorem as_radix_16_loop0_spec (self : Scalar) :
    as_radix_16_loop0 { start := 0#usize, «end» := 32#usize } self (Array.repeat 64#usize 0#i8)
    ⦃ (r : Array I8 64#usize) => ∀ i < 32,
      r[2 * i]!.val = ((self.bytes[i]!.val % 16 : ℕ) : ℤ) ∧
      r[2 * i + 1]!.val = ((self.bytes[i]!.val / 16 : ℕ) : ℤ) ⦄ := by
  unfold as_radix_16_loop0
  apply loop.spec_decr_nat (measure := fun (iter, _) => 32 - iter.start.val)
    (inv := fun (iter, out) => iter.end = 32#usize ∧ iter.start.val ≤ 32 ∧
      ∀ i < iter.start.val, out[2 * i]!.val = ((self.bytes[i]!.val % 16 : ℕ) : ℤ) ∧
        out[2 * i + 1]!.val = ((self.bytes[i]!.val / 16 : ℕ) : ℤ))
  · rintro ⟨iter, out⟩ ⟨hend, hstart, hdone⟩
    unfold as_radix_16_loop0.body
    by_cases hlt : iter.start.val < 32
    · step with core.iter.range.IteratorRange.next_Usize_some_spec
        as ⟨o, iter1, ho, hstart1, hend1⟩
      subst ho
      step as ⟨x, hx⟩
      step as ⟨lo, hlo⟩
      step as ⟨k2, hk2⟩
      step with UScalar.hcast_inBounds_spec as ⟨lo8, hlo8⟩
      step as ⟨out1, hout1⟩
      step as ⟨top, htop⟩
      step as ⟨k3, hk3⟩
      step with UScalar.hcast_inBounds_spec as ⟨hi8, hhi8⟩
      step as ⟨out2, hout2⟩
      refine ⟨by scalar_tac, by scalar_tac, fun i hi => ?_, by scalar_tac⟩
      rw [hout2, hout1]
      by_cases his : i = iter.start.val
      · rw [Array.getElem!_Nat_set_ne _ _ _ _ (by scalar_tac),
          Array.getElem!_Nat_set_eq _ _ _ _ ⟨by scalar_tac, by scalar_tac⟩,
          Array.getElem!_Nat_set_eq _ _ _ _ ⟨by scalar_tac, by scalar_tac⟩, hlo8, hhi8, hlo,
          his,
          ← hx]
        refine ⟨rfl, ?_⟩
        have hdiv : top.val = x.val / 16 := by scalar_tac
        rw [hdiv]
      · rw [Array.getElem!_Nat_set_ne _ _ _ _ (by scalar_tac),
          Array.getElem!_Nat_set_ne _ _ _ _ (by scalar_tac),
          Array.getElem!_Nat_set_ne _ _ _ _ (by scalar_tac),
          Array.getElem!_Nat_set_ne _ _ _ _ (by scalar_tac)]
        exact hdone i (by scalar_tac)
    · step*
  · simp

/-- The carry of one recentring step. -/
private theorem carry_arith {d d8 c : ℤ} (hd : 0 ≤ d ∧ d ≤ 16) (hd8 : d8 = d + 8)
    (hc : c = d8 / 2 ^ 4) : (c = 0 ∨ c = 1) ∧ -8 ≤ d - 16 * c ∧ d - 16 * c < 8 := by
  subst hd8 hc
  omega

/-- A digit `0 … 15`, possibly increased by a carry. -/
private theorem digit_succ_bound {x y : ℤ} (h : x = y ∨ x = y + 1) (hy : 0 ≤ y ∧ y ≤ 15) :
    0 ≤ x ∧ x ≤ 16 := by
  omega

/-- One step of the second loop of `as_radix_16`: digit `i` is recentred and its carry added to
digit `i + 1`. -/
private theorem as_radix_16_loop1_body_spec (iter : core.ops.range.Range Usize)
    (cur : Array I8 64#usize) (hlt : iter.start.val < 63) (hend : iter.end = 63#usize)
    (hd : 0 ≤ cur[iter.start.val]!.val ∧ cur[iter.start.val]!.val ≤ 16)
    (hn : 0 ≤ cur[iter.start.val + 1]!.val ∧ cur[iter.start.val + 1]!.val ≤ 15) :
    as_radix_16_loop1.body iter cur ⦃ r => ∃ iter1 cur2, r = .cont (iter1, cur2) ∧
      iter1.start.val = iter.start.val + 1 ∧ iter1.end = iter.end ∧
      cur2.asInt 4 = cur.asInt 4 ∧
      (-8 ≤ cur2[iter.start.val]!.val ∧ cur2[iter.start.val]!.val < 8) ∧
      (cur2[iter.start.val + 1]!.val = cur[iter.start.val + 1]!.val ∨
        cur2[iter.start.val + 1]!.val = cur[iter.start.val + 1]!.val + 1) ∧
      ∀ j, j ≠ iter.start.val → j ≠ iter.start.val + 1 → cur2[j]! = cur[j]! ⦄ := by
  unfold as_radix_16_loop1.body
  step with core.iter.range.IteratorRange.next_Usize_some_spec as ⟨o, iter1, ho, hstart1, hend1⟩
  subst ho
  step with Array.index_usize_getElem!_spec as ⟨d, hdv⟩
  rw [← hdv] at hd
  step as ⟨d8, hd8⟩
  step as ⟨c, hc, hcbv⟩
  rw [Int.shiftRight_eq_div_pow] at hc
  have hcb := carry_arith hd hd8 (by simpa using hc)
  step as ⟨c16, hc16, hc16bv⟩
  have hc16v : c16.val = 16 * c.val := by
    rw [hc16, Int.shiftLeft_eq]
    rcases hcb.1 with h | h <;> rw [h] <;> norm_num [I8.size, I8.numBits, Int.bmod]
  step as ⟨e, he⟩
  step as ⟨cur1, hcur1⟩
  step as ⟨k1, hk1⟩
  step with Array.index_usize_getElem!_spec as ⟨n, hnv⟩
  have hn1eq : n = cur[iter.start.val + 1]! := by
    rw [hnv, hcur1, hk1, Array.getElem!_Nat_set_ne _ _ _ _ (by simp)]
  rw [← hn1eq] at hn
  step as ⟨n1, hn1⟩
  step as ⟨cur2, hcur2⟩
  refine ⟨iter1, cur2, rfl, hstart1, hend1, ?_, ?_, ?_, ?_, fun j hj hj1 => ?_⟩
  · have h1 := Array.asInt_set 4 cur iter.start e (by scalar_tac)
    have h2 := Array.asInt_set 4 cur1 k1 n1 (by scalar_tac)
    rw [← hcur1] at h1
    rw [← hcur2, ← hnv, h1, hn1, he, hc16v, ← hdv, hk1, Nat.mul_succ, pow_add] at h2
    rw [h2]
    ring
  · rw [hcur2, Array.getElem!_Nat_set_ne _ _ _ _ (by simp [hk1]), hcur1,
      Array.getElem!_Nat_set_eq _ _ _ _ ⟨rfl, by scalar_tac⟩, he, hc16v]
    exact hcb.2.1
  · rw [hcur2, Array.getElem!_Nat_set_ne _ _ _ _ (by simp [hk1]), hcur1,
      Array.getElem!_Nat_set_eq _ _ _ _ ⟨rfl, by scalar_tac⟩, he, hc16v]
    exact hcb.2.2
  · rw [hcur2, Array.getElem!_Nat_set_eq _ _ _ _ ⟨hk1, by scalar_tac⟩, hn1, ← hn1eq]
    rcases hcb.1 with h | h <;> rw [h] <;> simp
  · rw [hcur2, Array.getElem!_Nat_set_ne _ _ _ _ (by rw [hk1]; exact Ne.symm hj1), hcur1,
      Array.getElem!_Nat_set_ne _ _ _ _ (Ne.symm hj)]

/-- The second loop of `as_radix_16` recentres the digits `0 … 15` into `-8 … 7`, carrying into
the next digit. -/
@[local step]
private theorem as_radix_16_loop1_spec (out : Array I8 64#usize)
    (hout : ∀ j < 64, 0 ≤ out[j]!.val ∧ out[j]!.val ≤ 15) (h63 : out[63]!.val ≤ 7) :
    as_radix_16_loop1 { start := 0#usize, «end» := 63#usize } out ⦃ (r : Array I8 64#usize) =>
      r.asInt 4 = out.asInt 4 ∧ (∀ i < 63, -8 ≤ r[i]!.val ∧ r[i]!.val < 8) ∧
      -8 ≤ r[63]!.val ∧ r[63]!.val ≤ 8 ⦄ := by
  unfold as_radix_16_loop1
  apply loop.spec_decr_nat (measure := fun (iter, _) => 63 - iter.start.val)
    (inv := fun (iter, cur) => iter.end = 63#usize ∧ iter.start.val ≤ 63 ∧
      cur.asInt 4 = out.asInt 4 ∧
      (∀ j < iter.start.val, -8 ≤ cur[j]!.val ∧ cur[j]!.val < 8) ∧
      (cur[iter.start.val]!.val = out[iter.start.val]!.val ∨
        cur[iter.start.val]!.val = out[iter.start.val]!.val + 1) ∧
      ∀ j, iter.start.val < j → j < 64 → cur[j]! = out[j]!)
  · rintro ⟨iter, cur⟩ ⟨hend, hstart, hval, hlow, hcur, hhigh⟩
    by_cases hlt : iter.start.val < 63
    · have hs1 : iter.start.val + 1 < 64 := Nat.succ_lt_succ hlt
      have hos := hout iter.start.val (Nat.lt_of_succ_lt hs1)
      have hcur1 := hhigh (iter.start.val + 1) (Nat.lt_succ_self _) hs1
      have hos1 := hout (iter.start.val + 1) hs1
      rw [← hcur1] at hos1
      apply spec_mono (as_radix_16_loop1_body_spec iter cur hlt hend (digit_succ_bound hcur hos)
        hos1)
      rintro r ⟨iter1, cur2, rfl, hstart1, hend1, hval2, hb, hnext, hrest⟩
      refine ⟨⟨hend1.trans hend, hstart1 ▸ hlt, hval2.trans hval, fun j hj => ?_, ?_,
        fun j hj hj64 => ?_⟩, ?_⟩
      · rw [hstart1] at hj
        by_cases hjs : j = iter.start.val
        · rw [hjs]
          exact hb
        · rw [hrest j hjs (Nat.ne_of_lt hj)]
          exact hlow j (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hj) hjs)
      · rw [hstart1, ← hcur1]
        exact hnext
      · rw [hstart1] at hj
        rw [hrest j (Nat.ne_of_gt (Nat.lt_of_succ_lt hj)) (Nat.ne_of_gt hj)]
        exact hhigh j (Nat.lt_of_succ_lt hj) hj64
      · dsimp only
        rw [hstart1]
        exact Nat.sub_lt_sub_left hlt (Nat.lt_succ_self _)
    · unfold as_radix_16_loop1.body
      step*
      have hs : iter.start.val = 63 := by scalar_tac
      have h63' := hout 63 (by norm_num)
      rw [hs] at hcur
      refine ⟨hval, fun i hi => hlow i (by scalar_tac), by scalar_tac, by scalar_tac⟩
  · simp

@[step]
theorem as_radix_16_spec (self : Scalar) (hself : self.bytes[31]!.val ≤ 127) :
    as_radix_16 self ⦃ (r : Array I8 64#usize) =>
      r.asInt 4 = self.asNat ∧
      (∀ i < 63, -8 ≤ r[i]!.val ∧ r[i]!.val < 8) ∧ -8 ≤ r[63]!.val ∧ r[63]!.val ≤ 8 ⦄ := by
  unfold as_radix_16
  step as ⟨b31, hb31⟩
  step
  step as ⟨out, hout⟩
  have hbounds : ∀ j < 64, 0 ≤ out[j]!.val ∧ out[j]!.val ≤ 15 := by
    intro j hj
    rcases Nat.even_or_odd' j with ⟨i, rfl | rfl⟩
    · have hb : self.bytes[i]!.val < 256 := (self.bytes[i]!).hBounds
      rw [(hout i (by scalar_tac)).1]
      scalar_tac
    · have hb : self.bytes[i]!.val < 256 := (self.bytes[i]!).hBounds
      rw [(hout i (by scalar_tac)).2]
      scalar_tac
  have h63 : out[63]!.val ≤ 7 := by
    rw [(hout 31 (by norm_num)).2]
    scalar_tac
  step as ⟨r, hval, hlow, h63l, h63u⟩
  refine ⟨?_, hlow, h63l, h63u⟩
  rw [hval, Scalar.asNat]
  exact Array.asInt_eq_asNat_of_pairs 4 out self.bytes (by simp) fun i hi => by
    rw [(hout i (by simpa using hi)).1, (hout i (by simpa using hi)).2]
    scalar_tac

end curve25519_dalek.scalar.Scalar
