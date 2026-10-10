module
public import Curve25519
public import Curve25519Dalek.Funs
public import Specs.Backend.Serial.U64.Defs
public import Subtle
public import Specs.Field.Invert
public import Specs.Field.IsZero
public import Specs.Backend.Serial.U64.Field.One
public import Specs.Backend.Serial.U64.Field.Mul
public import Specs.Backend.Serial.U64.Field.ConditionalAssign
public import Specs.Lemmas.ZMod
public import Specs.Field.Lemmas
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)

namespace Curve25519Dalek.field.FieldElement51

/-! ## Prefix products of the nonzero inputs, in `ZMod p` -/

/-- The factor of input `k` in the running product: the input, or `1` if it is zero. -/
private def fac (inputs : Slice FieldElement51) (k : ℕ) : ZMod p :=
  if (inputs[k]!.asNat : ZMod p) = 0 then 1 else (inputs[k]!.asNat : ZMod p)

/-- The product of the nonzero inputs before index `i`. -/
private def pre (inputs : Slice FieldElement51) (i : ℕ) : ZMod p :=
  ∏ k ∈ Finset.range i, fac inputs k

private theorem fac_ne_zero (inputs : Slice FieldElement51) (k : ℕ) : fac inputs k ≠ 0 := by
  unfold fac
  split_ifs with h
  · exact one_ne_zero
  · exact h

private theorem pre_ne_zero (inputs : Slice FieldElement51) (i : ℕ) : pre inputs i ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun k _ => fac_ne_zero inputs k

private theorem pre_succ (inputs : Slice FieldElement51) (i : ℕ) :
    pre inputs (i + 1) = pre inputs i * fac inputs i :=
  Finset.prod_range_succ _ i

private theorem not_one : (1#u8 &&& ~~~(1#u8 : subtle.Choice)) = 0#u8 := by decide

private theorem not_zero : (1#u8 &&& ~~~(0#u8 : subtle.Choice)) = 1#u8 := by decide

/-! ## First loop: prefix products into `scratch` -/

@[local step]
private theorem internal_invert_batch_loop0_spec (inputs scratch : Slice FieldElement51)
    (acc : FieldElement51) (n i : Usize) (hn : n.val = inputs.length)
    (hlen : scratch.length = inputs.length) (hi : i.val ≤ n.val)
    (hinputs : ∀ k < inputs.length, ∀ j < 5, (inputs[k]!)[j]!.val < 2 ^ 54)
    (hacc : (acc.asNat : ZMod p) = pre inputs i.val) (haccb : ∀ j < 5, acc[j]!.val < 2 ^ 54)
    (hscratch : ∀ k < i.val, (scratch[k]!.asNat : ZMod p) = pre inputs k ∧
      ∀ j < 5, (scratch[k]!)[j]!.val < 2 ^ 54) :
    internal_invert_batch_loop0 inputs scratch acc n i ⦃ (s : Slice FieldElement51)
      (a : FieldElement51) =>
      s.length = inputs.length ∧ (a.asNat : ZMod p) = pre inputs inputs.length ∧
      (∀ j < 5, a[j]!.val < 2 ^ 54) ∧
      ∀ k < inputs.length, (s[k]!.asNat : ZMod p) = pre inputs k ∧
        ∀ j < 5, (s[k]!)[j]!.val < 2 ^ 54 ⦄ := by
  unfold internal_invert_batch_loop0
  apply loop.spec_decr_nat (measure := fun x => n.val - x.2.2.val)
    (inv := fun x => x.2.2.val ≤ n.val ∧ x.1.length = inputs.length ∧
      (x.2.1.asNat : ZMod p) = pre inputs x.2.2.val ∧ (∀ j < 5, x.2.1[j]!.val < 2 ^ 54) ∧
      ∀ k < x.2.2.val, (x.1[k]!.asNat : ZMod p) = pre inputs k ∧
        ∀ j < 5, (x.1[k]!)[j]!.val < 2 ^ 54)
  · rintro ⟨s, a, i'⟩ ⟨hi', hsl, ha, hab, hs⟩
    simp only at hi' hsl ha hab hs
    unfold internal_invert_batch_loop0.body
    by_cases hlt : i' < n
    · simp only [hlt, if_true]
      have hlt' : i'.val < inputs.length := by scalar_tac
      step as ⟨s1, hs1⟩
      step as ⟨fe, hfe⟩
      have hfe' : fe = inputs[i'.val]! := by
        rw [hfe, Slice.getElem!_Nat_eq, getElem!_pos]
      have hfeb : ∀ j < 5, fe[j]!.val < 2 ^ 54 := hfe' ▸ hinputs i'.val hlt'
      step as ⟨fe1, hfe1, hfe1b⟩
      step as ⟨c, _, hc1, hc0⟩
      step as ⟨c1, _, hc1'⟩
      step as ⟨acc1, ha0, ha1⟩
      step as ⟨i1, hi1⟩
      have hacc1 : (acc1.asNat : ZMod p) = pre inputs i1.val ∧
          ∀ j < 5, acc1[j]!.val < 2 ^ 54 := by
        rw [hi1, pre_succ, ← ha, fac, ← hfe']
        by_cases hz : (fe.asNat : ZMod p) = 0
        · rw [hc1 (ZMod.natCast_eq_zero_iff_mod.mp hz), not_one] at hc1'
          rw [ha0 hc1', if_pos hz, mul_one]
          exact ⟨rfl, hab⟩
        · rw [hc0 (fun h => hz (ZMod.natCast_eq_zero_iff_mod.mpr h)), not_zero] at hc1'
          rw [ha1 hc1', if_neg hz, ← Nat.cast_mul, ZMod.natCast_eq_natCast_iff']
          exact ⟨hfe1, fun j hj => lt_trans (hfe1b j hj) (by norm_num)⟩
      refine ⟨by scalar_tac, by rw [hs1, Slice.set_length, hsl], hacc1.1, hacc1.2,
        fun k hk => ?_, by scalar_tac⟩
      rw [hs1]
      by_cases hki : k = i'.val
      · rw [Slice.getElem!_Nat_set_eq _ _ _ _ ⟨hki.symm, by scalar_tac⟩, hki]
        exact ⟨ha, hab⟩
      · rw [Slice.getElem!_Nat_set_ne _ _ _ _ (Ne.symm hki)]
        exact hs k (by scalar_tac)
    · simp only [hlt, if_false, WP.spec_ok]
      have hin : i'.val = inputs.length := by scalar_tac
      rw [hin] at ha hs
      exact ⟨hsl, ha, hab, hs⟩
  · exact ⟨hi, hlen, hacc, haccb, hscratch⟩

/-! ## Second loop: the inverses, from the back -/

/-- What the batch inversion leaves at index `j`, given the original `inputs`. -/
private def Done (inputs r : Slice FieldElement51) (j : ℕ) : Prop :=
  ((inputs[j]!.asNat : ZMod p) = 0 → r[j]! = inputs[j]!) ∧
  ((inputs[j]!.asNat : ZMod p) ≠ 0 → (r[j]!.asNat : ZMod p) * inputs[j]!.asNat = 1 ∧
    ∀ i < 5, (r[j]!)[i]!.val < 2 ^ 52)

@[local step]
private theorem internal_invert_batch_loop1_spec (inputs0 inputs scratch : Slice FieldElement51)
    (acc : FieldElement51) (k : Usize) (hk : k.val ≤ inputs0.length)
    (hlen : inputs.length = inputs0.length)
    (hinputs : ∀ k < inputs0.length, ∀ j < 5, (inputs0[k]!)[j]!.val < 2 ^ 54)
    (hscratch : ∀ k < inputs0.length, (scratch[k]!.asNat : ZMod p) = pre inputs0 k ∧
      ∀ j < 5, (scratch[k]!)[j]!.val < 2 ^ 54)
    (hslen : scratch.length = inputs0.length)
    (hacc : (acc.asNat : ZMod p) * pre inputs0 k.val = 1)
    (haccb : ∀ j < 5, acc[j]!.val < 2 ^ 54)
    (hlow : ∀ j < k.val, inputs[j]! = inputs0[j]!)
    (hhigh : ∀ j < inputs0.length, k.val ≤ j → Done inputs0 inputs j) :
    internal_invert_batch_loop1 inputs scratch acc k ⦃ (r : Slice FieldElement51) =>
      r.length = inputs0.length ∧ ∀ j < inputs0.length, Done inputs0 r j ⦄ := by
  unfold internal_invert_batch_loop1
  apply loop.spec_decr_nat (measure := fun x => x.2.2.val)
    (inv := fun x => x.2.2.val ≤ inputs0.length ∧ x.1.length = inputs0.length ∧
      (x.2.1.asNat : ZMod p) * pre inputs0 x.2.2.val = 1 ∧ (∀ j < 5, x.2.1[j]!.val < 2 ^ 54) ∧
      (∀ j < x.2.2.val, x.1[j]! = inputs0[j]!) ∧
      ∀ j < inputs0.length, x.2.2.val ≤ j → Done inputs0 x.1 j)
  · rintro ⟨s, a, k'⟩ ⟨hk', hsl, ha, hab, hl, hh⟩
    simp only at hk' hsl ha hab hl hh
    unfold internal_invert_batch_loop1.body
    by_cases hpos : k' > 0#usize
    · simp only [hpos, if_true]
      step as ⟨k1, hk1⟩
      have hk1' : k1.val < inputs0.length := by scalar_tac
      step as ⟨fe, hfe⟩
      have hfe' : fe = inputs0[k1.val]! := by
        rw [hfe, ← hl k1.val (by scalar_tac), Slice.getElem!_Nat_eq, getElem!_pos]
      have hfeb : ∀ j < 5, fe[j]!.val < 2 ^ 54 := hfe' ▸ hinputs k1.val hk1'
      step as ⟨tmp, htmp, htmpb⟩
      step as ⟨c, _, hc1, hc0⟩
      step as ⟨nz, _, hnz⟩
      step as ⟨fe1, hfe1⟩
      have hfe1' : fe1 = scratch[k1.val]! := by
        rw [hfe1, Slice.getElem!_Nat_eq, getElem!_pos]
      have hfe1b : ∀ j < 5, fe1[j]!.val < 2 ^ 54 := hfe1' ▸ (hscratch k1.val hk1').2
      step as ⟨prod, hprod, hprodb⟩
      step as ⟨fe2, back, hfe2, hback⟩
      step as ⟨fe3, hfe30, hfe31⟩
      step as ⟨acc1, ha0, ha1⟩
      have hpk : pre inputs0 k'.val = pre inputs0 k1.val * fac inputs0 k1.val := by
        rw [show k'.val = k1.val + 1 by scalar_tac, pre_succ]
      have hfe2' : fe2 = inputs0[k1.val]! := by rw [hfe2, ← hfe, hfe']
      -- the new accumulator and the new entry at `k1`
      have hnew : ((acc1.asNat : ZMod p) * pre inputs0 k1.val = 1 ∧
          ∀ j < 5, acc1[j]!.val < 2 ^ 54) ∧ Done inputs0 (s.set k1 fe3) k1.val := by
        unfold Done
        rw [Slice.getElem!_Nat_set_eq _ _ _ _ ⟨rfl, by scalar_tac⟩]
        rw [hpk, fac, ← hfe'] at ha
        by_cases hz : (fe.asNat : ZMod p) = 0
        · rw [hc1 (ZMod.natCast_eq_zero_iff_mod.mp hz), not_one] at hnz
          rw [ha0 hnz, hfe30 hnz, hfe2', ← hfe']
          rw [if_pos hz, mul_one] at ha
          exact ⟨⟨ha, hab⟩, fun _ => rfl, fun h => absurd hz h⟩
        · rw [hc0 (fun h => hz (ZMod.natCast_eq_zero_iff_mod.mpr h)), not_zero] at hnz
          rw [ha1 hnz, hfe31 hnz, ← hfe']
          rw [if_neg hz] at ha
          have htmp' : (tmp.asNat : ZMod p) = a.asNat * fe.asNat := by
            rw [← Nat.cast_mul, ZMod.natCast_eq_natCast_iff']
            exact htmp
          have hprod' : (prod.asNat : ZMod p) = a.asNat * pre inputs0 k1.val := by
            rw [← (hscratch k1.val hk1').1, ← hfe1', ← Nat.cast_mul,
              ZMod.natCast_eq_natCast_iff']
            exact hprod
          refine ⟨⟨by rw [htmp', ← ha]; ring,
              fun j hj => lt_trans (htmpb j hj) (by norm_num)⟩, fun h => absurd h hz,
            fun _ => ⟨by rw [hprod', ← ha]; ring, hprodb⟩⟩
      rw [hback]
      refine ⟨by scalar_tac, by rw [Slice.set_length, hsl], hnew.1.1, hnew.1.2, fun j hj => ?_,
        fun j hj hkj => ?_, by scalar_tac⟩
      · rw [Slice.getElem!_Nat_set_ne _ _ _ _ (by scalar_tac)]
        exact hl j (by scalar_tac)
      · by_cases hjk : j = k1.val
        · rw [hjk]
          exact hnew.2
        · unfold Done
          rw [Slice.getElem!_Nat_set_ne _ _ _ _ (Ne.symm hjk)]
          exact hh j hj (by scalar_tac)
    · simp only [hpos, if_false, WP.spec_ok]
      have hk0 : k'.val = 0 := by scalar_tac
      rw [hk0] at hh
      exact ⟨hsl, fun j hj => hh j hj (Nat.zero_le j)⟩
  · exact ⟨hk, hlen, hacc, haccb, hlow, hhigh⟩

@[step]
theorem internal_invert_batch_spec (inputs scratch : Slice FieldElement51)
    (hlen : scratch.length = inputs.length)
    (hinputs : ∀ i < inputs.length, ∀ j < 5, (inputs[i]!)[j]!.val < 2 ^ 54) :
    internal_invert_batch inputs scratch ⦃ (r _scratch : Slice FieldElement51) =>
      r.length = inputs.length ∧
      ∀ i < inputs.length,
        (inputs[i]!.asNat % p = 0 → r[i]! = inputs[i]!) ∧
        (inputs[i]!.asNat % p ≠ 0 → r[i]!.asNat * inputs[i]!.asNat % p = 1 ∧
          ∀ j < 5, (r[i]!)[j]!.val < 2 ^ 52) ⦄ := by
  unfold internal_invert_batch
  step as ⟨hlen'⟩
  step as ⟨one, hone, honeb⟩
  have hone' : (one.asNat : ZMod p) = pre inputs (0#usize).val := by
    rw [hone]
    simp [pre]
  step with internal_invert_batch_loop0_spec inputs scratch one inputs.len 0#usize (by simp) hlen
    (by simp) hinputs hone' (fun j hj => lt_trans (honeb j hj) (by norm_num))
    (fun k hk => absurd hk (by simp)) as ⟨scratch1, acc1, hs1len, hacc1, hacc1b, hs1⟩
  step as ⟨c, _, hc1, hc0⟩
  rw [hc0 (fun h => pre_ne_zero inputs inputs.length
    (hacc1 ▸ ZMod.natCast_eq_zero_iff_mod.mpr h))]
  step as ⟨c1, _, hc1'⟩
  rw [not_zero] at hc1'
  subst hc1'
  step as ⟨b, hb⟩
  have hbt : b = true := by
    rw [hb]
    decide
  step as ⟨hbt'⟩
  step as ⟨acc2, hinv1, hinv0, hacc2b⟩
  have hn : inputs.len.val = inputs.length := by simp
  have hacc2 : (acc2.asNat : ZMod p) * pre inputs inputs.len.val = 1 := by
    have hne : acc1.asNat % p ≠ 0 := fun h =>
      pre_ne_zero inputs inputs.length (hacc1 ▸ ZMod.natCast_eq_zero_iff_mod.mpr h)
    have h := ZMod.natCast_eq_natCast_of_mod_eq (hinv1 hne)
    push_cast at h
    rw [hn, ← hacc1, h]
  step with internal_invert_batch_loop1_spec inputs inputs scratch1 acc2 inputs.len hn.le rfl
    hinputs hs1 hs1len hacc2 (fun j hj => lt_trans (hacc2b j hj) (by norm_num))
    (fun j _ => rfl) (fun j hj hkj => absurd hj (by rw [← hn]; exact Nat.not_lt.mpr hkj))
    as ⟨r, hrlen, hr⟩
  refine ⟨hrlen, fun i hi => ⟨fun h => (hr i hi).1 (ZMod.natCast_eq_zero_iff_mod.mpr h),
    fun h => ?_⟩⟩
  obtain ⟨h1, h2⟩ := (hr i hi).2 (fun h' => h (ZMod.natCast_eq_zero_iff_mod.mp h'))
  refine ⟨?_, h2⟩
  rw [← one_mod_p, ← ZMod.natCast_eq_natCast_iff']
  push_cast
  exact h1

end Curve25519Dalek.field.FieldElement51
