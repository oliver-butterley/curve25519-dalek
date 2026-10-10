module
public import Curve25519
public import Curve25519Dalek.Funs
public import Specs.Defs
public import Specs.Backend.Serial.U64.Defs
public import Subtle
public import Zeroize
public import Specs.Backend.Serial.U64.Scalar.AsMontgomery
public import Specs.Backend.Serial.U64.Scalar.FromMontgomery
public import Specs.Backend.Serial.U64.Scalar.MontgomeryMul
public import Specs.Scalar.Unpack
public import Specs.Scalar.Scalar52Pack
public import Specs.Scalar.MontgomeryInvert
public import Specs.Scalar.One
public import Specs.Scalar.Zero
public import Specs.Scalar.Eq
public import Specs.Scalar.Lemmas
public import Specs.Backend.Serial.U64.Scalar.Lemmas
public import Specs.Lemmas.ZMod
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open curve25519_dalek.scalar (Scalar HalfWidthScalar)
open curve25519_dalek.backend.serial.u64.scalar (montgomeryRadix)

namespace curve25519_dalek.scalar.Scalar

open backend.serial.u64.scalar (Scalar52)

/-! ## Prefix products of the inputs, in `ZMod L` -/

/-- The product of the inputs before index `i`. -/
private def pre (inputs : Slice Scalar) (i : ℕ) : ZMod L :=
  ∏ k ∈ Finset.range i, (inputs[k]!.asNat : ZMod L)

private theorem pre_succ (inputs : Slice Scalar) (i : ℕ) :
    pre inputs (i + 1) = pre inputs i * inputs[i]!.asNat :=
  Finset.prod_range_succ _ i

private theorem pre_ne_zero (inputs : Slice Scalar)
    (hinputs : ∀ i < inputs.length, inputs[i]!.asNat % L ≠ 0) :
    pre inputs inputs.length ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun k hk h0 =>
    hinputs k (Finset.mem_range.mp hk) (ZMod.natCast_eq_zero_iff_mod.mp h0)

/-- `v` is the Montgomery form `x * R` of `x`, reduced and with 52-bit limbs. -/
private def MontVal (v : Scalar52) (x : ZMod L) : Prop :=
  (v.asNat : ZMod L) = x * montgomeryRadix ∧ v.asNat < L ∧ ∀ j < 5, v[j]!.val < 2 ^ 52

/-- The Montgomery product of two Montgomery forms. -/
private theorem montVal_mul {a b r : Scalar52} {x y : ZMod L} (ha : MontVal a x)
    (hb : (b.asNat : ZMod L) = y * montgomeryRadix)
    (hr : r.asNat * montgomeryRadix % L = a.asNat * b.asNat % L) :
    (r.asNat : ZMod L) = x * y * montgomeryRadix := by
  have hr' : (r.asNat : ZMod L) * montgomeryRadix = a.asNat * b.asNat := by
    exact_mod_cast (ZMod.natCast_eq_natCast_iff' _ _ _).mpr hr
  apply mul_right_cancel₀ montgomeryRadix_natCast_ne_zero
  rw [hr', ha.1, hb]
  ring

/-- The Montgomery product of a plain value and a Montgomery form. -/
private theorem plain_mul {a b r : Scalar52} {y : ZMod L}
    (hb : (b.asNat : ZMod L) = y * montgomeryRadix)
    (hr : r.asNat * montgomeryRadix % L = a.asNat * b.asNat % L) :
    (r.asNat : ZMod L) = a.asNat * y := by
  have hr' : (r.asNat : ZMod L) * montgomeryRadix = a.asNat * b.asNat := by
    exact_mod_cast (ZMod.natCast_eq_natCast_iff' _ _ _).mpr hr
  apply mul_right_cancel₀ montgomeryRadix_natCast_ne_zero
  rw [hr', hb]
  ring

private theorem mod_L_eq_one {a : ℕ} (h : (a : ZMod L) = 1) : a % L = 1 := by
  rw [← Nat.mod_eq_of_lt ((Nat.one_lt_two_pow (by decide)).trans two_pow_252_lt_L)]
  exact (ZMod.natCast_eq_natCast_iff' _ _ _).mp (by exact_mod_cast h)

/-! ## First loop: Montgomery forms of the inputs and of their prefix products -/

@[local step]
private theorem loop0_spec (inputs : Slice Scalar) (scratch : Slice Scalar52) (acc : Scalar52)
    (n : Usize) (hn : n.val = inputs.length) (hlen : scratch.length = inputs.length)
    (hacc : MontVal acc 1) :
    invert_batch_internal.«x86_64-unknown-linux-gnu_loop0» inputs scratch acc n 0#usize
      ⦃ (inputs1 : Slice Scalar) (scratch1 : Slice Scalar52) (acc1 : Scalar52) =>
      inputs1.length = inputs.length ∧ scratch1.length = inputs.length ∧
      MontVal acc1 (pre inputs inputs.length) ∧
      (∀ k < inputs.length, MontVal scratch1[k]! (pre inputs k)) ∧
      ∀ k < inputs.length,
        (inputs1[k]!.asNat : ZMod L) = inputs[k]!.asNat * montgomeryRadix ⦄ := by
  unfold invert_batch_internal.«x86_64-unknown-linux-gnu_loop0»
  apply loop.spec_decr_nat (measure := fun x => n.val - x.2.2.2.val)
    (inv := fun x => x.2.2.2.val ≤ n.val ∧ x.1.length = inputs.length ∧
      x.2.1.length = inputs.length ∧ MontVal x.2.2.1 (pre inputs x.2.2.2.val) ∧
      (∀ k < x.2.2.2.val, MontVal x.2.1[k]! (pre inputs k)) ∧
      (∀ k < x.2.2.2.val,
        (x.1[k]!.asNat : ZMod L) = inputs[k]!.asNat * montgomeryRadix) ∧
      ∀ k < inputs.length, x.2.2.2.val ≤ k → x.1[k]! = inputs[k]!)
  · rintro ⟨ins, sc, a, i⟩ ⟨hi, hinl, hscl, ha, hsc, hlow, hhigh⟩
    simp only at hi hinl hscl ha hsc hlow hhigh
    unfold invert_batch_internal.«x86_64-unknown-linux-gnu_loop0».body
    by_cases hlt : i < n
    · simp only [hlt, if_true]
      have hlt' : i.val < inputs.length := by scalar_tac
      step as ⟨sc1, hsc1⟩
      step as ⟨x, hx⟩
      have hx' : x = inputs[i.val]! := by
        rw [hx, ← hhigh i.val hlt' le_rfl, Slice.getElem!_Nat_eq, getElem!_pos]
      step as ⟨u, hu, hub⟩
      step as ⟨t, ht, htb⟩
      have htL : t.asNat < L := ht ▸ Nat.mod_lt _ L_pos
      step with Scalar52.pack_spec t htb (lt_two_pow_256_of_lt_L htL) as ⟨y, hy⟩
      step as ⟨ins1, hins1⟩
      step with backend.serial.u64.scalar.Scalar52.montgomery_mul_spec a t ha.2.2 htb
        (Nat.mul_lt_mul'' (ha.2.1.trans backend.serial.u64.scalar.L_lt_montgomeryRadix) htL) as
        ⟨a1, ha1, ha1L, ha1b⟩
      step as ⟨i1, hi1⟩
      have ht' : (t.asNat : ZMod L) = inputs[i.val]!.asNat * montgomeryRadix := by
        rw [← hx', ← hu]
        exact_mod_cast (ZMod.natCast_eq_natCast_of_mod_eq ht.symm).symm
      refine ⟨by scalar_tac, by rw [hins1, Slice.set_length, hinl],
        by rw [hsc1, Slice.set_length, hscl], ⟨?_, ha1L, ha1b⟩, fun k hk => ?_, fun k hk => ?_,
        fun k hk hik => ?_, by scalar_tac⟩
      · rw [hi1, pre_succ]
        exact montVal_mul ha ht' ha1
      · rw [hsc1]
        by_cases hki : k = i.val
        · rw [Slice.getElem!_Nat_set_eq _ _ _ _ ⟨hki.symm, by scalar_tac⟩, hki]
          exact ha
        · rw [Slice.getElem!_Nat_set_ne _ _ _ _ (Ne.symm hki)]
          exact hsc k (by scalar_tac)
      · rw [hins1]
        by_cases hki : k = i.val
        · rw [Slice.getElem!_Nat_set_eq _ _ _ _ ⟨hki.symm, by scalar_tac⟩, hki, ← ht']
          exact congrArg Nat.cast hy
        · rw [Slice.getElem!_Nat_set_ne _ _ _ _ (Ne.symm hki)]
          exact hlow k (by scalar_tac)
      · rw [hins1, Slice.getElem!_Nat_set_ne _ _ _ _ (by scalar_tac)]
        exact hhigh k hk (by scalar_tac)
    · simp only [hlt, if_false, WP.spec_ok]
      have hin : i.val = inputs.length := by scalar_tac
      rw [hin] at ha hsc hlow
      exact ⟨hinl, hscl, ha, hsc, hlow⟩
  · refine ⟨by simp, rfl, hlen, by simpa [pre] using hacc, fun k hk => absurd hk (by simp),
      fun k hk => absurd hk (by simp), fun k _ _ => rfl⟩

/-! ## Second loop: the inverses, from the back -/

@[local step]
private theorem loop1_spec (inputs inputs1 : Slice Scalar) (scratch : Slice Scalar52)
    (acc : Scalar52) (n : Usize) (hn : n.val = inputs.length)
    (hlen : inputs1.length = inputs.length) (hslen : scratch.length = inputs.length)
    (hscratch : ∀ k < inputs.length, MontVal scratch[k]! (pre inputs k))
    (hinputs1 : ∀ k < inputs.length,
      (inputs1[k]!.asNat : ZMod L) = inputs[k]!.asNat * montgomeryRadix)
    (hacc : (acc.asNat : ZMod L) * pre inputs inputs.length = 1) (haccL : acc.asNat < L)
    (haccb : ∀ j < 5, acc[j]!.val < 2 ^ 52) :
    invert_batch_internal.«x86_64-unknown-linux-gnu_loop1» inputs1 scratch acc n
      ⦃ (r : Slice Scalar) =>
      r.length = inputs.length ∧
      ∀ j < inputs.length, (r[j]!.asNat : ZMod L) * inputs[j]!.asNat = 1 ∧ r[j]!.asNat < L ⦄ := by
  unfold invert_batch_internal.«x86_64-unknown-linux-gnu_loop1»
  apply loop.spec_decr_nat (measure := fun x => x.2.2.val)
    (inv := fun x => x.2.2.val ≤ inputs.length ∧ x.1.length = inputs.length ∧
      (x.2.1.asNat : ZMod L) * pre inputs x.2.2.val = 1 ∧ x.2.1.asNat < L ∧
      (∀ j < 5, x.2.1[j]!.val < 2 ^ 52) ∧ (∀ j < x.2.2.val, x.1[j]! = inputs1[j]!) ∧
      ∀ j < inputs.length, x.2.2.val ≤ j →
        (x.1[j]!.asNat : ZMod L) * inputs[j]!.asNat = 1 ∧ x.1[j]!.asNat < L)
  · rintro ⟨ins, a, k⟩ ⟨hk, hinl, ha, haL, hab, hlow, hhigh⟩
    simp only at hk hinl ha haL hab hlow hhigh
    unfold invert_batch_internal.«x86_64-unknown-linux-gnu_loop1».body
    by_cases hpos : k > 0#usize
    · simp only [hpos, if_true]
      step as ⟨k1, hk1⟩
      have hk1' : k1.val < inputs.length := by scalar_tac
      step as ⟨x, hx⟩
      have hx' : x = inputs1[k1.val]! := by
        rw [hx, ← hlow k1.val (by scalar_tac), Slice.getElem!_Nat_eq, getElem!_pos]
      step as ⟨u, hu, hub⟩
      step with backend.serial.u64.scalar.Scalar52.montgomery_mul_spec a u hab hub
        (by
          rw [Nat.mul_comm]
          exact Nat.mul_lt_mul'' (backend.serial.u64.scalar.Scalar52.asNat_lt u hub) haL) as
        ⟨t, ht, htL, htb⟩
      step as ⟨z, hz⟩
      have hz' : z = scratch[k1.val]! := by
        rw [hz, Slice.getElem!_Nat_eq, getElem!_pos]
      have hzm : MontVal z (pre inputs k1.val) := hz' ▸ hscratch k1.val hk1'
      step with backend.serial.u64.scalar.Scalar52.montgomery_mul_spec a z hab hzm.2.2
        (Nat.mul_lt_mul'' (haL.trans backend.serial.u64.scalar.L_lt_montgomeryRadix)
          hzm.2.1) as ⟨w, hw, hwL, hwb⟩
      step with Scalar52.pack_spec w hwb (lt_two_pow_256_of_lt_L hwL) as ⟨y, hy⟩
      step as ⟨ins1, hins1⟩
      have hpk : pre inputs k.val = pre inputs k1.val * inputs[k1.val]!.asNat := by
        rw [show k.val = k1.val + 1 by scalar_tac, pre_succ]
      have hu' : (u.asNat : ZMod L) = inputs[k1.val]!.asNat * montgomeryRadix := by
        rw [hu, hx']
        exact hinputs1 k1.val hk1'
      have ht' := plain_mul hu' ht
      have hw' := plain_mul hzm.1 hw
      refine ⟨by scalar_tac, by rw [hins1, Slice.set_length, hinl], ?_, htL, htb,
        fun j hj => ?_, fun j hj hkj => ?_, by scalar_tac⟩
      · rw [ht', ← ha, hpk]
        ring
      · rw [hins1, Slice.getElem!_Nat_set_ne _ _ _ _ (by scalar_tac)]
        exact hlow j (by scalar_tac)
      · rw [hins1]
        by_cases hjk : j = k1.val
        · rw [Slice.getElem!_Nat_set_eq _ _ _ _ ⟨hjk.symm, by scalar_tac⟩, hjk, hy]
          refine ⟨?_, hwL⟩
          rw [hw', ← ha, hpk]
          ring
        · rw [Slice.getElem!_Nat_set_ne _ _ _ _ (Ne.symm hjk)]
          exact hhigh j hj (by scalar_tac)
    · simp only [hpos, if_false, WP.spec_ok]
      have hk0 : k.val = 0 := by scalar_tac
      rw [hk0] at hhigh
      exact ⟨hinl, fun j hj => hhigh j hj (Nat.zero_le j)⟩
  · exact ⟨by scalar_tac, hlen, hn ▸ hacc, haccL, haccb, fun j _ => rfl,
      fun j hj hkj => absurd hj (by scalar_tac)⟩

end curve25519_dalek.scalar.Scalar

namespace curve25519_dalek.scalar.Scalar

@[step]
theorem invert_batch_internal.«x86_64-unknown-linux-gnu_spec» (inputs : Slice Scalar)
    (scratch : Slice backend.serial.u64.scalar.Scalar52) (hlen : scratch.length = inputs.length)
    (hinputs : ∀ i < inputs.length, inputs[i]!.asNat % L ≠ 0) :
    invert_batch_internal.«x86_64-unknown-linux-gnu» inputs scratch
      ⦃ (ret : Scalar) (r : Slice Scalar)
      (_scratch : Slice backend.serial.u64.scalar.Scalar52) =>
      r.length = inputs.length ∧
      (∀ i < inputs.length, r[i]!.asNat * inputs[i]!.asNat % L = 1 ∧ r[i]!.asNat < L) ∧
      ret.asNat * (∏ i ∈ Finset.range inputs.length, inputs[i]!.asNat) % L = 1 ∧
      ret.asNat < L ⦄ := by
  unfold invert_batch_internal.«x86_64-unknown-linux-gnu»
  have hR := montgomeryRadix_natCast_ne_zero
  step as ⟨one, hone, honeb⟩
  step as ⟨acc, hacc, haccb⟩
  have haccm : MontVal acc 1 := by
    refine ⟨?_, hacc ▸ Nat.mod_lt _ L_pos, haccb⟩
    rw [one_mul, hacc, hone, ONE_spec, one_mul]
    exact ZMod.natCast_mod _ _
  step with loop0_spec inputs scratch acc inputs.len (by simp) hlen haccm as
    ⟨inputs1, scratch1, acc1, hin1l, hsc1l, hacc1, hsc1, hin1⟩
  step with Scalar52.pack_spec acc1 hacc1.2.2 (lt_two_pow_256_of_lt_L hacc1.2.1) as ⟨s1, hs1⟩
  have hacc1ne : acc1.asNat % L ≠ 0 := fun h =>
    mul_ne_zero (pre_ne_zero inputs hinputs) hR
      (hacc1.1 ▸ ZMod.natCast_eq_zero_iff_mod.mpr h)
  step with core.cmp.PartialEq.ne.trait_default.spec Insts.CoreCmpPartialEqScalar s1 ZERO
    (Insts.CoreCmpPartialEqScalar.eq_spec s1 ZERO) as ⟨b, hb⟩
  have hbt : b = true := hb.mpr fun h => hacc1ne (by
    rw [Nat.mod_eq_of_lt hacc1.2.1, ← hs1, h]
    exact ZERO_spec)
  step
  step with Scalar52.montgomery_invert_spec acc1 hacc1.2.2 hacc1.2.1 as
    ⟨s2, hs2, hs20, hs2L, hs2b⟩
  step as ⟨acc2, hacc2, hacc2L, hacc2b⟩
  step with Scalar52.pack_spec acc2 hacc2b (lt_two_pow_256_of_lt_L hacc2L) as ⟨ret, hret⟩
  have hacc2' : (acc2.asNat : ZMod L) * pre inputs inputs.length = 1 := by
    have h2 : (s2.asNat : ZMod L) * acc1.asNat = montgomeryRadix ^ 2 := by
      exact_mod_cast (ZMod.natCast_eq_natCast_iff' _ _ _).mpr (hs2 hacc1ne)
    have h3 : (acc2.asNat : ZMod L) * montgomeryRadix = s2.asNat := by
      exact_mod_cast (ZMod.natCast_eq_natCast_iff' _ _ _).mpr hacc2
    apply mul_right_cancel₀ (pow_ne_zero 2 hR)
    linear_combination (pre inputs inputs.length * montgomeryRadix) * h3 -
      (s2.asNat : ZMod L) * hacc1.1 + h2
  step with loop1_spec inputs inputs1 scratch1 acc2 inputs.len (by simp) hin1l hsc1l hsc1 hin1
    hacc2' hacc2L hacc2b as ⟨r, hrl, hr⟩
  simp only [core.slice.Slice.iter_mut, bind_ok]
  step with core.slice.iter.IterMut.Insts.ZeroizeZeroize.zeroize_const_spec
    backend.serial.u64.scalar.Scalar52.Insts.ZeroizeZeroize (Array.repeat 5#usize 0#u64)
    backend.serial.u64.scalar.Scalar52.Insts.ZeroizeZeroize.zeroize_spec
  unfold pre at hacc2'
  refine ⟨hrl, fun i hi => ⟨mod_L_eq_one ?_, (hr i hi).2⟩, mod_L_eq_one ?_, hret ▸ hacc2L⟩
  · push_cast
    exact (hr i hi).1
  · rw [hret]
    push_cast
    exact hacc2'

end curve25519_dalek.scalar.Scalar

namespace curve25519_dalek.scalar.Scalar

@[step]
theorem invert_batch_internal.«x86_64-no-tables_spec» (inputs : Slice Scalar)
    (scratch : Slice backend.serial.u64.scalar.Scalar52) (hlen : scratch.length = inputs.length)
    (hinputs : ∀ i < inputs.length, inputs[i]!.asNat % L ≠ 0) :
    invert_batch_internal.«x86_64-no-tables» inputs scratch
      ⦃ (ret : Scalar) (r : Slice Scalar)
      (_scratch : Slice backend.serial.u64.scalar.Scalar52) =>
      r.length = inputs.length ∧
      (∀ i < inputs.length, r[i]!.asNat * inputs[i]!.asNat % L = 1 ∧ r[i]!.asNat < L) ∧
      ret.asNat * (∏ i ∈ Finset.range inputs.length, inputs[i]!.asNat) % L = 1 ∧
      ret.asNat < L ⦄ :=
  invert_batch_internal.«x86_64-unknown-linux-gnu_spec» inputs scratch hlen hinputs

end curve25519_dalek.scalar.Scalar
