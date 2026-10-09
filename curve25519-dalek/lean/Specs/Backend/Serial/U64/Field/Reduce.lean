module
public import Curve25519
public import Curve25519Dalek.Funs
public import Specs.Backend.Serial.U64.Defs
public import Subtle
public import Specs.Lemmas.AsNat
public import Specs.Lemmas.StepSpecs
public import Mathlib.Tactic.LinearCombination
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open curve25519_dalek.backend.serial.u64.field (FieldElement51)

namespace curve25519_dalek.backend.serial.u64.field.FieldElement51

open scoped Specs.GetElemSteps Specs.MaskStep
attribute [local scalar_tac_simps] Nat.shiftRight_eq_div_pow

@[step]
theorem reduce.LOW_51_BIT_MASK_spec :
    reduce.LOW_51_BIT_MASK ⦃ (r : U64) => r.val = 2 ^ 51 - 1 ⦄ := by
  unfold reduce.LOW_51_BIT_MASK
  step*

/-- The carry propagation of `reduce` preserves the value modulo `p`: the top carry `a₄ / 2^51`
re-enters the bottom limb multiplied by `19 = 2^255 mod p`. -/
private theorem reduce_asNat_mod (a₀ a₁ a₂ a₃ a₄ : ℕ) :
    (a₀ % 2 ^ 51 + 19 * (a₄ / 2 ^ 51) + 2 ^ 51 * (a₁ % 2 ^ 51 + a₀ / 2 ^ 51)
      + 2 ^ 102 * (a₂ % 2 ^ 51 + a₁ / 2 ^ 51) + 2 ^ 153 * (a₃ % 2 ^ 51 + a₂ / 2 ^ 51)
      + 2 ^ 204 * (a₄ % 2 ^ 51 + a₃ / 2 ^ 51)) % p
      = (a₀ + 2 ^ 51 * a₁ + 2 ^ 102 * a₂ + 2 ^ 153 * a₃ + 2 ^ 204 * a₄) % p := by
  have h₀ := Nat.div_add_mod a₀ (2 ^ 51)
  have h₁ := Nat.div_add_mod a₁ (2 ^ 51)
  have h₂ := Nat.div_add_mod a₂ (2 ^ 51)
  have h₃ := Nat.div_add_mod a₃ (2 ^ 51)
  have h₄ := Nat.div_add_mod a₄ (2 ^ 51)
  have hp := p_add_nineteen
  have h : (a₀ % 2 ^ 51 + 19 * (a₄ / 2 ^ 51) + 2 ^ 51 * (a₁ % 2 ^ 51 + a₀ / 2 ^ 51)
      + 2 ^ 102 * (a₂ % 2 ^ 51 + a₁ / 2 ^ 51) + 2 ^ 153 * (a₃ % 2 ^ 51 + a₂ / 2 ^ 51)
      + 2 ^ 204 * (a₄ % 2 ^ 51 + a₃ / 2 ^ 51)) + p * (a₄ / 2 ^ 51)
      = a₀ + 2 ^ 51 * a₁ + 2 ^ 102 * a₂ + 2 ^ 153 * a₃ + 2 ^ 204 * a₄ := by
    zify at *
    linear_combination h₀ + 2 ^ 51 * h₁ + 2 ^ 102 * h₂ + 2 ^ 153 * h₃ + 2 ^ 204 * h₄
      + (a₄ / 2 ^ 51 : ℤ) * hp
  rw [← h, Nat.add_mul_mod_self_left]

set_option linter.hashCommand false in
#decompose reduce reduce_eq
  letRange 10 15 => reduce.mask
  letRange 11 16 => reduce.carry

attribute [nolint docBlame defsWithUnderscore] reduce.mask reduce.carry

/-- First phase of `reduce`: every limb is masked to its low 51 bits. -/
@[step]
theorem reduce.mask_spec (limbs : Array U64 5#usize) (i : U64) (hi : i = limbs[0]!) :
    reduce.mask limbs i ⦃ (r : Array U64 5#usize) =>
      r[0]!.val = limbs[0]!.val % 2 ^ 51 ∧ r[1]!.val = limbs[1]!.val % 2 ^ 51 ∧
      r[2]!.val = limbs[2]!.val % 2 ^ 51 ∧ r[3]!.val = limbs[3]!.val % 2 ^ 51 ∧
      r[4]!.val = limbs[4]!.val % 2 ^ 51 ⦄ := by
  unfold reduce.mask
  step*
  simp_lists [*]

/-- Second phase of `reduce`: each carry is added to the next limb, the top one times 19. -/
@[step]
theorem reduce.carry_spec (c0 c1 c2 c3 c4 : U64) (limbs5 : Array U64 5#usize)
    (h0 : limbs5[0]!.val < 2 ^ 51) (h1 : limbs5[1]!.val < 2 ^ 51) (h2 : limbs5[2]!.val < 2 ^ 51)
    (h3 : limbs5[3]!.val < 2 ^ 51) (h4 : limbs5[4]!.val < 2 ^ 51) (hc0 : c0.val < 2 ^ 13)
    (hc1 : c1.val < 2 ^ 13) (hc2 : c2.val < 2 ^ 13) (hc3 : c3.val < 2 ^ 13)
    (hc4 : c4.val < 2 ^ 13) :
    reduce.carry c0 c1 c2 c3 c4 limbs5 ⦃ (r : Array U64 5#usize) =>
      r[0]!.val = limbs5[0]!.val + 19 * c4.val ∧ r[1]!.val = limbs5[1]!.val + c0.val ∧
      r[2]!.val = limbs5[2]!.val + c1.val ∧ r[3]!.val = limbs5[3]!.val + c2.val ∧
      r[4]!.val = limbs5[4]!.val + c3.val ⦄ := by
  unfold reduce.carry
  step*
  agrind

/-- `reduce` with the additional bound `r.asNat < 2 p`, used by `to_bytes`. -/
theorem reduce_lt_spec (limbs : Array U64 5#usize) :
    reduce limbs ⦃ (r : FieldElement51) =>
      r.asNat % p = FieldElement51.asNat limbs % p ∧ (∀ i < 5, r[i]!.val < 2 ^ 52) ∧
      r.asNat < 2 * p ⦄ := by
  rw [reduce_eq]
  step*
  have hp := p_add_nineteen
  rw [FieldElement51.asNat_eq, FieldElement51.asNat_eq, Nat.forall_lt_five]
  simp only [*, Nat.shiftRight_eq_div_pow]
  refine ⟨reduce_asNat_mod _ _ _ _ _, ?_, ?_⟩
  · scalar_tac
  · scalar_tac

@[step]
theorem reduce_spec (limbs : Array U64 5#usize) :
    reduce limbs ⦃ (r : FieldElement51) =>
      r.asNat % p = FieldElement51.asNat limbs % p ∧ ∀ i < 5, r[i]!.val < 2 ^ 52 ⦄ :=
  spec_mono (reduce_lt_spec limbs) fun _ h => ⟨h.1, h.2.1⟩

end curve25519_dalek.backend.serial.u64.field.FieldElement51
