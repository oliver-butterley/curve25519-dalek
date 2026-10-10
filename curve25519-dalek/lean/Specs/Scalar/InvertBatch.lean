module
public import Curve25519
public import Curve25519Dalek.Funs
public import Specs.Defs
public import Specs.Backend.Serial.U64.Defs
public import Subtle
public import Specs.Backend.Serial.U64.Scalar.AsMontgomery
public import Specs.Scalar.Unpack
public import Specs.Scalar.InvertBatchInternal
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open curve25519_dalek.scalar (Scalar HalfWidthScalar)
open curve25519_dalek.backend.serial.u64.scalar (montgomeryRadix)

namespace curve25519_dalek.scalar.Scalar

@[step]
theorem invert_batch.«x86_64-unknown-linux-gnu_spec» {N : Usize} (inputs : Array Scalar N)
    (hinputs : ∀ i < N.val, inputs[i]!.asNat % L ≠ 0) :
    invert_batch.«x86_64-unknown-linux-gnu» inputs ⦃ (ret : Scalar) (r : Array Scalar N) =>
      (∀ i < N.val, r[i]!.asNat * inputs[i]!.asNat % L = 1 ∧ r[i]!.asNat < L) ∧
      ret.asNat * (∏ i ∈ Finset.range N.val, inputs[i]!.asNat) % L = 1 ∧
      ret.asNat < L ⦄ := by
  unfold invert_batch.«x86_64-unknown-linux-gnu»
  step as ⟨one, hone, honeb⟩
  step as ⟨acc, hacc, haccb⟩
  step as ⟨s, back, hs, hback⟩
  step as ⟨s1, back1, hs1, hback1⟩
  have hsN : s.length = N.val := by
    simp only [Slice.length, hs]
    exact inputs.property
  have hs1N : s1.length = s.length := by
    simp only [Slice.length, hs1, hs, Array.repeat_val, List.length_replicate]
    exact inputs.property.symm
  have hin : ∀ i : ℕ, inputs[i]! = s[i]! := by
    intro i
    rw [Array.getElem!_Nat_eq, Slice.getElem!_Nat_eq, hs]
  step with invert_batch_internal.«x86_64-unknown-linux-gnu_spec» s s1 hs1N
    (fun i hi => hin i ▸ hinputs i (hsN ▸ hi)) as ⟨ret, r, sc, hrl, hr, hret, hretL⟩
  have hget : ∀ i : ℕ, (back r)[i]! = r[i]! := by
    intro i
    rw [hback, Array.getElem!_Nat_eq, Array.from_slice_val _ _ (by simp [hrl, hsN]),
      ← Slice.getElem!_Nat_eq]
  refine ⟨fun i hi => ?_, ?_, hretL⟩
  · rw [hget, hin]
    exact hr i (hsN ▸ hi)
  · rw [← hsN, Finset.prod_congr rfl fun i _ => congrArg Scalar.asNat (hin i)]
    exact hret

end curve25519_dalek.scalar.Scalar

namespace curve25519_dalek.scalar.Scalar

@[step]
theorem invert_batch.«x86_64-no-tables_spec» {N : Usize} (inputs : Array Scalar N)
    (hinputs : ∀ i < N.val, inputs[i]!.asNat % L ≠ 0) :
    invert_batch.«x86_64-no-tables» inputs ⦃ (ret : Scalar) (r : Array Scalar N) =>
      (∀ i < N.val, r[i]!.asNat * inputs[i]!.asNat % L = 1 ∧ r[i]!.asNat < L) ∧
      ret.asNat * (∏ i ∈ Finset.range N.val, inputs[i]!.asNat) % L = 1 ∧
      ret.asNat < L ⦄ :=
  invert_batch.«x86_64-unknown-linux-gnu_spec» inputs hinputs

end curve25519_dalek.scalar.Scalar
