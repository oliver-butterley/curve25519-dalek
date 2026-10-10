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
theorem invert_batch_alloc.«x86_64-unknown-linux-gnu_spec» (inputs : Slice Scalar)
    (hinputs : ∀ i < inputs.length, inputs[i]!.asNat % L ≠ 0) :
    invert_batch_alloc.«x86_64-unknown-linux-gnu» inputs ⦃ (ret : Scalar) (r : Slice Scalar) =>
      r.length = inputs.length ∧
      (∀ i < inputs.length, r[i]!.asNat * inputs[i]!.asNat % L = 1 ∧ r[i]!.asNat < L) ∧
      ret.asNat * (∏ i ∈ Finset.range inputs.length, inputs[i]!.asNat) % L = 1 ∧
      ret.asNat < L ⦄ := by
  unfold invert_batch_alloc.«x86_64-unknown-linux-gnu»
  step as ⟨one, hone, honeb⟩
  step as ⟨acc, hacc, haccb⟩
  step with alloc.vec.from_elem_spec
    backend.serial.u64.scalar.Scalar52.Insts.CoreCloneClone acc inputs.len rfl
    as ⟨scratch, hsc, hsclen⟩
  simp only [alloc.vec.Vec.deref_mut, lift]
  have hslen : scratch.slice.length = inputs.length := by
    rw [show scratch.slice.length = scratch.length from rfl, hsclen, Slice.len_val]
  step as ⟨ret, r, scratch', hrlen, hr, hret, hretL⟩
  exact ⟨hrlen, hr, hret, hretL⟩

end curve25519_dalek.scalar.Scalar

namespace curve25519_dalek.scalar.Scalar

@[step]
theorem invert_batch_alloc.«x86_64-no-tables_spec» (inputs : Slice Scalar)
    (hinputs : ∀ i < inputs.length, inputs[i]!.asNat % L ≠ 0) :
    invert_batch_alloc.«x86_64-no-tables» inputs ⦃ (ret : Scalar) (r : Slice Scalar) =>
      r.length = inputs.length ∧
      (∀ i < inputs.length, r[i]!.asNat * inputs[i]!.asNat % L = 1 ∧ r[i]!.asNat < L) ∧
      ret.asNat * (∏ i ∈ Finset.range inputs.length, inputs[i]!.asNat) % L = 1 ∧
      ret.asNat < L ⦄ :=
  invert_batch_alloc.«x86_64-unknown-linux-gnu_spec» inputs hinputs

end curve25519_dalek.scalar.Scalar
