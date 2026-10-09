module
public import Curve25519
public import Curve25519Dalek.Funs
public import Specs.Backend.Serial.U64.Defs
public import Subtle
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open curve25519_dalek.backend.serial.u64.scalar (Scalar52)

namespace curve25519_dalek.backend.serial.u64.scalar.Scalar52.Insts.CoreOpsIndexIndexMutUsizeU64

@[step]
theorem index_mut_spec (self : Scalar52) (_index : Usize) (hindex : _index.val < 5) :
    index_mut self _index ⦃ (r : U64) (back : U64 → Scalar52) =>
      r = self[_index.val]! ∧ ∀ x, back x = self.set _index x ⦄ := by
  unfold index_mut
  step*
  subst_vars
  exact ⟨by simp_lists, fun _ => rfl⟩

end curve25519_dalek.backend.serial.u64.scalar.Scalar52.Insts.CoreOpsIndexIndexMutUsizeU64
