module
public import Curve25519
public import Curve25519Dalek.Funs
public import Specs.Backend.Serial.U64.Defs
public import Subtle
public section
set_option linter.style.longLine false

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open curve25519_dalek.backend.serial.u64.field (FieldElement51)

namespace curve25519_dalek.backend.serial.u64.field.FieldElement51.Insts.CoreOpsArithMulAssignSharedAFieldElement51
@[step]
theorem mul_assign_spec (self _rhs : FieldElement51)
    (hself : ∀ i < 5, self[i]!.val < 2 ^ 54) (hrhs : ∀ i < 5, _rhs[i]!.val < 2 ^ 54) :
    mul_assign self _rhs ⦃ (r : FieldElement51) =>
      r.asNat % p = self.asNat * _rhs.asNat % p ∧ ∀ i < 5, r[i]!.val < 2 ^ 52 ⦄ := by
  sorry
end curve25519_dalek.backend.serial.u64.field.FieldElement51.Insts.CoreOpsArithMulAssignSharedAFieldElement51
