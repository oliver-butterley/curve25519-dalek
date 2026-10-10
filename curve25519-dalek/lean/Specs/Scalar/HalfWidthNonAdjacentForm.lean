module
public import Curve25519
public import Curve25519Dalek.Funs
public import Specs.Defs
public import Specs.Backend.Serial.U64.Defs
public import Subtle
public import Specs.Scalar.NonAdjacentForm
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open curve25519_dalek.scalar (Scalar HalfWidthScalar)
open curve25519_dalek.backend.serial.u64.scalar (montgomeryRadix)

namespace curve25519_dalek.scalar.HalfWidthScalar

@[step]
theorem non_adjacent_form_spec (self : HalfWidthScalar) (w : Usize)
    (hw : 2 ≤ w.val ∧ w.val ≤ 8) (hself : self.asNat < 2 ^ 255) :
    non_adjacent_form self w ⦃ (r : Array I8 256#usize) =>
      r.asInt 1 = self.asNat ∧
      (∀ i < 256, r[i]!.val ≠ 0 → r[i]!.val % 2 = 1 ∧ 2 * |r[i]!.val| < 2 ^ w.val) ∧
      ∀ i < 256, ∀ j < 256, i < j → j < i + w.val → r[i]!.val ≠ 0 → r[j]!.val = 0 ⦄ := by
  unfold non_adjacent_form
  exact Scalar.non_adjacent_form_spec self w hw hself

end curve25519_dalek.scalar.HalfWidthScalar
