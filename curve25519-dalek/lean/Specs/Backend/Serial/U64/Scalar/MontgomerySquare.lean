module
public import Curve25519
public import Curve25519Dalek.Funs
public import Specs.Backend.Serial.U64.Defs
public import Subtle
public import Specs.Backend.Serial.U64.Scalar.SquareInternal
public import Specs.Backend.Serial.U64.Scalar.MontgomeryReduce
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open curve25519_dalek.backend.serial.u64.scalar (Scalar52)

namespace curve25519_dalek.backend.serial.u64.scalar.Scalar52

@[step]
theorem montgomery_square_spec (self : Scalar52) (hself : ∀ i < 5, self[i]!.val < 2 ^ 52)
    (hself' : self.asNat ^ 2 < montgomeryRadix * L) :
    montgomery_square self ⦃ (r : Scalar52) =>
      r.asNat * montgomeryRadix % L = self.asNat ^ 2 % L ∧ r.asNat < L ∧
      ∀ i < 5, r[i]!.val < 2 ^ 52 ⦄ := by
  unfold montgomery_square
  step with square_internal_spec self hself as ⟨aa, haa_eq, haa_lt⟩
  step with montgomery_reduce_spec aa (fun i hi => (haa_lt i hi).trans (by decide))
    (haa_eq ▸ hself') as ⟨r, hr, hrL, hr_lt⟩
  exact ⟨haa_eq ▸ hr, hrL, hr_lt⟩

end curve25519_dalek.backend.serial.u64.scalar.Scalar52
