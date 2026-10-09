module
public import Specs.Backend.Serial.U64.Constants.MinusOne
public import Specs.Backend.Serial.U64.Constants.EdwardsD
public import Specs.Backend.Serial.U64.Constants.EdwardsD2
public import Specs.Backend.Serial.U64.Constants.OneMinusEdwardsDSquared
public import Specs.Backend.Serial.U64.Constants.EdwardsDMinusOneSquared
public import Specs.Backend.Serial.U64.Constants.SqrtAdMinusOne
public import Specs.Backend.Serial.U64.Constants.InvsqrtAMinusD
public import Specs.Backend.Serial.U64.Constants.SqrtM1
public import Specs.Backend.Serial.U64.Constants.Aplus2OverFour
public import Specs.Backend.Serial.U64.Constants.L
public import Specs.Backend.Serial.U64.Constants.Lfactor
public import Specs.Backend.Serial.U64.Constants.R
public import Specs.Backend.Serial.U64.Constants.RR
public section
set_option linter.style.longLine false

/-! # Specs of `src/backend/serial/u64/constants.rs`

Audit file: every constant of `constants.rs` with its spec statement, proved by the theorem of the
same name (without the prime) in `Constants/`, and the axioms that proof depends on.
Definitions used: `FieldElement51.asNat`, `Scalar52.asNat` (`Specs/Backend/Serial/U64/Defs.lean`),
`p`, `a`, `d`, `A`, `curve25519.L` (`Curve25519/Basic.lean`).

Not yet specified (they need the curve model): `ED25519_BASEPOINT_POINT`,
`ED25519_BASEPOINT_128_POINT`, `EIGHT_TORSION`, `AFFINE_ODD_MULTIPLES_OF_BASEPOINT`,
`AFFINE_ODD_MULTIPLES_OF_BASEPOINT_128`, `ED25519_BASEPOINT_TABLE`.
Not translated (`digest` feature off): `ED25519_SQRTAM2`, `MONTGOMERY_A`, `MONTGOMERY_A_NEG`. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open curve25519_dalek.backend.serial.u64.field (FieldElement51)
open curve25519_dalek.backend.serial.u64.scalar (Scalar52)
open curve25519 (p a d A)

namespace curve25519_dalek.backend.serial.u64.constants

/-- `MINUS_ONE`: the field element `-1`. -/
theorem MINUS_ONE_spec' :
    MINUS_ONE ⦃ (r : FieldElement51) =>
      r.asNat + 1 = p ∧ ∀ i < 5, r[i]!.val < 2 ^ 51 ⦄ :=
  MINUS_ONE_spec

/-- info: 'curve25519_dalek.backend.serial.u64.constants.MINUS_ONE_spec'' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MINUS_ONE_spec'

/-- `EDWARDS_D`: the Edwards coefficient `d`. -/
theorem EDWARDS_D_spec' :
    EDWARDS_D ⦃ (r : FieldElement51) =>
      r.asNat = d.val ∧ ∀ i < 5, r[i]!.val < 2 ^ 51 ⦄ :=
  EDWARDS_D_spec

/-- info: 'curve25519_dalek.backend.serial.u64.constants.EDWARDS_D_spec'' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms EDWARDS_D_spec'

/-- `EDWARDS_D2`: `2 d`. -/
theorem EDWARDS_D2_spec' :
    EDWARDS_D2 ⦃ (r : FieldElement51) =>
      r.asNat = (2 * d).val ∧ ∀ i < 5, r[i]!.val < 2 ^ 51 ⦄ :=
  EDWARDS_D2_spec

/-- info: 'curve25519_dalek.backend.serial.u64.constants.EDWARDS_D2_spec'' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms EDWARDS_D2_spec'

/-- `ONE_MINUS_EDWARDS_D_SQUARED`: `1 - d²`. -/
theorem ONE_MINUS_EDWARDS_D_SQUARED_spec' :
    ONE_MINUS_EDWARDS_D_SQUARED ⦃ (r : FieldElement51) =>
      r.asNat = (1 - d ^ 2).val ∧ ∀ i < 5, r[i]!.val < 2 ^ 51 ⦄ :=
  ONE_MINUS_EDWARDS_D_SQUARED_spec

/-- info: 'curve25519_dalek.backend.serial.u64.constants.ONE_MINUS_EDWARDS_D_SQUARED_spec'' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ONE_MINUS_EDWARDS_D_SQUARED_spec'

/-- `EDWARDS_D_MINUS_ONE_SQUARED`: `(d - 1)²`. -/
theorem EDWARDS_D_MINUS_ONE_SQUARED_spec' :
    EDWARDS_D_MINUS_ONE_SQUARED ⦃ (r : FieldElement51) =>
      r.asNat = ((d - 1) ^ 2).val ∧ ∀ i < 5, r[i]!.val < 2 ^ 51 ⦄ :=
  EDWARDS_D_MINUS_ONE_SQUARED_spec

/-- info: 'curve25519_dalek.backend.serial.u64.constants.EDWARDS_D_MINUS_ONE_SQUARED_spec'' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms EDWARDS_D_MINUS_ONE_SQUARED_spec'

/-- `SQRT_AD_MINUS_ONE`: a square root of `a d - 1`. -/
theorem SQRT_AD_MINUS_ONE_spec' :
    SQRT_AD_MINUS_ONE ⦃ (r : FieldElement51) =>
      r.asNat < p ∧
      r.asNat ^ 2 % p = (a * d - 1).val ∧ ∀ i < 5, r[i]!.val < 2 ^ 51 ⦄ :=
  SQRT_AD_MINUS_ONE_spec

/-- info: 'curve25519_dalek.backend.serial.u64.constants.SQRT_AD_MINUS_ONE_spec'' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SQRT_AD_MINUS_ONE_spec'

/-- `INVSQRT_A_MINUS_D`: `1 / sqrt(a - d)`, i.e. `r² (a - d) = 1`. -/
theorem INVSQRT_A_MINUS_D_spec' :
    INVSQRT_A_MINUS_D ⦃ (r : FieldElement51) =>
      r.asNat < p ∧
      r.asNat ^ 2 * (a - d).val % p = 1 ∧ ∀ i < 5, r[i]!.val < 2 ^ 51 ⦄ :=
  INVSQRT_A_MINUS_D_spec

/-- info: 'curve25519_dalek.backend.serial.u64.constants.INVSQRT_A_MINUS_D_spec'' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms INVSQRT_A_MINUS_D_spec'

/-- `SQRT_M1`: a square root of `-1`. -/
theorem SQRT_M1_spec' :
    SQRT_M1 ⦃ (r : FieldElement51) =>
      r.asNat < p ∧ (r.asNat ^ 2 + 1) % p = 0 ∧ ∀ i < 5, r[i]!.val < 2 ^ 51 ⦄ :=
  SQRT_M1_spec

/-- info: 'curve25519_dalek.backend.serial.u64.constants.SQRT_M1_spec'' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SQRT_M1_spec'

/-- `APLUS2_OVER_FOUR`: `(A + 2) / 4 = 121666`. -/
theorem APLUS2_OVER_FOUR_spec' :
    APLUS2_OVER_FOUR ⦃ (r : FieldElement51) =>
      r.asNat * 4 = A + 2 ∧ ∀ i < 5, r[i]!.val < 2 ^ 51 ⦄ :=
  APLUS2_OVER_FOUR_spec

/-- info: 'curve25519_dalek.backend.serial.u64.constants.APLUS2_OVER_FOUR_spec'' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms APLUS2_OVER_FOUR_spec'

/-- `L`: the group order `ℓ`, in canonical radix-2^52 limbs. -/
theorem L_spec' :
    Scalar52.asNat L = curve25519.L ∧ ∀ i < 5, L[i]!.val < 2 ^ 52 :=
  L_spec

/-- info: 'curve25519_dalek.backend.serial.u64.constants.L_spec'' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms L_spec'

/-- `LFACTOR`: `-ℓ⁻¹ mod 2^52`. -/
theorem LFACTOR_spec' :
    LFACTOR.val < 2 ^ 52 ∧ (LFACTOR.val * curve25519.L + 1) % 2 ^ 52 = 0 :=
  LFACTOR_spec

/-- info: 'curve25519_dalek.backend.serial.u64.constants.LFACTOR_spec'' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms LFACTOR_spec'

/-- `R`: the Montgomery radix `2^260 mod ℓ`. -/
theorem R_spec' :
    Scalar52.asNat R = 2 ^ 260 % curve25519.L ∧ ∀ i < 5, R[i]!.val < 2 ^ 52 :=
  R_spec

/-- info: 'curve25519_dalek.backend.serial.u64.constants.R_spec'' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms R_spec'

/-- `RR`: `R² = 2^520 mod ℓ`. -/
theorem RR_spec' :
    Scalar52.asNat RR = 2 ^ 520 % curve25519.L ∧ ∀ i < 5, RR[i]!.val < 2 ^ 52 :=
  RR_spec

/-- info: 'curve25519_dalek.backend.serial.u64.constants.RR_spec'' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms RR_spec'

end curve25519_dalek.backend.serial.u64.constants
