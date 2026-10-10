module
public import Curve25519
public import Curve25519Dalek.Funs
public import Specs.Defs
public import Specs.Backend.Serial.U64.Defs
public import Subtle
public import Specs.Backend.Serial.U64.Scalar.Mul
public import Specs.Scalar.Unpack
public import Specs.Scalar.Scalar52Pack
public import Specs.Scalar.Lemmas
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open curve25519_dalek.scalar (Scalar HalfWidthScalar)
open curve25519_dalek.backend.serial.u64.scalar (montgomeryRadix)

namespace curve25519_dalek.scalar.MulAssignScalarSharedAScalar

@[step]
theorem mul_assign.«x86_64-unknown-linux-gnu_spec» (self _rhs : Scalar) :
    mul_assign.«x86_64-unknown-linux-gnu» self _rhs ⦃ (r : Scalar) =>
      r.asNat = self.asNat * _rhs.asNat % L ⦄ := by
  unfold mul_assign.«x86_64-unknown-linux-gnu»
  step as ⟨a, ha, hab⟩
  step as ⟨b, hb, hbb⟩
  step with backend.serial.u64.scalar.Scalar52.mul_spec a b hab hbb
    (ha ▸ hb ▸ mul_lt_montgomeryRadix_mul_L self.asNat_lt _rhs.asNat_lt) as ⟨c, hc, hcb⟩
  step with Scalar52.pack_spec c hcb (lt_two_pow_256_of_lt_L (hc ▸ Nat.mod_lt _ L_pos))
    as ⟨r, hr⟩
  rw [hr, hc, ha, hb]

end curve25519_dalek.scalar.MulAssignScalarSharedAScalar

namespace curve25519_dalek.scalar.MulAssignScalarSharedAScalar

@[step]
theorem mul_assign.«x86_64-no-tables_spec» (self _rhs : Scalar) :
    mul_assign.«x86_64-no-tables» self _rhs ⦃ (r : Scalar) =>
      r.asNat = self.asNat * _rhs.asNat % L ⦄ :=
  mul_assign.«x86_64-unknown-linux-gnu_spec» self _rhs

end curve25519_dalek.scalar.MulAssignScalarSharedAScalar
