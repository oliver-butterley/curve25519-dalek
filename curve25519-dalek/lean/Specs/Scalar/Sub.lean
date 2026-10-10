module
public import Curve25519
public import Curve25519Dalek.Funs
public import Specs.Defs
public import Specs.Backend.Serial.U64.Defs
public import Subtle
public import Specs.Backend.Serial.U64.Scalar.Sub
public import Specs.Scalar.Unpack
public import Specs.Scalar.Scalar52Pack
public import Specs.Scalar.Lemmas
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open curve25519_dalek.scalar (Scalar HalfWidthScalar)
open curve25519_dalek.backend.serial.u64.scalar (montgomeryRadix)

namespace curve25519_dalek.scalar.SubShared0ScalarSharedAScalarScalar

@[step]
theorem sub.«x86_64-unknown-linux-gnu_spec» (self rhs : Scalar) (hself : self.asNat < L)
    (hrhs : rhs.asNat < L) :
    sub.«x86_64-unknown-linux-gnu» self rhs ⦃ (r : Scalar) =>
      (r.asNat + rhs.asNat) % L = self.asNat % L ∧ r.asNat < L ⦄ := by
  unfold sub.«x86_64-unknown-linux-gnu»
  step as ⟨a, ha, hab⟩
  step as ⟨b, hb, hbb⟩
  step with backend.serial.u64.scalar.Scalar52.sub_spec a b hab hbb
    (ha ▸ hself.trans_le (Nat.le_add_left _ _)) (hb ▸ hrhs.le) as ⟨c, hc, hcL, hcb⟩
  step with Scalar52.pack_spec c hcb (lt_two_pow_256_of_lt_L hcL) as ⟨r, hr⟩
  rw [hr, ← ha, ← hb]
  exact ⟨hc, hcL⟩

end curve25519_dalek.scalar.SubShared0ScalarSharedAScalarScalar

namespace curve25519_dalek.scalar.SubShared0ScalarSharedAScalarScalar

@[step]
theorem sub.«x86_64-no-tables_spec» (self rhs : Scalar) (hself : self.asNat < L)
    (hrhs : rhs.asNat < L) :
    sub.«x86_64-no-tables» self rhs ⦃ (r : Scalar) =>
      (r.asNat + rhs.asNat) % L = self.asNat % L ∧ r.asNat < L ⦄ :=
  sub.«x86_64-unknown-linux-gnu_spec» self rhs hself hrhs

end curve25519_dalek.scalar.SubShared0ScalarSharedAScalarScalar
