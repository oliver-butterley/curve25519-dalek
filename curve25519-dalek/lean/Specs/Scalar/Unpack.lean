module
public import Curve25519
public import Curve25519Dalek.Funs
public import Specs.Defs
public import Specs.Backend.Serial.U64.Defs
public import Subtle
public import Specs.Backend.Serial.U64.Scalar.FromBytes
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open curve25519_dalek.scalar (Scalar HalfWidthScalar)
open curve25519_dalek.backend.serial.u64.scalar (montgomeryRadix)

namespace curve25519_dalek.scalar.Scalar

@[step]
theorem unpack.«x86_64-unknown-linux-gnu_spec» (self : Scalar) :
    unpack.«x86_64-unknown-linux-gnu» self ⦃ (r : backend.serial.u64.scalar.Scalar52) =>
      r.asNat = self.asNat ∧ ∀ i < 5, r[i]!.val < 2 ^ 52 ⦄ := by
  unfold unpack.«x86_64-unknown-linux-gnu»
  step as ⟨r, hr, hrb⟩
  exact ⟨hr, hrb⟩

end curve25519_dalek.scalar.Scalar

namespace curve25519_dalek.scalar.Scalar

@[step]
theorem unpack.«x86_64-no-tables_spec» (self : Scalar) :
    unpack.«x86_64-no-tables» self ⦃ (r : backend.serial.u64.scalar.Scalar52) =>
      r.asNat = self.asNat ∧ ∀ i < 5, r[i]!.val < 2 ^ 52 ⦄ := by
  unfold unpack.«x86_64-no-tables»
  step as ⟨r, hr, hrb⟩
  exact ⟨hr, hrb⟩

end curve25519_dalek.scalar.Scalar
