module
public import Curve25519
public import Curve25519Dalek.Funs
public import Specs.Defs
public import Specs.Backend.Serial.U64.Defs
public import Subtle
public import Specs.Backend.Serial.U64.Scalar.FromBytesWide
public import Specs.Scalar.Scalar52Pack
public import Specs.Scalar.Lemmas
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open curve25519_dalek.scalar (Scalar HalfWidthScalar)
open curve25519_dalek.backend.serial.u64.scalar (montgomeryRadix)

namespace curve25519_dalek.scalar.Scalar

@[step]
theorem from_bytes_mod_order_wide.«x86_64-unknown-linux-gnu_spec» (input : Array U8 64#usize) :
    from_bytes_mod_order_wide.«x86_64-unknown-linux-gnu» input ⦃ (r : Scalar) =>
      r.asNat = input.asNat 8 % L ⦄ := by
  unfold from_bytes_mod_order_wide.«x86_64-unknown-linux-gnu»
  step as ⟨s, hs, hsb⟩
  step with Scalar52.pack_spec s hsb (lt_two_pow_256_of_lt_L (hs ▸ Nat.mod_lt _ L_pos))
    as ⟨r, hr⟩
  rw [hr, hs]

end curve25519_dalek.scalar.Scalar

namespace curve25519_dalek.scalar.Scalar

@[step]
theorem from_bytes_mod_order_wide.«x86_64-no-tables_spec» (input : Array U8 64#usize) :
    from_bytes_mod_order_wide.«x86_64-no-tables» input ⦃ (r : Scalar) =>
      r.asNat = input.asNat 8 % L ⦄ :=
  from_bytes_mod_order_wide.«x86_64-unknown-linux-gnu_spec» input

end curve25519_dalek.scalar.Scalar
