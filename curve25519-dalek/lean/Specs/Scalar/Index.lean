module
public import Curve25519
public import Curve25519Dalek.Funs
public import Specs.Defs
public import Specs.Backend.Serial.U64.Defs
public import Subtle
public import Specs.Lemmas.Array
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open curve25519_dalek.scalar (Scalar HalfWidthScalar)
open curve25519_dalek.backend.serial.u64.scalar (montgomeryRadix)

namespace curve25519_dalek.scalar.Scalar.Insts.CoreOpsIndexIndexUsizeU8

@[step]
theorem index_spec (self : Scalar) (_index : Usize) (hindex : _index.val < 32) :
    index self _index ⦃ (r : U8) =>
      r = self.bytes[_index.val]! ⦄ := by
  unfold index
  step with Array.index_usize_getElem!_spec as ⟨r, hr⟩
  exact hr

end curve25519_dalek.scalar.Scalar.Insts.CoreOpsIndexIndexUsizeU8
