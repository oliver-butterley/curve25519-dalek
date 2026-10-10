module
public import Curve25519
public import Curve25519Dalek.Funs
public import Specs.Defs
public import Specs.Backend.Serial.U64.Defs
public import Subtle
public import Specs.Lemmas.Bytes
public import Specs.Scalar.HalfWidthFromBytes
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open curve25519_dalek.scalar (Scalar HalfWidthScalar)
open curve25519_dalek.backend.serial.u64.scalar (montgomeryRadix)

namespace curve25519_dalek.scalar.HalfWidthScalar.Insts.CoreConvertFromU8

@[step]
theorem from_spec (x : U8) :
    «from» x ⦃ (r : HalfWidthScalar) =>
      r.asNat = x.val ⦄ := by
  have key (a : Array U8 16#usize)
      (h : a.val = (List.replicate 16 0#u8).setSlice! 0 (x.bv.toLEBytes.map UScalar.mk)) :
      a.asNat 8 = x.val := by
    rw [← UScalar.bv_toNat]
    exact Array.asNat_setSlice!_toLEBytes a x.bv (by simp) h
  unfold «from»
  step*
  simp_all

end curve25519_dalek.scalar.HalfWidthScalar.Insts.CoreConvertFromU8

namespace curve25519_dalek.scalar.HalfWidthScalar.Insts.CoreConvertFromU16

@[step]
theorem from_spec (x : U16) :
    «from» x ⦃ (r : HalfWidthScalar) =>
      r.asNat = x.val ⦄ := by
  have key (a : Array U8 16#usize)
      (h : a.val = (List.replicate 16 0#u8).setSlice! 0 (x.bv.toLEBytes.map UScalar.mk)) :
      a.asNat 8 = x.val := by
    rw [← UScalar.bv_toNat]
    exact Array.asNat_setSlice!_toLEBytes a x.bv (by simp) h
  unfold «from»
  step*
  simp_all

end curve25519_dalek.scalar.HalfWidthScalar.Insts.CoreConvertFromU16

namespace curve25519_dalek.scalar.HalfWidthScalar.Insts.CoreConvertFromU32

@[step]
theorem from_spec (x : U32) :
    «from» x ⦃ (r : HalfWidthScalar) =>
      r.asNat = x.val ⦄ := by
  have key (a : Array U8 16#usize)
      (h : a.val = (List.replicate 16 0#u8).setSlice! 0 (x.bv.toLEBytes.map UScalar.mk)) :
      a.asNat 8 = x.val := by
    rw [← UScalar.bv_toNat]
    exact Array.asNat_setSlice!_toLEBytes a x.bv (by simp) h
  unfold «from»
  step*
  simp_all

end curve25519_dalek.scalar.HalfWidthScalar.Insts.CoreConvertFromU32

namespace curve25519_dalek.scalar.HalfWidthScalar.Insts.CoreConvertFromU64

@[step]
theorem from_spec (x : U64) :
    «from» x ⦃ (r : HalfWidthScalar) =>
      r.asNat = x.val ⦄ := by
  have key (a : Array U8 16#usize)
      (h : a.val = (List.replicate 16 0#u8).setSlice! 0 (x.bv.toLEBytes.map UScalar.mk)) :
      a.asNat 8 = x.val := by
    rw [← UScalar.bv_toNat]
    exact Array.asNat_setSlice!_toLEBytes a x.bv (by simp) h
  unfold «from»
  step*
  simp_all

end curve25519_dalek.scalar.HalfWidthScalar.Insts.CoreConvertFromU64

namespace curve25519_dalek.scalar.HalfWidthScalar.Insts.CoreConvertFromU128

@[step]
theorem from_spec (x : U128) :
    «from» x ⦃ (r : HalfWidthScalar) =>
      r.asNat = x.val ⦄ := by
  have key (a : Array U8 16#usize)
      (h : a.val = (List.replicate 16 0#u8).setSlice! 0 (x.bv.toLEBytes.map UScalar.mk)) :
      a.asNat 8 = x.val := by
    rw [← UScalar.bv_toNat]
    exact Array.asNat_setSlice!_toLEBytes a x.bv (by simp) h
  unfold «from»
  step*
  simp_all

end curve25519_dalek.scalar.HalfWidthScalar.Insts.CoreConvertFromU128
