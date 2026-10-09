module
public import Zeroize.Lemmas
public import Curve25519Dalek.Funs
@[expose] public section
-- The generated instance names exceed 100 characters.
set_option linter.style.longLine false
open Aeneas Aeneas.Std Result Aeneas.Std.WP

/-! # `zeroize` for the trait instances generated in `Curve25519Dalek/Funs.lean` (no axioms)

Concrete `@[step]` specs: the blanket impl for the primitive `DefaultIsZeroes` types gives `0`
(`false` for `bool`), arrays of those zeroize to all-zero arrays, and the backend field/scalar
types and Niels points zeroize to their all-zero value. With these, `step*` handles zeroize call
sites without having to supply the constant `z` of `Zeroize/Lemmas.lean`.
-/

namespace curve25519_dalek

/-! ## Blanket impl for primitive types -/

@[step] theorem U8.Insts.ZeroizeDefaultIsZeroes.zeroize_spec (x : Std.U8) :
    _root_.zeroize.Zeroize.Blanket.zeroize U8.Insts.ZeroizeDefaultIsZeroes x ⦃ r => r = 0#u8 ⦄ := by
  rw [_root_.zeroize.Zeroize.Blanket.zeroize_eq]; exact (spec_ok _).mpr rfl

@[step] theorem U32.Insts.ZeroizeDefaultIsZeroes.zeroize_spec (x : Std.U32) :
    _root_.zeroize.Zeroize.Blanket.zeroize U32.Insts.ZeroizeDefaultIsZeroes x ⦃ r => r = 0#u32 ⦄ := by
  rw [_root_.zeroize.Zeroize.Blanket.zeroize_eq]; exact (spec_ok _).mpr rfl

@[step] theorem U64.Insts.ZeroizeDefaultIsZeroes.zeroize_spec (x : Std.U64) :
    _root_.zeroize.Zeroize.Blanket.zeroize U64.Insts.ZeroizeDefaultIsZeroes x ⦃ r => r = 0#u64 ⦄ := by
  rw [_root_.zeroize.Zeroize.Blanket.zeroize_eq]; exact (spec_ok _).mpr rfl

@[step] theorem I8.Insts.ZeroizeDefaultIsZeroes.zeroize_spec (x : Std.I8) :
    _root_.zeroize.Zeroize.Blanket.zeroize I8.Insts.ZeroizeDefaultIsZeroes x ⦃ r => r = 0#i8 ⦄ := by
  rw [_root_.zeroize.Zeroize.Blanket.zeroize_eq]; exact (spec_ok _).mpr rfl

@[step] theorem Bool.Insts.ZeroizeDefaultIsZeroes.zeroize_spec (x : Bool) :
    _root_.zeroize.Zeroize.Blanket.zeroize Bool.Insts.ZeroizeDefaultIsZeroes x ⦃ r => r = false ⦄ := by
  rw [_root_.zeroize.Zeroize.Blanket.zeroize_eq]; exact (spec_ok _).mpr rfl

/-! ## Arrays of primitive types -/

@[step] theorem Array.Insts.ZeroizeZeroize.zeroize_U8_spec {N : Std.Usize} (a : Array Std.U8 N) :
    _root_.Array.Insts.ZeroizeZeroize.zeroize
      (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes) a ⦃ r => r = Array.repeat N 0#u8 ⦄ :=
  _root_.Array.Insts.ZeroizeZeroize.zeroize_const_spec _ _ U8.Insts.ZeroizeDefaultIsZeroes.zeroize_spec a

@[step] theorem Array.Insts.ZeroizeZeroize.zeroize_U32_spec {N : Std.Usize} (a : Array Std.U32 N) :
    _root_.Array.Insts.ZeroizeZeroize.zeroize
      (zeroize.Zeroize.Blanket U32.Insts.ZeroizeDefaultIsZeroes) a ⦃ r => r = Array.repeat N 0#u32 ⦄ :=
  _root_.Array.Insts.ZeroizeZeroize.zeroize_const_spec _ _ U32.Insts.ZeroizeDefaultIsZeroes.zeroize_spec a

@[step] theorem Array.Insts.ZeroizeZeroize.zeroize_U64_spec {N : Std.Usize} (a : Array Std.U64 N) :
    _root_.Array.Insts.ZeroizeZeroize.zeroize
      (zeroize.Zeroize.Blanket U64.Insts.ZeroizeDefaultIsZeroes) a ⦃ r => r = Array.repeat N 0#u64 ⦄ :=
  _root_.Array.Insts.ZeroizeZeroize.zeroize_const_spec _ _ U64.Insts.ZeroizeDefaultIsZeroes.zeroize_spec a

@[step] theorem Array.Insts.ZeroizeZeroize.zeroize_I8_spec {N : Std.Usize} (a : Array Std.I8 N) :
    _root_.Array.Insts.ZeroizeZeroize.zeroize
      (zeroize.Zeroize.Blanket I8.Insts.ZeroizeDefaultIsZeroes) a ⦃ r => r = Array.repeat N 0#i8 ⦄ :=
  _root_.Array.Insts.ZeroizeZeroize.zeroize_const_spec _ _ I8.Insts.ZeroizeDefaultIsZeroes.zeroize_spec a

/-! ## Backend field elements and scalars -/

@[step] theorem backend.serial.u64.field.FieldElement51.Insts.ZeroizeZeroize.zeroize_spec
    (x : backend.serial.u64.field.FieldElement51) :
    backend.serial.u64.field.FieldElement51.Insts.ZeroizeZeroize.zeroize x ⦃ r =>
      r = Array.repeat 5#usize 0#u64 ⦄ := by
  unfold backend.serial.u64.field.FieldElement51.Insts.ZeroizeZeroize.zeroize; step*

@[step] theorem backend.serial.u32.field.FieldElement2625.Insts.ZeroizeZeroize.zeroize_spec
    (x : backend.serial.u32.field.FieldElement2625) :
    backend.serial.u32.field.FieldElement2625.Insts.ZeroizeZeroize.zeroize x ⦃ r =>
      r = Array.repeat 10#usize 0#u32 ⦄ := by
  unfold backend.serial.u32.field.FieldElement2625.Insts.ZeroizeZeroize.zeroize; step*

@[step] theorem backend.serial.u64.scalar.Scalar52.Insts.ZeroizeZeroize.zeroize_spec
    (x : backend.serial.u64.scalar.Scalar52) :
    backend.serial.u64.scalar.Scalar52.Insts.ZeroizeZeroize.zeroize x ⦃ r =>
      r = Array.repeat 5#usize 0#u64 ⦄ := by
  unfold backend.serial.u64.scalar.Scalar52.Insts.ZeroizeZeroize.zeroize; step*

@[step] theorem backend.serial.u32.scalar.Scalar29.Insts.ZeroizeZeroize.zeroize_spec
    (x : backend.serial.u32.scalar.Scalar29) :
    backend.serial.u32.scalar.Scalar29.Insts.ZeroizeZeroize.zeroize x ⦃ r =>
      r = Array.repeat 9#usize 0#u32 ⦄ := by
  unfold backend.serial.u32.scalar.Scalar29.Insts.ZeroizeZeroize.zeroize; step*

/-! ## Niels points (all coordinates zeroized) -/

@[step] theorem
    backend.serial.curve_models.AffineNielsPoint.«x86_64-unknown-linux-gnu».Insts.ZeroizeZeroize.zeroize_spec
    (p : backend.serial.curve_models.AffineNielsPoint.«x86_64-unknown-linux-gnu») :
    backend.serial.curve_models.AffineNielsPoint.«x86_64-unknown-linux-gnu».Insts.ZeroizeZeroize.zeroize
      p ⦃ r => r =
        { y_plus_x := Array.repeat 5#usize 0#u64, y_minus_x := Array.repeat 5#usize 0#u64,
          xy2d := Array.repeat 5#usize 0#u64 } ⦄ := by
  unfold
    backend.serial.curve_models.AffineNielsPoint.«x86_64-unknown-linux-gnu».Insts.ZeroizeZeroize.zeroize
  step*

@[step] theorem
    backend.serial.curve_models.AffineNielsPoint.«x86_64-no-tables».Insts.ZeroizeZeroize.zeroize_spec
    (p : backend.serial.curve_models.AffineNielsPoint.«x86_64-no-tables») :
    backend.serial.curve_models.AffineNielsPoint.«x86_64-no-tables».Insts.ZeroizeZeroize.zeroize
      p ⦃ r => r =
        { y_plus_x := Array.repeat 5#usize 0#u64, y_minus_x := Array.repeat 5#usize 0#u64,
          xy2d := Array.repeat 5#usize 0#u64 } ⦄ := by
  unfold backend.serial.curve_models.AffineNielsPoint.«x86_64-no-tables».Insts.ZeroizeZeroize.zeroize
  step*

@[step] theorem
    backend.serial.curve_models.AffineNielsPoint.«i686-unknown-linux-gnu».Insts.ZeroizeZeroize.zeroize_spec
    (p : backend.serial.curve_models.AffineNielsPoint.«i686-unknown-linux-gnu») :
    backend.serial.curve_models.AffineNielsPoint.«i686-unknown-linux-gnu».Insts.ZeroizeZeroize.zeroize
      p ⦃ r => r =
        { y_plus_x := Array.repeat 10#usize 0#u32, y_minus_x := Array.repeat 10#usize 0#u32,
          xy2d := Array.repeat 10#usize 0#u32 } ⦄ := by
  unfold
    backend.serial.curve_models.AffineNielsPoint.«i686-unknown-linux-gnu».Insts.ZeroizeZeroize.zeroize
  step*

@[step] theorem
    backend.serial.curve_models.AffineNielsPoint.«i686-no-tables».Insts.ZeroizeZeroize.zeroize_spec
    (p : backend.serial.curve_models.AffineNielsPoint.«i686-no-tables») :
    backend.serial.curve_models.AffineNielsPoint.«i686-no-tables».Insts.ZeroizeZeroize.zeroize
      p ⦃ r => r =
        { y_plus_x := Array.repeat 10#usize 0#u32, y_minus_x := Array.repeat 10#usize 0#u32,
          xy2d := Array.repeat 10#usize 0#u32 } ⦄ := by
  unfold backend.serial.curve_models.AffineNielsPoint.«i686-no-tables».Insts.ZeroizeZeroize.zeroize
  step*

@[step] theorem
    backend.serial.curve_models.ProjectiveNielsPoint.«x86_64-unknown-linux-gnu».Insts.ZeroizeZeroize.zeroize_spec
    (p : backend.serial.curve_models.ProjectiveNielsPoint.«x86_64-unknown-linux-gnu») :
    backend.serial.curve_models.ProjectiveNielsPoint.«x86_64-unknown-linux-gnu».Insts.ZeroizeZeroize.zeroize
      p ⦃ r => r =
        { Y_plus_X := Array.repeat 5#usize 0#u64, Y_minus_X := Array.repeat 5#usize 0#u64,
          Z := Array.repeat 5#usize 0#u64, T2d := Array.repeat 5#usize 0#u64 } ⦄ := by
  unfold
    backend.serial.curve_models.ProjectiveNielsPoint.«x86_64-unknown-linux-gnu».Insts.ZeroizeZeroize.zeroize
  step*

@[step] theorem
    backend.serial.curve_models.ProjectiveNielsPoint.«x86_64-no-tables».Insts.ZeroizeZeroize.zeroize_spec
    (p : backend.serial.curve_models.ProjectiveNielsPoint.«x86_64-no-tables») :
    backend.serial.curve_models.ProjectiveNielsPoint.«x86_64-no-tables».Insts.ZeroizeZeroize.zeroize
      p ⦃ r => r =
        { Y_plus_X := Array.repeat 5#usize 0#u64, Y_minus_X := Array.repeat 5#usize 0#u64,
          Z := Array.repeat 5#usize 0#u64, T2d := Array.repeat 5#usize 0#u64 } ⦄ := by
  unfold
    backend.serial.curve_models.ProjectiveNielsPoint.«x86_64-no-tables».Insts.ZeroizeZeroize.zeroize
  step*

@[step] theorem
    backend.serial.curve_models.ProjectiveNielsPoint.«i686-unknown-linux-gnu».Insts.ZeroizeZeroize.zeroize_spec
    (p : backend.serial.curve_models.ProjectiveNielsPoint.«i686-unknown-linux-gnu») :
    backend.serial.curve_models.ProjectiveNielsPoint.«i686-unknown-linux-gnu».Insts.ZeroizeZeroize.zeroize
      p ⦃ r => r =
        { Y_plus_X := Array.repeat 10#usize 0#u32, Y_minus_X := Array.repeat 10#usize 0#u32,
          Z := Array.repeat 10#usize 0#u32, T2d := Array.repeat 10#usize 0#u32 } ⦄ := by
  unfold
    backend.serial.curve_models.ProjectiveNielsPoint.«i686-unknown-linux-gnu».Insts.ZeroizeZeroize.zeroize
  step*

@[step] theorem
    backend.serial.curve_models.ProjectiveNielsPoint.«i686-no-tables».Insts.ZeroizeZeroize.zeroize_spec
    (p : backend.serial.curve_models.ProjectiveNielsPoint.«i686-no-tables») :
    backend.serial.curve_models.ProjectiveNielsPoint.«i686-no-tables».Insts.ZeroizeZeroize.zeroize
      p ⦃ r => r =
        { Y_plus_X := Array.repeat 10#usize 0#u32, Y_minus_X := Array.repeat 10#usize 0#u32,
          Z := Array.repeat 10#usize 0#u32, T2d := Array.repeat 10#usize 0#u32 } ⦄ := by
  unfold
    backend.serial.curve_models.ProjectiveNielsPoint.«i686-no-tables».Insts.ZeroizeZeroize.zeroize
  step*

/-! ## Byte-array types -/

@[step] theorem montgomery.MontgomeryPoint.Insts.ZeroizeZeroize.zeroize_spec
    (p : montgomery.MontgomeryPoint) :
    montgomery.MontgomeryPoint.Insts.ZeroizeZeroize.zeroize p ⦃ r =>
      r = Array.repeat 32#usize 0#u8 ⦄ := by
  unfold montgomery.MontgomeryPoint.Insts.ZeroizeZeroize.zeroize; step*

@[step] theorem ristretto.CompressedRistretto.Insts.ZeroizeZeroize.zeroize_spec
    (p : ristretto.CompressedRistretto) :
    ristretto.CompressedRistretto.Insts.ZeroizeZeroize.zeroize p ⦃ r =>
      r = Array.repeat 32#usize 0#u8 ⦄ := by
  unfold ristretto.CompressedRistretto.Insts.ZeroizeZeroize.zeroize; step*

@[step] theorem scalar.Scalar.Insts.ZeroizeZeroize.zeroize_spec (s : scalar.Scalar) :
    scalar.Scalar.Insts.ZeroizeZeroize.zeroize s ⦃ r =>
      r = { bytes := Array.repeat 32#usize 0#u8 } ⦄ := by
  unfold scalar.Scalar.Insts.ZeroizeZeroize.zeroize; step*

end curve25519_dalek
