import Aeneas
import Subtle.Types
import translated.Types
open Aeneas Aeneas.Std Result ControlFlow Error
open Aeneas.Std.WP
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option linter.style.whitespace false
set_option linter.style.setOption false
set_option linter.style.longLine false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
open curve25519_dalek

/-- [subtle::{impl subtle::ConstantTimeEq for u8}::ct_eq]:
    Name pattern: [subtle::{subtle::ConstantTimeEq<u8>}::ct_eq] -/
@[rust_fun "subtle::{subtle::ConstantTimeEq<u8>}::ct_eq"]
def U8.Insts.SubtleConstantTimeEq.ct_eq (a : Std.U8) (b : Std.U8) : Result subtle.Choice :=
  ok (if a = b then Choice.one else Choice.zero)

/-- `ct_eq` returns `Choice(1)` if the operands are equal and `Choice(0)`
    otherwise. Docs: subtle-2.6.1/src/lib.rs:261-273. -/
@[step]
theorem U8.Insts.SubtleConstantTimeEq.ct_eq_spec (a b : Std.U8) :
    U8.Insts.SubtleConstantTimeEq.ct_eq a b ⦃
      (c : subtle.Choice) => c = if a = b then Choice.one else Choice.zero ⦄ := by
  unfold U8.Insts.SubtleConstantTimeEq.ct_eq; simp [spec_ok]

/-- [subtle::{impl subtle::ConstantTimeEq for u16}::ct_eq]:
    Name pattern: [subtle::{subtle::ConstantTimeEq<u16>}::ct_eq] -/
@[rust_fun "subtle::{subtle::ConstantTimeEq<u16>}::ct_eq"]
def U16.Insts.SubtleConstantTimeEq.ct_eq (a : Std.U16) (b : Std.U16) : Result subtle.Choice :=
  ok (if a = b then Choice.one else Choice.zero)

/-- `ct_eq` returns `Choice(1)` if the operands are equal and `Choice(0)`
    otherwise. Docs: subtle-2.6.1/src/lib.rs:261-273. -/
@[step]
theorem U16.Insts.SubtleConstantTimeEq.ct_eq_spec (a b : Std.U16) :
    U16.Insts.SubtleConstantTimeEq.ct_eq a b ⦃
      (c : subtle.Choice) => c = if a = b then Choice.one else Choice.zero ⦄ := by
  unfold U16.Insts.SubtleConstantTimeEq.ct_eq; simp [spec_ok]

open scoped Classical in
/-- [subtle::{impl subtle::ConstantTimeEq for [T]}::ct_eq]:
    Name pattern: [subtle::{subtle::ConstantTimeEq<[@T]>}::ct_eq]

    Constant-time equality for slices: equal lengths and element-wise equal. -/
@[rust_fun "subtle::{subtle::ConstantTimeEq<[@T]>}::ct_eq"]
noncomputable def Slice.Insts.SubtleConstantTimeEq.ct_eq
  {T : Type} (_ConstantTimeEqInst : subtle.ConstantTimeEq T) :
  Slice T → Slice T → Result subtle.Choice :=
  fun a b => ok (if a = b then Choice.one else Choice.zero)

open scoped Classical in
/-- Slice `ct_eq` returns `Choice(1)` iff the slices are equal: it short-circuits
    to `Choice(0)` on differing lengths, otherwise ANDs the element-wise
    `ct_eq`s (which are `Choice(1)` iff the elements are equal).
    Docs: subtle-2.6.1/src/lib.rs:290-335. -/
@[step]
theorem Slice.Insts.SubtleConstantTimeEq.ct_eq_spec
    {T : Type} (ConstantTimeEqInst : subtle.ConstantTimeEq T) (a b : Slice T) :
    Slice.Insts.SubtleConstantTimeEq.ct_eq ConstantTimeEqInst a b ⦃
      (c : subtle.Choice) => c = if a = b then Choice.one else Choice.zero ⦄ := by
  unfold Slice.Insts.SubtleConstantTimeEq.ct_eq; simp [spec_ok]
