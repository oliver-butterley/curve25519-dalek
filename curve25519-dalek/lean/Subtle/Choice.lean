import Aeneas
import Subtle.Types
import Curve25519Dalek.Types
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

/-! Lean model for `subtle::Choice` methods and trait impls -/

/-- [subtle::{subtle::Choice}::unwrap_u8]:
    Name pattern: [subtle::{subtle::Choice}::unwrap_u8]

    Since `Choice` is modeled as a `U8`, unwrapping is the identity. -/
@[rust_fun "subtle::{subtle::Choice}::unwrap_u8"]
def subtle.Choice.unwrap_u8 (c : subtle.Choice) : Result Std.U8 :=
  ok c

/-- `unwrap_u8` reveals the underlying `u8` of the `Choice` wrapper.
    Docs: subtle-2.6.1/src/lib.rs:122-137. -/
@[step]
theorem subtle.Choice.unwrap_u8_spec (c : subtle.Choice) :
    subtle.Choice.unwrap_u8 c ⦃ (r : Std.U8) => r = c ⦄ := by
  unfold subtle.Choice.unwrap_u8; simp [spec_ok]

/-- [subtle::{impl core::convert::From<subtle::Choice> for bool}::from]:
    Name pattern: [subtle::{core::convert::From<bool, subtle::Choice>}::from]

    Mirrors subtle's `source.0 != 0`. -/
@[rust_fun "subtle::{core::convert::From<bool, subtle::Choice>}::from"]
def Bool.Insts.CoreConvertFromChoice.from (c : subtle.Choice) : Result Bool :=
  ok (c != 0#u8)

/-- `From<Choice> for bool` yields `true` iff the underlying byte was `1` (it is
    `0` or `1` by the `Choice` invariant). Docs: subtle-2.6.1/src/lib.rs:138-155. -/
@[step]
theorem Bool.Insts.CoreConvertFromChoice.from_spec (c : subtle.Choice) :
    Bool.Insts.CoreConvertFromChoice.from c ⦃ (b : Bool) =>
      (c = Choice.zero → b = false) ∧ (c = Choice.one → b = true) ⦄ := by
  unfold Bool.Insts.CoreConvertFromChoice.from
  simp only [spec_ok]
  refine ⟨fun h => ?_, fun h => ?_⟩ <;> subst h <;> simp [Choice.zero, Choice.one]

/-- [subtle::{impl core::convert::From<u8> for subtle::Choice}::from]:
    Name pattern: [subtle::{core::convert::From<subtle::Choice, u8>}::from]

    Wraps a `u8` into a `Choice`; the identity since `Choice = U8`. -/
@[rust_fun "subtle::{core::convert::From<subtle::Choice, u8>}::from"]
def subtle.Choice.Insts.CoreConvertFromU8.from (input : Std.U8) : Result subtle.Choice :=
  ok input

/-- `From<u8> for Choice` wraps the byte unchanged (`Choice(black_box(input))`);
    the caller is required (`debug_assert!`) to pass `0` or `1`.
    Docs: subtle-2.6.1/src/lib.rs:236-245. -/
@[step]
theorem subtle.Choice.Insts.CoreConvertFromU8.from_spec (input : Std.U8) :
    subtle.Choice.Insts.CoreConvertFromU8.from input ⦃ (c : subtle.Choice) => c = input ⦄ := by
  unfold subtle.Choice.Insts.CoreConvertFromU8.from; simp [spec_ok]

/-- [subtle::{impl core::ops::bit::BitAnd for subtle::Choice}::bitand]:
    Name pattern: [subtle::{core::ops::bit::BitAnd<subtle::Choice, subtle::Choice, subtle::Choice>}::bitand] -/
@[rust_fun
  "subtle::{core::ops::bit::BitAnd<subtle::Choice, subtle::Choice, subtle::Choice>}::bitand"]
def subtle.Choice.Insts.CoreOpsBitBitAndChoiceChoice.bitand
  (a : subtle.Choice) (b : subtle.Choice) : Result subtle.Choice :=
  ok (a &&& b)

/-- `Choice`'s `BitAnd` is the bitwise AND of the underlying bytes (a non
    short-circuiting boolean AND for `0`/`1` choices).
    Docs: subtle-2.6.1/src/lib.rs:114-115 and 158-163. -/
@[step]
theorem subtle.Choice.Insts.CoreOpsBitBitAndChoiceChoice.bitand_spec
    (a b : subtle.Choice) :
    subtle.Choice.Insts.CoreOpsBitBitAndChoiceChoice.bitand a b ⦃
      (c : subtle.Choice) => c = a &&& b ⦄ := by
  unfold subtle.Choice.Insts.CoreOpsBitBitAndChoiceChoice.bitand; simp [spec_ok]

/-- [subtle::{impl core::ops::bit::BitOr for subtle::Choice}::bitor]:
    Name pattern: [subtle::{core::ops::bit::BitOr<subtle::Choice, subtle::Choice, subtle::Choice>}::bitor] -/
@[rust_fun
  "subtle::{core::ops::bit::BitOr<subtle::Choice, subtle::Choice, subtle::Choice>}::bitor"]
def subtle.Choice.Insts.CoreOpsBitBitOrChoiceChoice.bitor
  (a : subtle.Choice) (b : subtle.Choice) : Result subtle.Choice :=
  ok (a ||| b)

/-- `Choice`'s `BitOr` is the bitwise OR of the underlying bytes (a non
    short-circuiting boolean OR for `0`/`1` choices).
    Docs: subtle-2.6.1/src/lib.rs:114-115 and 174-179. -/
@[step]
theorem subtle.Choice.Insts.CoreOpsBitBitOrChoiceChoice.bitor_spec
    (a b : subtle.Choice) :
    subtle.Choice.Insts.CoreOpsBitBitOrChoiceChoice.bitor a b ⦃
      (c : subtle.Choice) => c = a ||| b ⦄ := by
  unfold subtle.Choice.Insts.CoreOpsBitBitOrChoiceChoice.bitor; simp [spec_ok]

/-- [subtle::{impl core::ops::bit::Not for subtle::Choice}::not]:
    Name pattern: [subtle::{core::ops::bit::Not<subtle::Choice, subtle::Choice>}::not]

    Mirrors subtle's `Choice(1u8 & !self.0)`. -/
@[rust_fun
  "subtle::{core::ops::bit::Not<subtle::Choice, subtle::Choice>}::not"]
def subtle.Choice.Insts.CoreOpsBitNotChoice.not (c : subtle.Choice) : Result subtle.Choice :=
  ok (1#u8 &&& (~~~c))

/-- `Choice`'s `Not` complements the low bit only: `Choice(1u8 & !self.0)` (so it
    maps `0 ↔ 1` on valid choices). Docs: subtle-2.6.1/src/lib.rs:114-115 and 205-211. -/
@[step]
theorem subtle.Choice.Insts.CoreOpsBitNotChoice.not_spec (c : subtle.Choice) :
    subtle.Choice.Insts.CoreOpsBitNotChoice.not c ⦃
      (r : subtle.Choice) => r = 1#u8 &&& (~~~c) ⦄ := by
  unfold subtle.Choice.Insts.CoreOpsBitNotChoice.not; simp [spec_ok]
