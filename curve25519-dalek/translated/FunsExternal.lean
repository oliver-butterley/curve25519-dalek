import Aeneas
import translated.Types
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option linter.style.whitespace false
set_option linter.style.setOption false
set_option linter.style.longLine false

/- You can set the `maxHeartbeats` value with the `-max-heartbeats` CLI option -/
set_option maxHeartbeats 1000000

/- You can set the `maxRecDepth` value with the `-max-recdepth` CLI option -/
set_option maxRecDepth 2048
open curve25519_dalek

/-- [core::array::{impl core::iter::traits::collect::IntoIterator<&'a mut T, core::slice::iter::IterMut<'a, T>> for &'a mut [T; N]}::into_iter]:
    Source: '/rustc/library/core/src/array/mod.rs', lines 376:4-376:40
    Name pattern: [core::array::{core::iter::traits::collect::IntoIterator<&'a mut [@T; @N], &'a mut @T, core::slice::iter::IterMut<'a, @T>>}::into_iter]
    Visibility: public -/
@[rust_fun
  "core::array::{core::iter::traits::collect::IntoIterator<&'a mut [@T; @N], &'a mut @T, core::slice::iter::IterMut<'a, @T>>}::into_iter"]
axiom MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter
  {T : Type} {N : Std.Usize} :
  Array T N → Result ((core.slice.iter.IterMut T) × (core.slice.iter.IterMut
    T → Array T N))

/-- [core::iter::range::{impl core::iter::range::Step for usize}::backward_overflowing]:
    Source: '/rustc/library/core/src/iter/range.rs', lines 357:16-357:78
    Name pattern: [core::iter::range::{core::iter::range::Step<usize>}::backward_overflowing]
    Visibility: public -/
@[rust_fun
  "core::iter::range::{core::iter::range::Step<usize>}::backward_overflowing"]
axiom Usize.Insts.CoreIterRangeStep.backward_overflowing
  : Std.Usize → Std.Usize → Result (Std.Usize × Bool)

/-- [core::iter::range::{impl core::iter::range::Step for usize}::forward_overflowing]:
    Source: '/rustc/library/core/src/iter/range.rs', lines 348:16-348:77
    Name pattern: [core::iter::range::{core::iter::range::Step<usize>}::forward_overflowing]
    Visibility: public -/
@[rust_fun
  "core::iter::range::{core::iter::range::Step<usize>}::forward_overflowing"]
axiom Usize.Insts.CoreIterRangeStep.forward_overflowing
  : Std.Usize → Std.Usize → Result (Std.Usize × Bool)

/-- [core::iter::range::{impl core::iter::range::Step for u32}::backward_overflowing]:
    Source: '/rustc/library/core/src/iter/range.rs', lines 357:16-357:78
    Name pattern: [core::iter::range::{core::iter::range::Step<u32>}::backward_overflowing]
    Visibility: public -/
@[rust_fun
  "core::iter::range::{core::iter::range::Step<u32>}::backward_overflowing"]
axiom U32.Insts.CoreIterRangeStep.backward_overflowing
  : Std.U32 → Std.Usize → Result (Std.U32 × Bool)

/-- [core::iter::range::{impl core::iter::range::Step for u32}::forward_overflowing]:
    Source: '/rustc/library/core/src/iter/range.rs', lines 348:16-348:77
    Name pattern: [core::iter::range::{core::iter::range::Step<u32>}::forward_overflowing]
    Visibility: public -/
@[rust_fun
  "core::iter::range::{core::iter::range::Step<u32>}::forward_overflowing"]
axiom U32.Insts.CoreIterRangeStep.forward_overflowing
  : Std.U32 → Std.Usize → Result (Std.U32 × Bool)

/-- [subtle::{impl core::convert::From<subtle::Choice> for bool}::from]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/subtle-2.6.1/src/lib.rs', lines 153:4-153:35
    Name pattern: [subtle::{core::convert::From<bool, subtle::Choice>}::from]
    Visibility: public -/
@[rust_fun "subtle::{core::convert::From<bool, subtle::Choice>}::from"]
axiom Bool.Insts.CoreConvertFromChoice.from : subtle.Choice → Result Bool

/-- [subtle::{impl core::convert::From<u8> for subtle::Choice}::from]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/subtle-2.6.1/src/lib.rs', lines 238:4-238:32
    Name pattern: [subtle::{core::convert::From<subtle::Choice, u8>}::from]
    Visibility: public -/
@[rust_fun "subtle::{core::convert::From<subtle::Choice, u8>}::from"]
axiom subtle.Choice.Insts.CoreConvertFromU8.from
  : Std.U8 → Result subtle.Choice

/-- [subtle::{impl subtle::ConstantTimeEq for [T]}::ct_eq]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/subtle-2.6.1/src/lib.rs', lines 313:4-313:41
    Name pattern: [subtle::{subtle::ConstantTimeEq<[@T]>}::ct_eq]
    Visibility: public -/
@[rust_fun "subtle::{subtle::ConstantTimeEq<[@T]>}::ct_eq"]
axiom Slice.Insts.SubtleConstantTimeEq.ct_eq
  {T : Type} (ConstantTimeEqInst : subtle.ConstantTimeEq T) :
  Slice T → Slice T → Result subtle.Choice

/-- [subtle::{impl subtle::ConstantTimeEq for u8}::ct_eq]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/subtle-2.6.1/src/lib.rs', lines 348:12-348:51
    Name pattern: [subtle::{subtle::ConstantTimeEq<u8>}::ct_eq]
    Visibility: public -/
@[rust_fun "subtle::{subtle::ConstantTimeEq<u8>}::ct_eq"]
axiom U8.Insts.SubtleConstantTimeEq.ct_eq
  : Std.U8 → Std.U8 → Result subtle.Choice

/-- [subtle::{impl subtle::ConditionallySelectable for u64}::conditional_select]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/subtle-2.6.1/src/lib.rs', lines 513:12-513:77
    Name pattern: [subtle::{subtle::ConditionallySelectable<u64>}::conditional_select]
    Visibility: public -/
@[rust_fun
  "subtle::{subtle::ConditionallySelectable<u64>}::conditional_select"]
axiom U64.Insts.SubtleConditionallySelectable.conditional_select
  : Std.U64 → Std.U64 → subtle.Choice → Result Std.U64

/-- [subtle::{impl subtle::ConditionallySelectable for u32}::conditional_select]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/subtle-2.6.1/src/lib.rs', lines 513:12-513:77
    Name pattern: [subtle::{subtle::ConditionallySelectable<u32>}::conditional_select]
    Visibility: public -/
@[rust_fun
  "subtle::{subtle::ConditionallySelectable<u32>}::conditional_select"]
axiom U32.Insts.SubtleConditionallySelectable.conditional_select
  : Std.U32 → Std.U32 → subtle.Choice → Result Std.U32

/-- [zeroize::{impl zeroize::Zeroize for Z}::zeroize]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/zeroize-1.8.2/src/lib.rs', lines 301:4-301:25
    Name pattern: [zeroize::{zeroize::Zeroize<@Z>}::zeroize]
    Visibility: public -/
@[rust_fun "zeroize::{zeroize::Zeroize<@Z>}::zeroize"]
axiom zeroize.Zeroize.Blanket.zeroize
  {Z : Type} (DefaultIsZeroesInst : zeroize.DefaultIsZeroes Z) : Z → Result Z

/-- [zeroize::{impl zeroize::Zeroize for [Z; N]}::zeroize]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/zeroize-1.8.2/src/lib.rs', lines 373:4-373:25
    Name pattern: [zeroize::{zeroize::Zeroize<[@Z; @N]>}::zeroize]
    Visibility: public -/
@[rust_fun "zeroize::{zeroize::Zeroize<[@Z; @N]>}::zeroize"]
axiom Array.Insts.ZeroizeZeroize.zeroize
  {Z : Type} {N : Std.Usize} (ZeroizeInst : zeroize.Zeroize Z) :
  Array Z N → Result (Array Z N)

