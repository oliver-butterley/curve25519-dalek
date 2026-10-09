-- [curve25519_dalek]: external functions.
module
public import Aeneas
public import Curve25519Dalek.Types
public import Subtle
public import Zeroize
@[expose] public section
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

/-- [core::array::from_fn]:
    Source: '/rustc/library/core/src/array/mod.rs', lines 110:0-112:52
    Name pattern: [core::array::from_fn]
    Visibility: public -/
@[rust_fun "core::array::from_fn"]
axiom core.array.from_fn
  {T : Type} {F : Type} (N : Std.Usize) (opsfunctionFnMutFTupleUsizeTInst :
  core.ops.function.FnMut F Std.Usize T) :
  F → Result (Array T N)

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

/-- [core::num::{usize}::div_ceil]:
    Source: '/rustc/library/core/src/num/uint_macros.rs', lines 3787:8-3787:54
    Name pattern: [core::num::{usize}::div_ceil]
    Visibility: public -/
@[rust_fun "core::num::{usize}::div_ceil"]
axiom core.num.Usize.div_ceil : Std.Usize → Std.Usize → Result Std.Usize

/-- [core::result::{core::result::Result<T, E>}::map]:
    Source: '/rustc/library/core/src/result.rs', lines 832:4-834:53
    Name pattern: [core::result::{core::result::Result<@T, @E>}::map]
    Visibility: public -/
@[rust_fun "core::result::{core::result::Result<@T, @E>}::map"]
axiom core.result.Result.map
  {T : Type} {E : Type} {U : Type} {F : Type} (opsfunctionFnOnceFTupleTUInst :
  core.ops.function.FnOnce F T U) :
  core.result.Result T E → F → Result (core.result.Result U E)

/-- [alloc::vec::{alloc::vec::Vec<T>}::is_empty]:
    Source: '/rustc/library/alloc/src/vec/mod.rs', lines 3125:4-3125:40
    Name pattern: [alloc::vec::{alloc::vec::Vec<@T>}::is_empty]
    Visibility: public -/
@[rust_fun "alloc::vec::{alloc::vec::Vec<@T>}::is_empty"]
axiom alloc.vec.Vec.is_empty
  {T : Type} (A : Type) : alloc.vec.Vec T → Result Bool

/-- [curve25519_dalek::backend::serial::u32::constants::ED25519_BASEPOINT_TABLE_INNER_DOC_HIDDEN]
    Source: 'curve25519-dalek/src/backend/serial/u32/constants.rs', lines 300:0-3949:3 -/
axiom backend.serial.u32.constants.ED25519_BASEPOINT_TABLE_INNER_DOC_HIDDEN
  : Result edwards.EdwardsBasepointTable.«i686-unknown-linux-gnu»

/-- [curve25519_dalek::backend::serial::u64::constants::ED25519_BASEPOINT_TABLE_INNER_DOC_HIDDEN]
    Source: 'curve25519-dalek/src/backend/serial/u64/constants.rs', lines 381:0-6334:3 -/
axiom backend.serial.u64.constants.ED25519_BASEPOINT_TABLE_INNER_DOC_HIDDEN
  : Result edwards.EdwardsBasepointTable.«x86_64-unknown-linux-gnu»

/-- [curve25519_dalek::constants::RISTRETTO_BASEPOINT_TABLE::i686-unknown-linux-gnu]
    Source: 'curve25519-dalek/src/constants.rs', lines 85:0-89:2
    Visibility: public -/
axiom constants.RISTRETTO_BASEPOINT_TABLE.«i686-unknown-linux-gnu»
  : Result ristretto.RistrettoBasepointTable.«i686-unknown-linux-gnu»

/-- [curve25519_dalek::constants::RISTRETTO_BASEPOINT_TABLE::x86_64-unknown-linux-gnu]
    Source: 'curve25519-dalek/src/constants.rs', lines 85:0-89:2
    Visibility: public -/
axiom constants.RISTRETTO_BASEPOINT_TABLE.«x86_64-unknown-linux-gnu»
  : Result ristretto.RistrettoBasepointTable.«x86_64-unknown-linux-gnu»

/-- [core::borrow::{impl core::borrow::Borrow<T> for T}::borrow]:
    Source: '/rustc/library/core/src/borrow.rs', lines 214:4-214:26
    Name pattern: [core::borrow::{core::borrow::Borrow<@T, @T>}::borrow]
    Visibility: public -/
@[rust_fun "core::borrow::{core::borrow::Borrow<@T, @T>}::borrow"]
axiom core.borrow.Borrow.Blanket.borrow {T : Type} : T → Result T
