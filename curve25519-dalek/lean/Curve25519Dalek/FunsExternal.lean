-- [curve25519_dalek]: external functions.
module
public import Aeneas
public import Curve25519Dalek.Types
public import Subtle
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

/-- [zeroize::{impl zeroize::Zeroize for core::slice::iter::IterMut<'_0, Z>}::zeroize]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/zeroize-1.8.2/src/lib.rs', lines 385:4-385:25
    Name pattern: [zeroize::{zeroize::Zeroize<core::slice::iter::IterMut<'0, @Z>>}::zeroize]
    Visibility: public -/
@[rust_fun
  "zeroize::{zeroize::Zeroize<core::slice::iter::IterMut<'0, @Z>>}::zeroize"]
axiom core.slice.iter.IterMut.Insts.ZeroizeZeroize.zeroize
  {Z : Type} (ZeroizeInst : zeroize.Zeroize Z) :
  core.slice.iter.IterMut Z → Result ((core.slice.iter.IterMut Z) ×
    (core.slice.iter.IterMut Z → core.slice.iter.IterMut Z))

/-- [curve25519_dalek::backend::serial::scalar_mul::pippenger::{impl curve25519_dalek::traits::VartimeMultiscalarMul<curve25519_dalek::edwards::EdwardsPoint::x86_64-unknown-linux-gnu> for curve25519_dalek::backend::serial::scalar_mul::pippenger::Pippenger}::optional_multiscalar_mul]:
    Source: 'curve25519-dalek/src/backend/serial/scalar_mul/pippenger.rs', lines 67:4-176:5
    Visibility: public -/
axiom
  backend.serial.scalar_mul.pippenger.Pippenger.Insts.«Curve25519_dalekTraitsVartimeMultiscalarMulEdwardsPointx86_64-unknown-linux-gnu».optional_multiscalar_mul
  {I : Type} {J : Type} {Clause0_Item : Type} {Clause0_IntoIter : Type}
  {Clause2_IntoIter : Type} (coreitertraitscollectIntoIteratorInst :
  core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
  (coreborrowBorrowClause0_ItemScalarInst : core.borrow.Borrow Clause0_Item
  scalar.Scalar)
  («coreitertraitscollectIntoIteratorJOptionEdwardsPointx86_64-unknown-linux-gnuClause2_IntoIterInst»
  : core.iter.traits.collect.IntoIterator J (Option
  edwards.EdwardsPoint.«x86_64-unknown-linux-gnu») Clause2_IntoIter) :
  I → J → Result (Option edwards.EdwardsPoint.«x86_64-unknown-linux-gnu»)

/-- [curve25519_dalek::backend::serial::scalar_mul::pippenger::{impl curve25519_dalek::traits::VartimeMultiscalarMul<curve25519_dalek::edwards::EdwardsPoint::i686-unknown-linux-gnu> for curve25519_dalek::backend::serial::scalar_mul::pippenger::Pippenger}::optional_multiscalar_mul]:
    Source: 'curve25519-dalek/src/backend/serial/scalar_mul/pippenger.rs', lines 67:4-176:5
    Visibility: public -/
axiom
  backend.serial.scalar_mul.pippenger.Pippenger.Insts.«Curve25519_dalekTraitsVartimeMultiscalarMulEdwardsPointi686-unknown-linux-gnu».optional_multiscalar_mul
  {I : Type} {J : Type} {Clause0_Item : Type} {Clause0_IntoIter : Type}
  {Clause2_IntoIter : Type} (coreitertraitscollectIntoIteratorInst :
  core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
  (coreborrowBorrowClause0_ItemScalarInst : core.borrow.Borrow Clause0_Item
  scalar.Scalar)
  («coreitertraitscollectIntoIteratorJOptionEdwardsPointi686-unknown-linux-gnuClause2_IntoIterInst»
  : core.iter.traits.collect.IntoIterator J (Option
  edwards.EdwardsPoint.«i686-unknown-linux-gnu») Clause2_IntoIter) :
  I → J → Result (Option edwards.EdwardsPoint.«i686-unknown-linux-gnu»)

/-- [curve25519_dalek::backend::serial::scalar_mul::precomputed_straus::{impl curve25519_dalek::traits::VartimePrecomputedMultiscalarMul<curve25519_dalek::edwards::EdwardsPoint::x86_64-unknown-linux-gnu> for curve25519_dalek::backend::serial::scalar_mul::precomputed_straus::VartimePrecomputedStraus::x86_64-unknown-linux-gnu}::optional_mixed_multiscalar_mul]:
    Source: 'curve25519-dalek/src/backend/serial/scalar_mul/precomputed_straus.rs', lines 57:4-127:5
    Visibility: public -/
axiom
  backend.serial.scalar_mul.precomputed_straus.VartimePrecomputedStraus.«x86_64-unknown-linux-gnu».Insts.«Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPointx86_64-unknown-linux-gnu».optional_mixed_multiscalar_mul
  {I : Type} {J : Type} {K : Type} {Clause0_Item : Type} {Clause0_IntoIter :
  Type} {Clause2_Item : Type} {Clause2_IntoIter : Type} {Clause4_IntoIter :
  Type} (coreitertraitscollectIntoIteratorInst :
  core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
  (coreborrowBorrowClause0_ItemScalarInst : core.borrow.Borrow Clause0_Item
  scalar.Scalar) (coreitertraitscollectIntoIteratorInst1 :
  core.iter.traits.collect.IntoIterator J Clause2_Item Clause2_IntoIter)
  (coreborrowBorrowClause2_ItemScalarInst : core.borrow.Borrow Clause2_Item
  scalar.Scalar)
  («coreitertraitscollectIntoIteratorKOptionEdwardsPointx86_64-unknown-linux-gnuClause4_IntoIterInst»
  : core.iter.traits.collect.IntoIterator K (Option
  edwards.EdwardsPoint.«x86_64-unknown-linux-gnu») Clause4_IntoIter) :
  backend.serial.scalar_mul.precomputed_straus.VartimePrecomputedStraus.«x86_64-unknown-linux-gnu»
    → I → J → K → Result (Option
    edwards.EdwardsPoint.«x86_64-unknown-linux-gnu»)

/-- [curve25519_dalek::backend::serial::scalar_mul::precomputed_straus::{impl curve25519_dalek::traits::VartimePrecomputedMultiscalarMul<curve25519_dalek::edwards::EdwardsPoint::x86_64-unknown-linux-gnu> for curve25519_dalek::backend::serial::scalar_mul::precomputed_straus::VartimePrecomputedStraus::x86_64-unknown-linux-gnu}::new]:
    Source: 'curve25519-dalek/src/backend/serial/scalar_mul/precomputed_straus.rs', lines 36:4-47:5
    Visibility: public -/
axiom
  backend.serial.scalar_mul.precomputed_straus.VartimePrecomputedStraus.«x86_64-unknown-linux-gnu».Insts.«Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPointx86_64-unknown-linux-gnu».new
  {I : Type} {Clause0_Item : Type} {Clause0_IntoIter : Type}
  (coreitertraitscollectIntoIteratorInst :
  core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
  («coreborrowBorrowClause0_ItemEdwardsPointx86_64-unknown-linux-gnuInst» :
  core.borrow.Borrow Clause0_Item
  edwards.EdwardsPoint.«x86_64-unknown-linux-gnu») :
  I → Result
    backend.serial.scalar_mul.precomputed_straus.VartimePrecomputedStraus.«x86_64-unknown-linux-gnu»

/-- [curve25519_dalek::backend::serial::scalar_mul::precomputed_straus::{impl curve25519_dalek::traits::VartimePrecomputedMultiscalarMul<curve25519_dalek::edwards::EdwardsPoint::i686-unknown-linux-gnu> for curve25519_dalek::backend::serial::scalar_mul::precomputed_straus::VartimePrecomputedStraus::i686-unknown-linux-gnu}::optional_mixed_multiscalar_mul]:
    Source: 'curve25519-dalek/src/backend/serial/scalar_mul/precomputed_straus.rs', lines 57:4-127:5
    Visibility: public -/
axiom
  backend.serial.scalar_mul.precomputed_straus.VartimePrecomputedStraus.«i686-unknown-linux-gnu».Insts.«Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPointi686-unknown-linux-gnu».optional_mixed_multiscalar_mul
  {I : Type} {J : Type} {K : Type} {Clause0_Item : Type} {Clause0_IntoIter :
  Type} {Clause2_Item : Type} {Clause2_IntoIter : Type} {Clause4_IntoIter :
  Type} (coreitertraitscollectIntoIteratorInst :
  core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
  (coreborrowBorrowClause0_ItemScalarInst : core.borrow.Borrow Clause0_Item
  scalar.Scalar) (coreitertraitscollectIntoIteratorInst1 :
  core.iter.traits.collect.IntoIterator J Clause2_Item Clause2_IntoIter)
  (coreborrowBorrowClause2_ItemScalarInst : core.borrow.Borrow Clause2_Item
  scalar.Scalar)
  («coreitertraitscollectIntoIteratorKOptionEdwardsPointi686-unknown-linux-gnuClause4_IntoIterInst»
  : core.iter.traits.collect.IntoIterator K (Option
  edwards.EdwardsPoint.«i686-unknown-linux-gnu») Clause4_IntoIter) :
  backend.serial.scalar_mul.precomputed_straus.VartimePrecomputedStraus.«i686-unknown-linux-gnu»
    → I → J → K → Result (Option
    edwards.EdwardsPoint.«i686-unknown-linux-gnu»)

/-- [curve25519_dalek::backend::serial::scalar_mul::precomputed_straus::{impl curve25519_dalek::traits::VartimePrecomputedMultiscalarMul<curve25519_dalek::edwards::EdwardsPoint::i686-unknown-linux-gnu> for curve25519_dalek::backend::serial::scalar_mul::precomputed_straus::VartimePrecomputedStraus::i686-unknown-linux-gnu}::new]:
    Source: 'curve25519-dalek/src/backend/serial/scalar_mul/precomputed_straus.rs', lines 36:4-47:5
    Visibility: public -/
axiom
  backend.serial.scalar_mul.precomputed_straus.VartimePrecomputedStraus.«i686-unknown-linux-gnu».Insts.«Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPointi686-unknown-linux-gnu».new
  {I : Type} {Clause0_Item : Type} {Clause0_IntoIter : Type}
  (coreitertraitscollectIntoIteratorInst :
  core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
  («coreborrowBorrowClause0_ItemEdwardsPointi686-unknown-linux-gnuInst» :
  core.borrow.Borrow Clause0_Item
  edwards.EdwardsPoint.«i686-unknown-linux-gnu») :
  I → Result
    backend.serial.scalar_mul.precomputed_straus.VartimePrecomputedStraus.«i686-unknown-linux-gnu»

/-- [curve25519_dalek::backend::serial::scalar_mul::straus::{impl curve25519_dalek::traits::MultiscalarMul<curve25519_dalek::edwards::EdwardsPoint::x86_64-unknown-linux-gnu> for curve25519_dalek::backend::serial::scalar_mul::straus::Straus}::multiscalar_mul]:
    Source: 'curve25519-dalek/src/backend/serial/scalar_mul/straus.rs', lines 103:4-144:5
    Visibility: public -/
axiom
  backend.serial.scalar_mul.straus.Straus.Insts.«Curve25519_dalekTraitsMultiscalarMulEdwardsPointx86_64-unknown-linux-gnu».multiscalar_mul
  {I : Type} {J : Type} {Clause0_Item : Type} {Clause0_IntoIter : Type}
  {Clause2_Item : Type} {Clause2_IntoIter : Type}
  (coreitertraitscollectIntoIteratorInst :
  core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
  (coreborrowBorrowClause0_ItemScalarInst : core.borrow.Borrow Clause0_Item
  scalar.Scalar) (coreitertraitscollectIntoIteratorInst1 :
  core.iter.traits.collect.IntoIterator J Clause2_Item Clause2_IntoIter)
  («coreborrowBorrowClause2_ItemEdwardsPointx86_64-unknown-linux-gnuInst» :
  core.borrow.Borrow Clause2_Item
  edwards.EdwardsPoint.«x86_64-unknown-linux-gnu») :
  I → J → Result edwards.EdwardsPoint.«x86_64-unknown-linux-gnu»

/-- [curve25519_dalek::backend::serial::scalar_mul::straus::{impl curve25519_dalek::traits::MultiscalarMul<curve25519_dalek::edwards::EdwardsPoint::i686-unknown-linux-gnu> for curve25519_dalek::backend::serial::scalar_mul::straus::Straus}::multiscalar_mul]:
    Source: 'curve25519-dalek/src/backend/serial/scalar_mul/straus.rs', lines 103:4-144:5
    Visibility: public -/
axiom
  backend.serial.scalar_mul.straus.Straus.Insts.«Curve25519_dalekTraitsMultiscalarMulEdwardsPointi686-unknown-linux-gnu».multiscalar_mul
  {I : Type} {J : Type} {Clause0_Item : Type} {Clause0_IntoIter : Type}
  {Clause2_Item : Type} {Clause2_IntoIter : Type}
  (coreitertraitscollectIntoIteratorInst :
  core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
  (coreborrowBorrowClause0_ItemScalarInst : core.borrow.Borrow Clause0_Item
  scalar.Scalar) (coreitertraitscollectIntoIteratorInst1 :
  core.iter.traits.collect.IntoIterator J Clause2_Item Clause2_IntoIter)
  («coreborrowBorrowClause2_ItemEdwardsPointi686-unknown-linux-gnuInst» :
  core.borrow.Borrow Clause2_Item
  edwards.EdwardsPoint.«i686-unknown-linux-gnu») :
  I → J → Result edwards.EdwardsPoint.«i686-unknown-linux-gnu»

/-- [curve25519_dalek::backend::serial::scalar_mul::straus::{impl curve25519_dalek::traits::VartimeMultiscalarMul<curve25519_dalek::edwards::EdwardsPoint::x86_64-unknown-linux-gnu> for curve25519_dalek::backend::serial::scalar_mul::straus::Straus}::optional_multiscalar_mul]:
    Source: 'curve25519-dalek/src/backend/serial/scalar_mul/straus.rs', lines 159:4-200:5
    Visibility: public -/
axiom
  backend.serial.scalar_mul.straus.Straus.Insts.«Curve25519_dalekTraitsVartimeMultiscalarMulEdwardsPointx86_64-unknown-linux-gnu».optional_multiscalar_mul
  {I : Type} {J : Type} {Clause0_Item : Type} {Clause0_IntoIter : Type}
  {Clause2_IntoIter : Type} (coreitertraitscollectIntoIteratorInst :
  core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
  (coreborrowBorrowClause0_ItemScalarInst : core.borrow.Borrow Clause0_Item
  scalar.Scalar)
  («coreitertraitscollectIntoIteratorJOptionEdwardsPointx86_64-unknown-linux-gnuClause2_IntoIterInst»
  : core.iter.traits.collect.IntoIterator J (Option
  edwards.EdwardsPoint.«x86_64-unknown-linux-gnu») Clause2_IntoIter) :
  I → J → Result (Option edwards.EdwardsPoint.«x86_64-unknown-linux-gnu»)

/-- [curve25519_dalek::backend::serial::scalar_mul::straus::{impl curve25519_dalek::traits::VartimeMultiscalarMul<curve25519_dalek::edwards::EdwardsPoint::i686-unknown-linux-gnu> for curve25519_dalek::backend::serial::scalar_mul::straus::Straus}::optional_multiscalar_mul]:
    Source: 'curve25519-dalek/src/backend/serial/scalar_mul/straus.rs', lines 159:4-200:5
    Visibility: public -/
axiom
  backend.serial.scalar_mul.straus.Straus.Insts.«Curve25519_dalekTraitsVartimeMultiscalarMulEdwardsPointi686-unknown-linux-gnu».optional_multiscalar_mul
  {I : Type} {J : Type} {Clause0_Item : Type} {Clause0_IntoIter : Type}
  {Clause2_IntoIter : Type} (coreitertraitscollectIntoIteratorInst :
  core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
  (coreborrowBorrowClause0_ItemScalarInst : core.borrow.Borrow Clause0_Item
  scalar.Scalar)
  («coreitertraitscollectIntoIteratorJOptionEdwardsPointi686-unknown-linux-gnuClause2_IntoIterInst»
  : core.iter.traits.collect.IntoIterator J (Option
  edwards.EdwardsPoint.«i686-unknown-linux-gnu») Clause2_IntoIter) :
  I → J → Result (Option edwards.EdwardsPoint.«i686-unknown-linux-gnu»)

/-- [curve25519_dalek::edwards::{impl core::iter::traits::accum::Sum<T> for curve25519_dalek::edwards::EdwardsPoint::x86_64-unknown-linux-gnu}::sum]:
    Source: 'curve25519-dalek/src/edwards.rs', lines 865:4-870:5
    Visibility: public -/
axiom
  edwards.EdwardsPoint.«x86_64-unknown-linux-gnu».Insts.CoreIterTraitsAccumSum.sum
  {T : Type} {I : Type}
  («coreborrowBorrowTEdwardsPointx86_64-unknown-linux-gnuInst» :
  core.borrow.Borrow T edwards.EdwardsPoint.«x86_64-unknown-linux-gnu»)
  (coreitertraitsiteratorIteratorInst : core.iter.traits.iterator.Iterator I T)
  :
  I → Result edwards.EdwardsPoint.«x86_64-unknown-linux-gnu»

/-- [curve25519_dalek::edwards::{impl core::iter::traits::accum::Sum<T> for curve25519_dalek::edwards::EdwardsPoint::i686-unknown-linux-gnu}::sum]:
    Source: 'curve25519-dalek/src/edwards.rs', lines 865:4-870:5
    Visibility: public -/
axiom
  edwards.EdwardsPoint.«i686-unknown-linux-gnu».Insts.CoreIterTraitsAccumSum.sum
  {T : Type} {I : Type}
  («coreborrowBorrowTEdwardsPointi686-unknown-linux-gnuInst» :
  core.borrow.Borrow T edwards.EdwardsPoint.«i686-unknown-linux-gnu»)
  (coreitertraitsiteratorIteratorInst : core.iter.traits.iterator.Iterator I T)
  :
  I → Result edwards.EdwardsPoint.«i686-unknown-linux-gnu»

/-- [curve25519_dalek::edwards::{impl curve25519_dalek::traits::MultiscalarMul<curve25519_dalek::edwards::EdwardsPoint::x86_64-unknown-linux-gnu> for curve25519_dalek::edwards::EdwardsPoint::x86_64-unknown-linux-gnu}::multiscalar_mul]:
    Source: 'curve25519-dalek/src/edwards.rs', lines 994:4-1019:5
    Visibility: public -/
axiom
  edwards.EdwardsPoint.«x86_64-unknown-linux-gnu».Insts.«Curve25519_dalekTraitsMultiscalarMulEdwardsPointx86_64-unknown-linux-gnu».multiscalar_mul
  {I : Type} {J : Type} {Clause0_Item : Type} {Clause0_IntoIter : Type}
  {Clause2_Item : Type} {Clause2_IntoIter : Type}
  (coreitertraitscollectIntoIteratorInst :
  core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
  (coreborrowBorrowClause0_ItemScalarInst : core.borrow.Borrow Clause0_Item
  scalar.Scalar) (coreitertraitscollectIntoIteratorInst1 :
  core.iter.traits.collect.IntoIterator J Clause2_Item Clause2_IntoIter)
  («coreborrowBorrowClause2_ItemEdwardsPointx86_64-unknown-linux-gnuInst» :
  core.borrow.Borrow Clause2_Item
  edwards.EdwardsPoint.«x86_64-unknown-linux-gnu») :
  I → J → Result edwards.EdwardsPoint.«x86_64-unknown-linux-gnu»

/-- [curve25519_dalek::edwards::{impl curve25519_dalek::traits::MultiscalarMul<curve25519_dalek::edwards::EdwardsPoint::i686-unknown-linux-gnu> for curve25519_dalek::edwards::EdwardsPoint::i686-unknown-linux-gnu}::multiscalar_mul]:
    Source: 'curve25519-dalek/src/edwards.rs', lines 994:4-1019:5
    Visibility: public -/
axiom
  edwards.EdwardsPoint.«i686-unknown-linux-gnu».Insts.«Curve25519_dalekTraitsMultiscalarMulEdwardsPointi686-unknown-linux-gnu».multiscalar_mul
  {I : Type} {J : Type} {Clause0_Item : Type} {Clause0_IntoIter : Type}
  {Clause2_Item : Type} {Clause2_IntoIter : Type}
  (coreitertraitscollectIntoIteratorInst :
  core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
  (coreborrowBorrowClause0_ItemScalarInst : core.borrow.Borrow Clause0_Item
  scalar.Scalar) (coreitertraitscollectIntoIteratorInst1 :
  core.iter.traits.collect.IntoIterator J Clause2_Item Clause2_IntoIter)
  («coreborrowBorrowClause2_ItemEdwardsPointi686-unknown-linux-gnuInst» :
  core.borrow.Borrow Clause2_Item
  edwards.EdwardsPoint.«i686-unknown-linux-gnu») :
  I → J → Result edwards.EdwardsPoint.«i686-unknown-linux-gnu»

/-- [curve25519_dalek::edwards::{impl curve25519_dalek::traits::VartimeMultiscalarMul<curve25519_dalek::edwards::EdwardsPoint::x86_64-unknown-linux-gnu> for curve25519_dalek::edwards::EdwardsPoint::x86_64-unknown-linux-gnu}::optional_multiscalar_mul]:
    Source: 'curve25519-dalek/src/edwards.rs', lines 1026:4-1054:5
    Visibility: public -/
axiom
  edwards.EdwardsPoint.«x86_64-unknown-linux-gnu».Insts.«Curve25519_dalekTraitsVartimeMultiscalarMulEdwardsPointx86_64-unknown-linux-gnu».optional_multiscalar_mul
  {I : Type} {J : Type} {Clause0_Item : Type} {Clause0_IntoIter : Type}
  {Clause2_IntoIter : Type} (coreitertraitscollectIntoIteratorInst :
  core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
  (coreborrowBorrowClause0_ItemScalarInst : core.borrow.Borrow Clause0_Item
  scalar.Scalar)
  («coreitertraitscollectIntoIteratorJOptionEdwardsPointx86_64-unknown-linux-gnuClause2_IntoIterInst»
  : core.iter.traits.collect.IntoIterator J (Option
  edwards.EdwardsPoint.«x86_64-unknown-linux-gnu») Clause2_IntoIter) :
  I → J → Result (Option edwards.EdwardsPoint.«x86_64-unknown-linux-gnu»)

/-- [curve25519_dalek::edwards::{impl curve25519_dalek::traits::VartimeMultiscalarMul<curve25519_dalek::edwards::EdwardsPoint::i686-unknown-linux-gnu> for curve25519_dalek::edwards::EdwardsPoint::i686-unknown-linux-gnu}::optional_multiscalar_mul]:
    Source: 'curve25519-dalek/src/edwards.rs', lines 1026:4-1054:5
    Visibility: public -/
axiom
  edwards.EdwardsPoint.«i686-unknown-linux-gnu».Insts.«Curve25519_dalekTraitsVartimeMultiscalarMulEdwardsPointi686-unknown-linux-gnu».optional_multiscalar_mul
  {I : Type} {J : Type} {Clause0_Item : Type} {Clause0_IntoIter : Type}
  {Clause2_IntoIter : Type} (coreitertraitscollectIntoIteratorInst :
  core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
  (coreborrowBorrowClause0_ItemScalarInst : core.borrow.Borrow Clause0_Item
  scalar.Scalar)
  («coreitertraitscollectIntoIteratorJOptionEdwardsPointi686-unknown-linux-gnuClause2_IntoIterInst»
  : core.iter.traits.collect.IntoIterator J (Option
  edwards.EdwardsPoint.«i686-unknown-linux-gnu») Clause2_IntoIter) :
  I → J → Result (Option edwards.EdwardsPoint.«i686-unknown-linux-gnu»)

/-- [curve25519_dalek::edwards::{impl curve25519_dalek::traits::VartimePrecomputedMultiscalarMul<curve25519_dalek::edwards::EdwardsPoint::x86_64-unknown-linux-gnu> for curve25519_dalek::edwards::VartimeEdwardsPrecomputation::x86_64-unknown-linux-gnu}::optional_mixed_multiscalar_mul]:
    Source: 'curve25519-dalek/src/edwards.rs', lines 1084:4-1099:5
    Visibility: public -/
axiom
  edwards.VartimeEdwardsPrecomputation.«x86_64-unknown-linux-gnu».Insts.«Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPointx86_64-unknown-linux-gnu».optional_mixed_multiscalar_mul
  {I : Type} {J : Type} {K : Type} {Clause0_Item : Type} {Clause0_IntoIter :
  Type} {Clause2_Item : Type} {Clause2_IntoIter : Type} {Clause4_IntoIter :
  Type} (coreitertraitscollectIntoIteratorInst :
  core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
  (coreborrowBorrowClause0_ItemScalarInst : core.borrow.Borrow Clause0_Item
  scalar.Scalar) (coreitertraitscollectIntoIteratorInst1 :
  core.iter.traits.collect.IntoIterator J Clause2_Item Clause2_IntoIter)
  (coreborrowBorrowClause2_ItemScalarInst : core.borrow.Borrow Clause2_Item
  scalar.Scalar)
  («coreitertraitscollectIntoIteratorKOptionEdwardsPointx86_64-unknown-linux-gnuClause4_IntoIterInst»
  : core.iter.traits.collect.IntoIterator K (Option
  edwards.EdwardsPoint.«x86_64-unknown-linux-gnu») Clause4_IntoIter) :
  edwards.VartimeEdwardsPrecomputation.«x86_64-unknown-linux-gnu» → I → J
    → K → Result (Option edwards.EdwardsPoint.«x86_64-unknown-linux-gnu»)

/-- [curve25519_dalek::edwards::{impl curve25519_dalek::traits::VartimePrecomputedMultiscalarMul<curve25519_dalek::edwards::EdwardsPoint::x86_64-unknown-linux-gnu> for curve25519_dalek::edwards::VartimeEdwardsPrecomputation::x86_64-unknown-linux-gnu}::new]:
    Source: 'curve25519-dalek/src/edwards.rs', lines 1068:4-1074:5
    Visibility: public -/
axiom
  edwards.VartimeEdwardsPrecomputation.«x86_64-unknown-linux-gnu».Insts.«Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPointx86_64-unknown-linux-gnu».new
  {I : Type} {Clause0_Item : Type} {Clause0_IntoIter : Type}
  (coreitertraitscollectIntoIteratorInst :
  core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
  («coreborrowBorrowClause0_ItemEdwardsPointx86_64-unknown-linux-gnuInst» :
  core.borrow.Borrow Clause0_Item
  edwards.EdwardsPoint.«x86_64-unknown-linux-gnu») :
  I → Result
    edwards.VartimeEdwardsPrecomputation.«x86_64-unknown-linux-gnu»

/-- [curve25519_dalek::edwards::{impl curve25519_dalek::traits::VartimePrecomputedMultiscalarMul<curve25519_dalek::edwards::EdwardsPoint::i686-unknown-linux-gnu> for curve25519_dalek::edwards::VartimeEdwardsPrecomputation::i686-unknown-linux-gnu}::optional_mixed_multiscalar_mul]:
    Source: 'curve25519-dalek/src/edwards.rs', lines 1084:4-1099:5
    Visibility: public -/
axiom
  edwards.VartimeEdwardsPrecomputation.«i686-unknown-linux-gnu».Insts.«Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPointi686-unknown-linux-gnu».optional_mixed_multiscalar_mul
  {I : Type} {J : Type} {K : Type} {Clause0_Item : Type} {Clause0_IntoIter :
  Type} {Clause2_Item : Type} {Clause2_IntoIter : Type} {Clause4_IntoIter :
  Type} (coreitertraitscollectIntoIteratorInst :
  core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
  (coreborrowBorrowClause0_ItemScalarInst : core.borrow.Borrow Clause0_Item
  scalar.Scalar) (coreitertraitscollectIntoIteratorInst1 :
  core.iter.traits.collect.IntoIterator J Clause2_Item Clause2_IntoIter)
  (coreborrowBorrowClause2_ItemScalarInst : core.borrow.Borrow Clause2_Item
  scalar.Scalar)
  («coreitertraitscollectIntoIteratorKOptionEdwardsPointi686-unknown-linux-gnuClause4_IntoIterInst»
  : core.iter.traits.collect.IntoIterator K (Option
  edwards.EdwardsPoint.«i686-unknown-linux-gnu») Clause4_IntoIter) :
  edwards.VartimeEdwardsPrecomputation.«i686-unknown-linux-gnu» → I → J
    → K → Result (Option edwards.EdwardsPoint.«i686-unknown-linux-gnu»)

/-- [curve25519_dalek::edwards::{impl curve25519_dalek::traits::VartimePrecomputedMultiscalarMul<curve25519_dalek::edwards::EdwardsPoint::i686-unknown-linux-gnu> for curve25519_dalek::edwards::VartimeEdwardsPrecomputation::i686-unknown-linux-gnu}::new]:
    Source: 'curve25519-dalek/src/edwards.rs', lines 1068:4-1074:5
    Visibility: public -/
axiom
  edwards.VartimeEdwardsPrecomputation.«i686-unknown-linux-gnu».Insts.«Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPointi686-unknown-linux-gnu».new
  {I : Type} {Clause0_Item : Type} {Clause0_IntoIter : Type}
  (coreitertraitscollectIntoIteratorInst :
  core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
  («coreborrowBorrowClause0_ItemEdwardsPointi686-unknown-linux-gnuInst» :
  core.borrow.Borrow Clause0_Item
  edwards.EdwardsPoint.«i686-unknown-linux-gnu») :
  I → Result edwards.VartimeEdwardsPrecomputation.«i686-unknown-linux-gnu»

/-- [curve25519_dalek::montgomery::{impl core::ops::arith::Mul<&'b curve25519_dalek::scalar::Scalar, curve25519_dalek::montgomery::MontgomeryPoint> for curve25519_dalek::montgomery::MontgomeryPoint}::mul]:
    Source: 'curve25519-dalek/src/macros.rs', lines 93:12-95:13
    Visibility: public -/
axiom
  montgomery.MontgomeryPoint.Insts.CoreOpsArithMulSharedBScalarMontgomeryPoint.mul
  :
  montgomery.MontgomeryPoint → scalar.Scalar → Result
    montgomery.MontgomeryPoint

/-- [curve25519_dalek::montgomery::{impl core::ops::arith::Mul<&'b curve25519_dalek::montgomery::MontgomeryPoint, curve25519_dalek::montgomery::MontgomeryPoint> for curve25519_dalek::scalar::Scalar}::mul]:
    Source: 'curve25519-dalek/src/macros.rs', lines 93:12-95:13
    Visibility: public -/
axiom
  scalar.Scalar.Insts.CoreOpsArithMulSharedBMontgomeryPointMontgomeryPoint.mul
  :
  scalar.Scalar → montgomery.MontgomeryPoint → Result
    montgomery.MontgomeryPoint

/-- [curve25519_dalek::montgomery::{impl core::ops::arith::Mul<&'_0 curve25519_dalek::scalar::Scalar, curve25519_dalek::montgomery::MontgomeryPoint> for &'_1 curve25519_dalek::montgomery::MontgomeryPoint}::mul]:
    Source: 'curve25519-dalek/src/montgomery.rs', lines 488:4-492:5
    Visibility: public -/
axiom
  Shared1MontgomeryPoint.Insts.CoreOpsArithMulShared0ScalarMontgomeryPoint.mul
  :
  montgomery.MontgomeryPoint → scalar.Scalar → Result
    montgomery.MontgomeryPoint

/-- [curve25519_dalek::montgomery::{impl core::ops::arith::Mul<&'_0 curve25519_dalek::montgomery::MontgomeryPoint, curve25519_dalek::montgomery::MontgomeryPoint> for &'_1 curve25519_dalek::scalar::Scalar}::mul]:
    Source: 'curve25519-dalek/src/montgomery.rs', lines 504:4-506:5
    Visibility: public -/
axiom
  Shared1Scalar.Insts.CoreOpsArithMulShared0MontgomeryPointMontgomeryPoint.mul
  :
  scalar.Scalar → montgomery.MontgomeryPoint → Result
    montgomery.MontgomeryPoint

/-- [curve25519_dalek::ristretto::{curve25519_dalek::ristretto::RistrettoPoint::x86_64-unknown-linux-gnu}::double_and_compress_batch]:
    Source: 'curve25519-dalek/src/ristretto.rs', lines 566:4-663:5
    Visibility: public -/
axiom
  ristretto.«RistrettoPointx86_64-unknown-linux-gnu».double_and_compress_batch
  {I : Type} {Clause0_IntoIter : Type}
  («coreitertraitscollectIntoIteratorISharedARistrettoPointx86_64-unknown-linux-gnuClause0_IntoIterInst»
  : core.iter.traits.collect.IntoIterator I
  ristretto.RistrettoPoint.«x86_64-unknown-linux-gnu» Clause0_IntoIter) :
  I → Result (alloc.vec.Vec ristretto.CompressedRistretto)

/-- [curve25519_dalek::ristretto::{curve25519_dalek::ristretto::RistrettoPoint::i686-unknown-linux-gnu}::double_and_compress_batch]:
    Source: 'curve25519-dalek/src/ristretto.rs', lines 566:4-663:5
    Visibility: public -/
axiom
  ristretto.«RistrettoPointi686-unknown-linux-gnu».double_and_compress_batch
  {I : Type} {Clause0_IntoIter : Type}
  («coreitertraitscollectIntoIteratorISharedARistrettoPointi686-unknown-linux-gnuClause0_IntoIterInst»
  : core.iter.traits.collect.IntoIterator I
  ristretto.RistrettoPoint.«i686-unknown-linux-gnu» Clause0_IntoIter) :
  I → Result (alloc.vec.Vec ristretto.CompressedRistretto)

/-- [curve25519_dalek::ristretto::{impl core::iter::traits::accum::Sum<T> for curve25519_dalek::ristretto::RistrettoPoint::x86_64-unknown-linux-gnu}::sum]:
    Source: 'curve25519-dalek/src/ristretto.rs', lines 902:4-907:5
    Visibility: public -/
axiom
  ristretto.RistrettoPoint.«x86_64-unknown-linux-gnu».Insts.CoreIterTraitsAccumSum.sum
  {T : Type} {I : Type}
  («coreborrowBorrowTRistrettoPointx86_64-unknown-linux-gnuInst» :
  core.borrow.Borrow T ristretto.RistrettoPoint.«x86_64-unknown-linux-gnu»)
  (coreitertraitsiteratorIteratorInst : core.iter.traits.iterator.Iterator I T)
  :
  I → Result ristretto.RistrettoPoint.«x86_64-unknown-linux-gnu»

/-- [curve25519_dalek::ristretto::{impl core::iter::traits::accum::Sum<T> for curve25519_dalek::ristretto::RistrettoPoint::i686-unknown-linux-gnu}::sum]:
    Source: 'curve25519-dalek/src/ristretto.rs', lines 902:4-907:5
    Visibility: public -/
axiom
  ristretto.RistrettoPoint.«i686-unknown-linux-gnu».Insts.CoreIterTraitsAccumSum.sum
  {T : Type} {I : Type}
  («coreborrowBorrowTRistrettoPointi686-unknown-linux-gnuInst» :
  core.borrow.Borrow T ristretto.RistrettoPoint.«i686-unknown-linux-gnu»)
  (coreitertraitsiteratorIteratorInst : core.iter.traits.iterator.Iterator I T)
  :
  I → Result ristretto.RistrettoPoint.«i686-unknown-linux-gnu»

/-- [curve25519_dalek::ristretto::{impl curve25519_dalek::traits::MultiscalarMul<curve25519_dalek::ristretto::RistrettoPoint::x86_64-unknown-linux-gnu> for curve25519_dalek::ristretto::RistrettoPoint::x86_64-unknown-linux-gnu}::multiscalar_mul]:
    Source: 'curve25519-dalek/src/ristretto.rs', lines 984:4-993:5
    Visibility: public -/
axiom
  ristretto.RistrettoPoint.«x86_64-unknown-linux-gnu».Insts.«Curve25519_dalekTraitsMultiscalarMulRistrettoPointx86_64-unknown-linux-gnu».multiscalar_mul
  {I : Type} {J : Type} {Clause0_Item : Type} {Clause0_IntoIter : Type}
  {Clause2_Item : Type} {Clause2_IntoIter : Type}
  (coreitertraitscollectIntoIteratorInst :
  core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
  (coreborrowBorrowClause0_ItemScalarInst : core.borrow.Borrow Clause0_Item
  scalar.Scalar) (coreitertraitscollectIntoIteratorInst1 :
  core.iter.traits.collect.IntoIterator J Clause2_Item Clause2_IntoIter)
  («coreborrowBorrowClause2_ItemRistrettoPointx86_64-unknown-linux-gnuInst» :
  core.borrow.Borrow Clause2_Item
  ristretto.RistrettoPoint.«x86_64-unknown-linux-gnu») :
  I → J → Result ristretto.RistrettoPoint.«x86_64-unknown-linux-gnu»

/-- [curve25519_dalek::ristretto::{impl curve25519_dalek::traits::MultiscalarMul<curve25519_dalek::ristretto::RistrettoPoint::i686-unknown-linux-gnu> for curve25519_dalek::ristretto::RistrettoPoint::i686-unknown-linux-gnu}::multiscalar_mul]:
    Source: 'curve25519-dalek/src/ristretto.rs', lines 984:4-993:5
    Visibility: public -/
axiom
  ristretto.RistrettoPoint.«i686-unknown-linux-gnu».Insts.«Curve25519_dalekTraitsMultiscalarMulRistrettoPointi686-unknown-linux-gnu».multiscalar_mul
  {I : Type} {J : Type} {Clause0_Item : Type} {Clause0_IntoIter : Type}
  {Clause2_Item : Type} {Clause2_IntoIter : Type}
  (coreitertraitscollectIntoIteratorInst :
  core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
  (coreborrowBorrowClause0_ItemScalarInst : core.borrow.Borrow Clause0_Item
  scalar.Scalar) (coreitertraitscollectIntoIteratorInst1 :
  core.iter.traits.collect.IntoIterator J Clause2_Item Clause2_IntoIter)
  («coreborrowBorrowClause2_ItemRistrettoPointi686-unknown-linux-gnuInst» :
  core.borrow.Borrow Clause2_Item
  ristretto.RistrettoPoint.«i686-unknown-linux-gnu») :
  I → J → Result ristretto.RistrettoPoint.«i686-unknown-linux-gnu»

/-- [curve25519_dalek::ristretto::{impl curve25519_dalek::traits::VartimeMultiscalarMul<curve25519_dalek::ristretto::RistrettoPoint::x86_64-unknown-linux-gnu> for curve25519_dalek::ristretto::RistrettoPoint::x86_64-unknown-linux-gnu}::optional_multiscalar_mul]:
    Source: 'curve25519-dalek/src/ristretto.rs', lines 1000:4-1012:5
    Visibility: public -/
axiom
  ristretto.RistrettoPoint.«x86_64-unknown-linux-gnu».Insts.«Curve25519_dalekTraitsVartimeMultiscalarMulRistrettoPointx86_64-unknown-linux-gnu».optional_multiscalar_mul
  {I : Type} {J : Type} {Clause0_Item : Type} {Clause0_IntoIter : Type}
  {Clause2_IntoIter : Type} (coreitertraitscollectIntoIteratorInst :
  core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
  (coreborrowBorrowClause0_ItemScalarInst : core.borrow.Borrow Clause0_Item
  scalar.Scalar)
  («coreitertraitscollectIntoIteratorJOptionRistrettoPointx86_64-unknown-linux-gnuClause2_IntoIterInst»
  : core.iter.traits.collect.IntoIterator J (Option
  ristretto.RistrettoPoint.«x86_64-unknown-linux-gnu») Clause2_IntoIter) :
  I → J → Result (Option
    ristretto.RistrettoPoint.«x86_64-unknown-linux-gnu»)

/-- [curve25519_dalek::ristretto::{impl curve25519_dalek::traits::VartimeMultiscalarMul<curve25519_dalek::ristretto::RistrettoPoint::i686-unknown-linux-gnu> for curve25519_dalek::ristretto::RistrettoPoint::i686-unknown-linux-gnu}::optional_multiscalar_mul]:
    Source: 'curve25519-dalek/src/ristretto.rs', lines 1000:4-1012:5
    Visibility: public -/
axiom
  ristretto.RistrettoPoint.«i686-unknown-linux-gnu».Insts.«Curve25519_dalekTraitsVartimeMultiscalarMulRistrettoPointi686-unknown-linux-gnu».optional_multiscalar_mul
  {I : Type} {J : Type} {Clause0_Item : Type} {Clause0_IntoIter : Type}
  {Clause2_IntoIter : Type} (coreitertraitscollectIntoIteratorInst :
  core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
  (coreborrowBorrowClause0_ItemScalarInst : core.borrow.Borrow Clause0_Item
  scalar.Scalar)
  («coreitertraitscollectIntoIteratorJOptionRistrettoPointi686-unknown-linux-gnuClause2_IntoIterInst»
  : core.iter.traits.collect.IntoIterator J (Option
  ristretto.RistrettoPoint.«i686-unknown-linux-gnu») Clause2_IntoIter) :
  I → J → Result (Option
    ristretto.RistrettoPoint.«i686-unknown-linux-gnu»)

/-- [curve25519_dalek::ristretto::{impl curve25519_dalek::traits::VartimePrecomputedMultiscalarMul<curve25519_dalek::ristretto::RistrettoPoint::x86_64-unknown-linux-gnu> for curve25519_dalek::ristretto::VartimeRistrettoPrecomputation::x86_64-unknown-linux-gnu}::optional_mixed_multiscalar_mul]:
    Source: 'curve25519-dalek/src/ristretto.rs', lines 1047:4-1070:5
    Visibility: public -/
axiom
  ristretto.VartimeRistrettoPrecomputation.«x86_64-unknown-linux-gnu».Insts.«Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulRistrettoPointx86_64-unknown-linux-gnu».optional_mixed_multiscalar_mul
  {I : Type} {J : Type} {K : Type} {Clause0_Item : Type} {Clause0_IntoIter :
  Type} {Clause2_Item : Type} {Clause2_IntoIter : Type} {Clause4_IntoIter :
  Type} (coreitertraitscollectIntoIteratorInst :
  core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
  (coreborrowBorrowClause0_ItemScalarInst : core.borrow.Borrow Clause0_Item
  scalar.Scalar) (coreitertraitscollectIntoIteratorInst1 :
  core.iter.traits.collect.IntoIterator J Clause2_Item Clause2_IntoIter)
  (coreborrowBorrowClause2_ItemScalarInst : core.borrow.Borrow Clause2_Item
  scalar.Scalar)
  («coreitertraitscollectIntoIteratorKOptionRistrettoPointx86_64-unknown-linux-gnuClause4_IntoIterInst»
  : core.iter.traits.collect.IntoIterator K (Option
  ristretto.RistrettoPoint.«x86_64-unknown-linux-gnu») Clause4_IntoIter) :
  ristretto.VartimeRistrettoPrecomputation.«x86_64-unknown-linux-gnu» → I
    → J → K → Result (Option
    ristretto.RistrettoPoint.«x86_64-unknown-linux-gnu»)

/-- [curve25519_dalek::ristretto::{impl curve25519_dalek::traits::VartimePrecomputedMultiscalarMul<curve25519_dalek::ristretto::RistrettoPoint::x86_64-unknown-linux-gnu> for curve25519_dalek::ristretto::VartimeRistrettoPrecomputation::x86_64-unknown-linux-gnu}::new]:
    Source: 'curve25519-dalek/src/ristretto.rs', lines 1029:4-1037:5
    Visibility: public -/
axiom
  ristretto.VartimeRistrettoPrecomputation.«x86_64-unknown-linux-gnu».Insts.«Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulRistrettoPointx86_64-unknown-linux-gnu».new
  {I : Type} {Clause0_Item : Type} {Clause0_IntoIter : Type}
  (coreitertraitscollectIntoIteratorInst :
  core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
  («coreborrowBorrowClause0_ItemRistrettoPointx86_64-unknown-linux-gnuInst» :
  core.borrow.Borrow Clause0_Item
  ristretto.RistrettoPoint.«x86_64-unknown-linux-gnu») :
  I → Result
    ristretto.VartimeRistrettoPrecomputation.«x86_64-unknown-linux-gnu»

/-- [curve25519_dalek::ristretto::{impl curve25519_dalek::traits::VartimePrecomputedMultiscalarMul<curve25519_dalek::ristretto::RistrettoPoint::i686-unknown-linux-gnu> for curve25519_dalek::ristretto::VartimeRistrettoPrecomputation::i686-unknown-linux-gnu}::optional_mixed_multiscalar_mul]:
    Source: 'curve25519-dalek/src/ristretto.rs', lines 1047:4-1070:5
    Visibility: public -/
axiom
  ristretto.VartimeRistrettoPrecomputation.«i686-unknown-linux-gnu».Insts.«Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulRistrettoPointi686-unknown-linux-gnu».optional_mixed_multiscalar_mul
  {I : Type} {J : Type} {K : Type} {Clause0_Item : Type} {Clause0_IntoIter :
  Type} {Clause2_Item : Type} {Clause2_IntoIter : Type} {Clause4_IntoIter :
  Type} (coreitertraitscollectIntoIteratorInst :
  core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
  (coreborrowBorrowClause0_ItemScalarInst : core.borrow.Borrow Clause0_Item
  scalar.Scalar) (coreitertraitscollectIntoIteratorInst1 :
  core.iter.traits.collect.IntoIterator J Clause2_Item Clause2_IntoIter)
  (coreborrowBorrowClause2_ItemScalarInst : core.borrow.Borrow Clause2_Item
  scalar.Scalar)
  («coreitertraitscollectIntoIteratorKOptionRistrettoPointi686-unknown-linux-gnuClause4_IntoIterInst»
  : core.iter.traits.collect.IntoIterator K (Option
  ristretto.RistrettoPoint.«i686-unknown-linux-gnu») Clause4_IntoIter) :
  ristretto.VartimeRistrettoPrecomputation.«i686-unknown-linux-gnu» → I →
    J → K → Result (Option
    ristretto.RistrettoPoint.«i686-unknown-linux-gnu»)

/-- [curve25519_dalek::ristretto::{impl curve25519_dalek::traits::VartimePrecomputedMultiscalarMul<curve25519_dalek::ristretto::RistrettoPoint::i686-unknown-linux-gnu> for curve25519_dalek::ristretto::VartimeRistrettoPrecomputation::i686-unknown-linux-gnu}::new]:
    Source: 'curve25519-dalek/src/ristretto.rs', lines 1029:4-1037:5
    Visibility: public -/
axiom
  ristretto.VartimeRistrettoPrecomputation.«i686-unknown-linux-gnu».Insts.«Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulRistrettoPointi686-unknown-linux-gnu».new
  {I : Type} {Clause0_Item : Type} {Clause0_IntoIter : Type}
  (coreitertraitscollectIntoIteratorInst :
  core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
  («coreborrowBorrowClause0_ItemRistrettoPointi686-unknown-linux-gnuInst» :
  core.borrow.Borrow Clause0_Item
  ristretto.RistrettoPoint.«i686-unknown-linux-gnu») :
  I → Result
    ristretto.VartimeRistrettoPrecomputation.«i686-unknown-linux-gnu»



/-- [zeroize::{impl zeroize::Zeroize for alloc::vec::Vec<Z>}::zeroize]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/zeroize-1.8.2/src/lib.rs', lines 551:4-551:25
    Name pattern: [zeroize::{zeroize::Zeroize<alloc::vec::Vec<@Z>>}::zeroize]
    Visibility: public -/
@[rust_fun "zeroize::{zeroize::Zeroize<alloc::vec::Vec<@Z>>}::zeroize"]
axiom alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize
  {Z : Type} (ZeroizeInst : zeroize.Zeroize Z) :
  alloc.vec.Vec Z → Result (alloc.vec.Vec Z)

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
