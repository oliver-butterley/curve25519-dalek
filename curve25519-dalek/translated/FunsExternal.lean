-- [curve25519_dalek]: external functions.
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

/-- [core::array::from_fn]:
    Source: '/rustc/library/core/src/array/mod.rs', lines 110:0-112:52
    Name pattern: [core::array::from_fn]
    Visibility: public -/
@[rust_fun "core::array::from_fn"]
axiom core.array.from_fn
  {T : Type} {F : Type} (N : Std.Usize) (opsfunctionFnMutFTupleUsizeTInst :
  core.ops.function.FnMut F Std.Usize T) :
  F → Result (Array T N)

/-- [core::borrow::{impl core::borrow::Borrow<T> for T}::borrow]:
    Source: '/rustc/library/core/src/borrow.rs', lines 214:4-214:26
    Name pattern: [core::borrow::{core::borrow::Borrow<@T, @T>}::borrow]
    Visibility: public -/
@[rust_fun "core::borrow::{core::borrow::Borrow<@T, @T>}::borrow"]
axiom core.borrow.Borrow.Blanket.borrow {T : Type} : T → Result T

/-- [core::fmt::{impl core::fmt::Debug for str}::fmt]:
    Source: '/rustc/library/core/src/fmt/mod.rs', lines 2932:4-2932:50
    Name pattern: [core::fmt::{core::fmt::Debug<str>}::fmt]
    Visibility: public -/
@[rust_fun "core::fmt::{core::fmt::Debug<str>}::fmt"]
axiom Str.Insts.CoreFmtDebug.fmt
  :
  Str → core.fmt.Formatter → Result ((core.result.Result Unit
    core.fmt.Error) × core.fmt.Formatter)

/-- [core::iter::traits::iterator::Iterator::by_ref]:
    Source: '/rustc/library/core/src/iter/traits/iterator.rs', lines 1950:4-1952:20
    Name pattern: [core::iter::traits::iterator::Iterator::by_ref]
    Visibility: public -/
@[trait_default, rust_fun "core::iter::traits::iterator::Iterator::by_ref"]
axiom core.iter.traits.iterator.Iterator.by_ref.default
  {Self : Type} {Clause0_Item : Type} (IteratorInst :
  core.iter.traits.iterator.Iterator Self Clause0_Item) :
  Self → Result (Self × (Self → Self))

/-- [core::iter::traits::iterator::Iterator::map]:
    Source: '/rustc/library/core/src/iter/traits/iterator.rs', lines 831:4-834:34
    Name pattern: [core::iter::traits::iterator::Iterator::map]
    Visibility: public -/
@[trait_default, rust_fun "core::iter::traits::iterator::Iterator::map"]
axiom core.iter.traits.iterator.Iterator.map.default
  {Self : Type} {B : Type} {F : Type} {Clause0_Item : Type} (IteratorInst :
  core.iter.traits.iterator.Iterator Self Clause0_Item)
  (opsfunctionFnMutFTupleClause0_ItemBInst : core.ops.function.FnMut F
  Clause0_Item B) :
  Self → F → Result (core.iter.adapters.map.Map Self F)

/-- [core::iter::adapters::map::{impl core::iter::traits::iterator::Iterator<B> for core::iter::adapters::map::Map<I, F>}::fold]:
    Source: '/rustc/library/core/src/iter/adapters/map.rs', lines 124:4-126:41
    Name pattern: [core::iter::adapters::map::{core::iter::traits::iterator::Iterator<core::iter::adapters::map::Map<@I, @F>, @B>}::fold]
    Visibility: public -/
@[rust_fun
  "core::iter::adapters::map::{core::iter::traits::iterator::Iterator<core::iter::adapters::map::Map<@I, @F>, @B>}::fold"]
axiom core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator.fold
  {B : Type} {I : Type} {F : Type} {Acc : Type} {G : Type} {Clause0_Item :
  Type} (traitsiteratorIteratorInst : core.iter.traits.iterator.Iterator I
  Clause0_Item) (opsfunctionFnMutFTupleClause0_ItemBInst :
  core.ops.function.FnMut F Clause0_Item B) (opsfunctionFnMutGPairAccInst :
  core.ops.function.FnMut G (Acc × B) Acc) :
  core.iter.adapters.map.Map I F → Acc → G → Result Acc

/-- [core::iter::adapters::map::{impl core::iter::traits::iterator::Iterator<B> for core::iter::adapters::map::Map<I, F>}::size_hint]:
    Source: '/rustc/library/core/src/iter/adapters/map.rs', lines 111:4-111:49
    Name pattern: [core::iter::adapters::map::{core::iter::traits::iterator::Iterator<core::iter::adapters::map::Map<@I, @F>, @B>}::size_hint]
    Visibility: public -/
@[rust_fun
  "core::iter::adapters::map::{core::iter::traits::iterator::Iterator<core::iter::adapters::map::Map<@I, @F>, @B>}::size_hint"]
axiom core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator.size_hint
  {B : Type} {I : Type} {F : Type} {Clause0_Item : Type}
  (traitsiteratorIteratorInst : core.iter.traits.iterator.Iterator I
  Clause0_Item) (opsfunctionFnMutFTupleClause0_ItemBInst :
  core.ops.function.FnMut F Clause0_Item B) :
  core.iter.adapters.map.Map I F → Result (Std.Usize × (Option Std.Usize))

/-- [core::iter::adapters::map::{impl core::iter::traits::iterator::Iterator<B> for core::iter::adapters::map::Map<I, F>}::next]:
    Source: '/rustc/library/core/src/iter/adapters/map.rs', lines 106:4-106:35
    Name pattern: [core::iter::adapters::map::{core::iter::traits::iterator::Iterator<core::iter::adapters::map::Map<@I, @F>, @B>}::next]
    Visibility: public -/
@[rust_fun
  "core::iter::adapters::map::{core::iter::traits::iterator::Iterator<core::iter::adapters::map::Map<@I, @F>, @B>}::next"]
axiom core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator.next
  {B : Type} {I : Type} {F : Type} {Clause0_Item : Type}
  (traitsiteratorIteratorInst : core.iter.traits.iterator.Iterator I
  Clause0_Item) (opsfunctionFnMutFTupleClause0_ItemBInst :
  core.ops.function.FnMut F Clause0_Item B) :
  core.iter.adapters.map.Map I F → Result ((Option B) ×
    (core.iter.adapters.map.Map I F))

/-- [core::iter::adapters::zip::{impl core::iter::traits::iterator::Iterator<(Clause0_Item, Clause1_Item)> for core::iter::adapters::zip::Zip<A, B>}::fold]:
    Source: '/rustc/library/core/src/iter/adapters/zip.rs', lines 97:4-99:41
    Name pattern: [core::iter::adapters::zip::{core::iter::traits::iterator::Iterator<core::iter::adapters::zip::Zip<@A, @B>, (@Clause0_Item, @Clause1_Item)>}::fold]
    Visibility: public -/
@[rust_fun
  "core::iter::adapters::zip::{core::iter::traits::iterator::Iterator<core::iter::adapters::zip::Zip<@A, @B>, (@Clause0_Item, @Clause1_Item)>}::fold"]
axiom core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.fold
  {A : Type} {B : Type} {Acc : Type} {F : Type} {Clause0_Item : Type}
  {Clause1_Item : Type} (traitsiteratorIteratorInst :
  core.iter.traits.iterator.Iterator A Clause0_Item)
  (traitsiteratorIteratorInst1 : core.iter.traits.iterator.Iterator B
  Clause1_Item) (opsfunctionFnMutFPairAccPairAccInst : core.ops.function.FnMut
  F (Acc × (Clause0_Item × Clause1_Item)) Acc) :
  core.iter.adapters.zip.Zip A B → Acc → F → Result Acc

/-- [core::iter::adapters::zip::{impl core::iter::traits::iterator::Iterator<(Clause0_Item, Clause1_Item)> for core::iter::adapters::zip::Zip<A, B>}::size_hint]:
    Source: '/rustc/library/core/src/iter/adapters/zip.rs', lines 87:4-87:49
    Name pattern: [core::iter::adapters::zip::{core::iter::traits::iterator::Iterator<core::iter::adapters::zip::Zip<@A, @B>, (@Clause0_Item, @Clause1_Item)>}::size_hint]
    Visibility: public -/
@[rust_fun
  "core::iter::adapters::zip::{core::iter::traits::iterator::Iterator<core::iter::adapters::zip::Zip<@A, @B>, (@Clause0_Item, @Clause1_Item)>}::size_hint"]
axiom
  core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.size_hint
  {A : Type} {B : Type} {Clause0_Item : Type} {Clause1_Item : Type}
  (traitsiteratorIteratorInst : core.iter.traits.iterator.Iterator A
  Clause0_Item) (traitsiteratorIteratorInst1 :
  core.iter.traits.iterator.Iterator B Clause1_Item) :
  core.iter.adapters.zip.Zip A B → Result (Std.Usize × (Option Std.Usize))

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

/-- [core::iter::traits::iterator::Iterator::fold]:
    Source: '/rustc/library/core/src/iter/traits/iterator.rs', lines 2660:4-2663:64
    Name pattern: [core::iter::traits::iterator::Iterator::fold]
    Visibility: public -/
@[trait_default, rust_fun "core::iter::traits::iterator::Iterator::fold"]
axiom core.iter.traits.iterator.Iterator.fold.default
  {Self : Type} {B : Type} {F : Type} {Clause0_Item : Type} (IteratorInst :
  core.iter.traits.iterator.Iterator Self Clause0_Item)
  (opsfunctionFnMutFPairBInst : core.ops.function.FnMut F (B × Clause0_Item)
  B) :
  Self → B → F → Result B

/-- [core::iter::range::{impl core::iter::traits::iterator::Iterator<A> for core::ops::range::Range<A>}::size_hint]:
    Source: '/rustc/library/core/src/iter/range.rs', lines 1189:4-1189:49
    Name pattern: [core::iter::range::{core::iter::traits::iterator::Iterator<core::ops::range::Range<@A>, @A>}::size_hint]
    Visibility: public -/
@[rust_fun
  "core::iter::range::{core::iter::traits::iterator::Iterator<core::ops::range::Range<@A>, @A>}::size_hint"]
axiom core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.size_hint
  {A : Type} (StepInst : core.iter.range.Step A) :
  core.ops.range.Range A → Result (Std.Usize × (Option Std.Usize))

/-- [core::iter::sources::empty::empty]:
    Source: '/rustc/library/core/src/iter/sources/empty.rs', lines 20:0-20:35
    Name pattern: [core::iter::sources::empty::empty]
    Visibility: public -/
@[rust_fun "core::iter::sources::empty::empty"]
axiom core.iter.sources.empty.empty
  (T : Type) : Result (core.iter.sources.empty.Empty T)

/-- [core::iter::sources::empty::{impl core::iter::traits::iterator::Iterator<T> for core::iter::sources::empty::Empty<T>}::size_hint]:
    Source: '/rustc/library/core/src/iter/sources/empty.rs', lines 47:4-47:49
    Name pattern: [core::iter::sources::empty::{core::iter::traits::iterator::Iterator<core::iter::sources::empty::Empty<@T>, @T>}::size_hint]
    Visibility: public -/
@[rust_fun
  "core::iter::sources::empty::{core::iter::traits::iterator::Iterator<core::iter::sources::empty::Empty<@T>, @T>}::size_hint"]
axiom
  core.iter.sources.empty.Empty.Insts.CoreIterTraitsIteratorIterator.size_hint
  {T : Type} :
  core.iter.sources.empty.Empty T → Result (Std.Usize × (Option Std.Usize))

/-- [core::iter::sources::empty::{impl core::iter::traits::iterator::Iterator<T> for core::iter::sources::empty::Empty<T>}::next]:
    Source: '/rustc/library/core/src/iter/sources/empty.rs', lines 43:4-43:35
    Name pattern: [core::iter::sources::empty::{core::iter::traits::iterator::Iterator<core::iter::sources::empty::Empty<@T>, @T>}::next]
    Visibility: public -/
@[rust_fun
  "core::iter::sources::empty::{core::iter::traits::iterator::Iterator<core::iter::sources::empty::Empty<@T>, @T>}::next"]
axiom core.iter.sources.empty.Empty.Insts.CoreIterTraitsIteratorIterator.next
  {T : Type} :
  core.iter.sources.empty.Empty T → Result ((Option T) ×
    (core.iter.sources.empty.Empty T))

/-- [core::iter::traits::iterator::Iterator::size_hint]:
    Source: '/rustc/library/core/src/iter/traits/iterator.rs', lines 189:4-189:49
    Name pattern: [core::iter::traits::iterator::Iterator::size_hint]
    Visibility: public -/
@[trait_default, rust_fun "core::iter::traits::iterator::Iterator::size_hint"]
axiom core.iter.traits.iterator.Iterator.size_hint.default
  {Self : Type} {Clause0_Item : Type} (IteratorInst :
  core.iter.traits.iterator.Iterator Self Clause0_Item) :
  Self → Result (Std.Usize × (Option Std.Usize))

/-- [core::iter::traits::iterator::{impl core::iter::traits::iterator::Iterator<Clause0_Item> for &'_0 mut I}::size_hint]:
    Source: '/rustc/library/core/src/iter/traits/iterator.rs', lines 4237:4-4237:49
    Name pattern: [core::iter::traits::iterator::{core::iter::traits::iterator::Iterator<&'0 mut @I, @Clause0_Item>}::size_hint]
    Visibility: public -/
@[rust_fun
  "core::iter::traits::iterator::{core::iter::traits::iterator::Iterator<&'0 mut @I, @Clause0_Item>}::size_hint"]
axiom Mut0I.Insts.CoreIterTraitsIteratorIterator.size_hint
  {I : Type} {Clause0_Item : Type} (IteratorInst :
  core.iter.traits.iterator.Iterator I Clause0_Item) :
  I → Result (Std.Usize × (Option Std.Usize))

/-- [core::num::{usize}::div_ceil]:
    Source: '/rustc/library/core/src/num/uint_macros.rs', lines 3787:8-3787:54
    Name pattern: [core::num::{usize}::div_ceil]
    Visibility: public -/
@[rust_fun "core::num::{usize}::div_ceil"]
axiom core.num.Usize.div_ceil : Std.Usize → Std.Usize → Result Std.Usize

/-- [core::option::{core::option::Option<T>}::map]:
    Source: '/rustc/library/core/src/option.rs', lines 1158:4-1160:53
    Name pattern: [core::option::{core::option::Option<@T>}::map]
    Visibility: public -/
@[rust_fun "core::option::{core::option::Option<@T>}::map"]
axiom core.option.Option.map
  {T : Type} {U : Type} {F : Type} (opsfunctionFnOnceFTupleTUInst :
  core.ops.function.FnOnce F T U) :
  Option T → F → Result (Option U)

/-- [core::option::{impl core::cmp::PartialEq<core::option::Option<T>> for core::option::Option<T>}::eq]:
    Source: '/rustc/library/core/src/option.rs', lines 2436:4-2436:38
    Name pattern: [core::option::{core::cmp::PartialEq<core::option::Option<@T>, core::option::Option<@T>>}::eq]
    Visibility: public -/
@[rust_fun
  "core::option::{core::cmp::PartialEq<core::option::Option<@T>, core::option::Option<@T>>}::eq"]
axiom core.option.Option.Insts.CoreCmpPartialEqOption.eq
  {T : Type} (cmpPartialEqInst : core.cmp.PartialEq T T) :
  Option T → Option T → Result Bool

/-- [core::option::{impl core::iter::traits::collect::FromIterator<core::option::Option<A>> for core::option::Option<V>}::from_iter]:
    Source: '/rustc/library/core/src/option.rs', lines 2851:4-2851:73
    Name pattern: [core::option::{core::iter::traits::collect::FromIterator<core::option::Option<@V>, core::option::Option<@A>>}::from_iter]
    Visibility: public -/
@[rust_fun
  "core::option::{core::iter::traits::collect::FromIterator<core::option::Option<@V>, core::option::Option<@A>>}::from_iter"]
axiom
  core.option.Option.Insts.CoreIterTraitsCollectFromIteratorOption.from_iter
  {A : Type} {V : Type} {I : Type} {Clause1_IntoIter : Type}
  (itertraitscollectFromIteratorInst : core.iter.traits.collect.FromIterator V
  A) (itertraitscollectIntoIteratorIOptionClause1_IntoIterInst :
  core.iter.traits.collect.IntoIterator I (Option A) Clause1_IntoIter) :
  I → Result (Option V)

/-- [core::option::{impl core::ops::try_trait::Try for core::option::Option<T>}::branch]:
    Source: '/rustc/library/core/src/option.rs', lines 2868:4-2868:64
    Name pattern: [core::option::{core::ops::try_trait::Try<core::option::Option<@T>>}::branch]
    Visibility: public -/
@[rust_fun
  "core::option::{core::ops::try_trait::Try<core::option::Option<@T>>}::branch"]
axiom core.option.Option.Insts.CoreOpsTry_traitTry.branch
  {T : Type} :
  Option T → Result (core.ops.control_flow.ControlFlow (Option
    core.convert.Infallible) T)

/-- [core::option::{impl core::ops::try_trait::FromResidual<core::option::Option<core::convert::Infallible>> for core::option::Option<T>}::from_residual]:
    Source: '/rustc/library/core/src/option.rs', lines 2882:4-2882:67
    Name pattern: [core::option::{core::ops::try_trait::FromResidual<core::option::Option<@T>, core::option::Option<core::convert::Infallible>>}::from_residual]
    Visibility: public -/
@[rust_fun
  "core::option::{core::ops::try_trait::FromResidual<core::option::Option<@T>, core::option::Option<core::convert::Infallible>>}::from_residual"]
axiom
  core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual
  (T : Type) : Option core.convert.Infallible → Result (Option T)

/-- [core::result::{core::result::Result<T, E>}::map]:
    Source: '/rustc/library/core/src/result.rs', lines 832:4-834:53
    Name pattern: [core::result::{core::result::Result<@T, @E>}::map]
    Visibility: public -/
@[rust_fun "core::result::{core::result::Result<@T, @E>}::map"]
axiom core.result.Result.map
  {T : Type} {E : Type} {U : Type} {F : Type} (opsfunctionFnOnceFTupleTUInst :
  core.ops.function.FnOnce F T U) :
  core.result.Result T E → F → Result (core.result.Result U E)

/-- [core::slice::index::{impl core::slice::index::SliceIndex<[T], [T]> for core::ops::range::RangeFull}::index_mut]:
    Source: '/rustc/library/core/src/slice/index.rs', lines 641:4-641:51
    Name pattern: [core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFull, [@T], [@T]>}::index_mut]
    Visibility: public -/
@[rust_fun
  "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFull, [@T], [@T]>}::index_mut"]
axiom
  core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut
  {T : Type} :
  core.ops.range.RangeFull → Slice T → Result ((Slice T) × (Slice T →
    Slice T))

/-- [core::slice::index::{impl core::slice::index::SliceIndex<[T], [T]> for core::ops::range::RangeFull}::index]:
    Source: '/rustc/library/core/src/slice/index.rs', lines 635:4-635:39
    Name pattern: [core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFull, [@T], [@T]>}::index]
    Visibility: public -/
@[rust_fun
  "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFull, [@T], [@T]>}::index"]
axiom core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index
  {T : Type} : core.ops.range.RangeFull → Slice T → Result (Slice T)

/-- [core::slice::index::{impl core::slice::index::SliceIndex<[T], [T]> for core::ops::range::RangeFull}::get_unchecked_mut]:
    Source: '/rustc/library/core/src/slice/index.rs', lines 630:4-630:66
    Name pattern: [core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFull, [@T], [@T]>}::get_unchecked_mut]
    Visibility: public -/
@[rust_fun
  "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFull, [@T], [@T]>}::get_unchecked_mut"]
axiom
  core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut
  {T : Type} :
  core.ops.range.RangeFull → MutRawPtr (Slice T) → Result (MutRawPtr (Slice
    T))

/-- [core::slice::index::{impl core::slice::index::SliceIndex<[T], [T]> for core::ops::range::RangeFull}::get_unchecked]:
    Source: '/rustc/library/core/src/slice/index.rs', lines 625:4-625:66
    Name pattern: [core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFull, [@T], [@T]>}::get_unchecked]
    Visibility: public -/
@[rust_fun
  "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFull, [@T], [@T]>}::get_unchecked"]
axiom
  core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked
  {T : Type} :
  core.ops.range.RangeFull → ConstRawPtr (Slice T) → Result (ConstRawPtr
    (Slice T))

/-- [core::slice::index::{impl core::slice::index::SliceIndex<[T], [T]> for core::ops::range::RangeFull}::get_mut]:
    Source: '/rustc/library/core/src/slice/index.rs', lines 620:4-620:57
    Name pattern: [core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFull, [@T], [@T]>}::get_mut]
    Visibility: public -/
@[rust_fun
  "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFull, [@T], [@T]>}::get_mut"]
axiom core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut
  {T : Type} :
  core.ops.range.RangeFull → Slice T → Result ((Option (Slice T)) ×
    (Option (Slice T) → Slice T))

/-- [core::slice::index::{impl core::slice::index::SliceIndex<[T], [T]> for core::ops::range::RangeFull}::get]:
    Source: '/rustc/library/core/src/slice/index.rs', lines 614:4-614:45
    Name pattern: [core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFull, [@T], [@T]>}::get]
    Visibility: public -/
@[rust_fun
  "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFull, [@T], [@T]>}::get"]
axiom core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get
  {T : Type} :
  core.ops.range.RangeFull → Slice T → Result (Option (Slice T))

/-- [core::slice::iter::{impl core::iter::traits::iterator::Iterator<&'a mut T> for core::slice::iter::IterMut<'a, T>}::fold]:
    Source: '/rustc/library/core/src/slice/iter/macros.rs', lines 254:12-256:49
    Name pattern: [core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::IterMut<'a, @T>, &'a mut @T>}::fold]
    Visibility: public -/
@[rust_fun
  "core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::IterMut<'a, @T>, &'a mut @T>}::fold"]
axiom core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT.fold
  {T : Type} {B : Type} {F : Type} (opsfunctionFnMutFPairBMutATBInst :
  core.ops.function.FnMut F (B × T) B) :
  core.slice.iter.IterMut T → B → F → Result (B ×
    (core.slice.iter.IterMut T))

/-- [core::slice::iter::{impl core::iter::traits::iterator::Iterator<&'a mut T> for core::slice::iter::IterMut<'a, T>}::size_hint]:
    Source: '/rustc/library/core/src/slice/iter/macros.rs', lines 213:12-213:57
    Name pattern: [core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::IterMut<'a, @T>, &'a mut @T>}::size_hint]
    Visibility: public -/
@[rust_fun
  "core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::IterMut<'a, @T>, &'a mut @T>}::size_hint"]
axiom
  core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT.size_hint
  {T : Type} :
  core.slice.iter.IterMut T → Result (Std.Usize × (Option Std.Usize))

/-- [core::slice::iter::{impl core::iter::traits::iterator::Iterator<&'a T> for core::slice::iter::Iter<'a, T>}::fold]:
    Source: '/rustc/library/core/src/slice/iter/macros.rs', lines 254:12-256:49
    Name pattern: [core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::Iter<'a, @T>, &'a @T>}::fold]
    Visibility: public -/
@[rust_fun
  "core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::Iter<'a, @T>, &'a @T>}::fold"]
axiom core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.fold
  {T : Type} {B : Type} {F : Type} (opsfunctionFnMutFPairBSharedATBInst :
  core.ops.function.FnMut F (B × T) B) :
  core.slice.iter.Iter T → B → F → Result B

/-- [core::slice::iter::{impl core::iter::traits::iterator::Iterator<&'a T> for core::slice::iter::Iter<'a, T>}::size_hint]:
    Source: '/rustc/library/core/src/slice/iter/macros.rs', lines 213:12-213:57
    Name pattern: [core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::Iter<'a, @T>, &'a @T>}::size_hint]
    Visibility: public -/
@[rust_fun
  "core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::Iter<'a, @T>, &'a @T>}::size_hint"]
axiom
  core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.size_hint
  {T : Type} :
  core.slice.iter.Iter T → Result (Std.Usize × (Option Std.Usize))

/-- [core::slice::iter::{impl core::iter::traits::iterator::Iterator<&'a [T]> for core::slice::iter::Chunks<'a, T>}::size_hint]:
    Source: '/rustc/library/core/src/slice/iter.rs', lines 1515:4-1515:49
    Name pattern: [core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::Chunks<'a, @T>, &'a [@T]>}::size_hint]
    Visibility: public -/
@[rust_fun
  "core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::Chunks<'a, @T>, &'a [@T]>}::size_hint"]
axiom
  core.slice.iter.Chunks.Insts.CoreIterTraitsIteratorIteratorSharedASlice.size_hint
  {T : Type} :
  core.slice.iter.Chunks T → Result (Std.Usize × (Option Std.Usize))

/-- [core::slice::iter::{impl core::iter::traits::iterator::Iterator<&'a [T]> for core::slice::iter::Chunks<'a, T>}::next]:
    Source: '/rustc/library/core/src/slice/iter.rs', lines 1503:4-1503:41
    Name pattern: [core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::Chunks<'a, @T>, &'a [@T]>}::next]
    Visibility: public -/
@[rust_fun
  "core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::Chunks<'a, @T>, &'a [@T]>}::next"]
axiom
  core.slice.iter.Chunks.Insts.CoreIterTraitsIteratorIteratorSharedASlice.next
  {T : Type} :
  core.slice.iter.Chunks T → Result ((Option (Slice T)) ×
    (core.slice.iter.Chunks T))

/-- [core::slice::{[T]}::chunks]:
    Source: '/rustc/library/core/src/slice/mod.rs', lines 1154:4-1154:66
    Name pattern: [core::slice::{[@T]}::chunks]
    Visibility: public -/
@[rust_fun "core::slice::{[@T]}::chunks"]
axiom core.slice.Slice.chunks
  {T : Type} : Slice T → Std.Usize → Result (core.slice.iter.Chunks T)

/-- [alloc::vec::{alloc::vec::Vec<T>}::is_empty]:
    Source: '/rustc/library/alloc/src/vec/mod.rs', lines 3125:4-3125:40
    Name pattern: [alloc::vec::{alloc::vec::Vec<@T>}::is_empty]
    Visibility: public -/
@[rust_fun "alloc::vec::{alloc::vec::Vec<@T>}::is_empty"]
axiom alloc.vec.Vec.is_empty
  {T : Type} (A : Type) : alloc.vec.Vec T → Result Bool

/-- [subtle::{subtle::Choice}::unwrap_u8]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/subtle-2.6.1/src/lib.rs', lines 133:4-133:33
    Name pattern: [subtle::{subtle::Choice}::unwrap_u8]
    Visibility: public -/
@[rust_fun "subtle::{subtle::Choice}::unwrap_u8"]
axiom subtle.Choice.unwrap_u8 : subtle.Choice → Result Std.U8

/-- [subtle::{impl core::convert::From<subtle::Choice> for bool}::from]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/subtle-2.6.1/src/lib.rs', lines 153:4-153:35
    Name pattern: [subtle::{core::convert::From<bool, subtle::Choice>}::from]
    Visibility: public -/
@[rust_fun "subtle::{core::convert::From<bool, subtle::Choice>}::from"]
axiom Bool.Insts.CoreConvertFromChoice.from : subtle.Choice → Result Bool

/-- [subtle::{impl core::ops::bit::BitAnd<subtle::Choice, subtle::Choice> for subtle::Choice}::bitand]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/subtle-2.6.1/src/lib.rs', lines 162:4-162:42
    Name pattern: [subtle::{core::ops::bit::BitAnd<subtle::Choice, subtle::Choice, subtle::Choice>}::bitand]
    Visibility: public -/
@[rust_fun
  "subtle::{core::ops::bit::BitAnd<subtle::Choice, subtle::Choice, subtle::Choice>}::bitand"]
axiom subtle.Choice.Insts.CoreOpsBitBitAndChoiceChoice.bitand
  : subtle.Choice → subtle.Choice → Result subtle.Choice

/-- [subtle::{impl core::ops::bit::BitOr<subtle::Choice, subtle::Choice> for subtle::Choice}::bitor]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/subtle-2.6.1/src/lib.rs', lines 177:4-177:41
    Name pattern: [subtle::{core::ops::bit::BitOr<subtle::Choice, subtle::Choice, subtle::Choice>}::bitor]
    Visibility: public -/
@[rust_fun
  "subtle::{core::ops::bit::BitOr<subtle::Choice, subtle::Choice, subtle::Choice>}::bitor"]
axiom subtle.Choice.Insts.CoreOpsBitBitOrChoiceChoice.bitor
  : subtle.Choice → subtle.Choice → Result subtle.Choice

/-- [subtle::{impl core::ops::bit::Not<subtle::Choice> for subtle::Choice}::not]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/subtle-2.6.1/src/lib.rs', lines 207:4-207:26
    Name pattern: [subtle::{core::ops::bit::Not<subtle::Choice, subtle::Choice>}::not]
    Visibility: public -/
@[rust_fun
  "subtle::{core::ops::bit::Not<subtle::Choice, subtle::Choice>}::not"]
axiom subtle.Choice.Insts.CoreOpsBitNotChoice.not
  : subtle.Choice → Result subtle.Choice

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

/-- [subtle::{impl subtle::ConstantTimeEq for u16}::ct_eq]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/subtle-2.6.1/src/lib.rs', lines 348:12-348:51
    Name pattern: [subtle::{subtle::ConstantTimeEq<u16>}::ct_eq]
    Visibility: public -/
@[rust_fun "subtle::{subtle::ConstantTimeEq<u16>}::ct_eq"]
axiom U16.Insts.SubtleConstantTimeEq.ct_eq
  : Std.U16 → Std.U16 → Result subtle.Choice

/-- [subtle::ConditionallySelectable::conditional_assign]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/subtle-2.6.1/src/lib.rs', lines 442:4-442:66
    Name pattern: [subtle::ConditionallySelectable::conditional_assign]
    Visibility: public -/
@[trait_default, rust_fun
  "subtle::ConditionallySelectable::conditional_assign"]
axiom subtle.ConditionallySelectable.conditional_assign.default
  {Self : Type} (ConditionallySelectableInst : subtle.ConditionallySelectable
  Self) :
  Self → Self → subtle.Choice → Result Self

/-- [subtle::ConditionallySelectable::conditional_swap]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/subtle-2.6.1/src/lib.rs', lines 469:4-469:67
    Name pattern: [subtle::ConditionallySelectable::conditional_swap]
    Visibility: public -/
@[trait_default, rust_fun "subtle::ConditionallySelectable::conditional_swap"]
axiom subtle.ConditionallySelectable.conditional_swap.default
  {Self : Type} (ConditionallySelectableInst : subtle.ConditionallySelectable
  Self) :
  Self → Self → subtle.Choice → Result (Self × Self)

/-- [subtle::{impl subtle::ConditionallySelectable for u8}::conditional_swap]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/subtle-2.6.1/src/lib.rs', lines 529:12-529:75
    Name pattern: [subtle::{subtle::ConditionallySelectable<u8>}::conditional_swap]
    Visibility: public -/
@[rust_fun "subtle::{subtle::ConditionallySelectable<u8>}::conditional_swap"]
axiom U8.Insts.SubtleConditionallySelectable.conditional_swap
  : Std.U8 → Std.U8 → subtle.Choice → Result (Std.U8 × Std.U8)

/-- [subtle::{impl subtle::ConditionallySelectable for u8}::conditional_assign]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/subtle-2.6.1/src/lib.rs', lines 521:12-521:74
    Name pattern: [subtle::{subtle::ConditionallySelectable<u8>}::conditional_assign]
    Visibility: public -/
@[rust_fun "subtle::{subtle::ConditionallySelectable<u8>}::conditional_assign"]
axiom U8.Insts.SubtleConditionallySelectable.conditional_assign
  : Std.U8 → Std.U8 → subtle.Choice → Result Std.U8

/-- [subtle::{impl subtle::ConditionallySelectable for u8}::conditional_select]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/subtle-2.6.1/src/lib.rs', lines 513:12-513:77
    Name pattern: [subtle::{subtle::ConditionallySelectable<u8>}::conditional_select]
    Visibility: public -/
@[rust_fun "subtle::{subtle::ConditionallySelectable<u8>}::conditional_select"]
axiom U8.Insts.SubtleConditionallySelectable.conditional_select
  : Std.U8 → Std.U8 → subtle.Choice → Result Std.U8

/-- [subtle::{impl subtle::ConditionallySelectable for u64}::conditional_select]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/subtle-2.6.1/src/lib.rs', lines 513:12-513:77
    Name pattern: [subtle::{subtle::ConditionallySelectable<u64>}::conditional_select]
    Visibility: public -/
@[rust_fun
  "subtle::{subtle::ConditionallySelectable<u64>}::conditional_select"]
axiom U64.Insts.SubtleConditionallySelectable.conditional_select
  : Std.U64 → Std.U64 → subtle.Choice → Result Std.U64

/-- [subtle::{impl subtle::ConditionallySelectable for u64}::conditional_assign]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/subtle-2.6.1/src/lib.rs', lines 521:12-521:74
    Name pattern: [subtle::{subtle::ConditionallySelectable<u64>}::conditional_assign]
    Visibility: public -/
@[rust_fun
  "subtle::{subtle::ConditionallySelectable<u64>}::conditional_assign"]
axiom U64.Insts.SubtleConditionallySelectable.conditional_assign
  : Std.U64 → Std.U64 → subtle.Choice → Result Std.U64

/-- [subtle::{impl subtle::ConditionallySelectable for u64}::conditional_swap]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/subtle-2.6.1/src/lib.rs', lines 529:12-529:75
    Name pattern: [subtle::{subtle::ConditionallySelectable<u64>}::conditional_swap]
    Visibility: public -/
@[rust_fun "subtle::{subtle::ConditionallySelectable<u64>}::conditional_swap"]
axiom U64.Insts.SubtleConditionallySelectable.conditional_swap
  : Std.U64 → Std.U64 → subtle.Choice → Result (Std.U64 × Std.U64)

/-- [subtle::{impl subtle::ConditionallySelectable for [T; N]}::conditional_select]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/subtle-2.6.1/src/lib.rs', lines 581:4-581:69
    Name pattern: [subtle::{subtle::ConditionallySelectable<[@T; @N]>}::conditional_select]
    Visibility: public -/
@[rust_fun
  "subtle::{subtle::ConditionallySelectable<[@T; @N]>}::conditional_select"]
axiom Array.Insts.SubtleConditionallySelectable.conditional_select
  {T : Type} {N : Std.Usize} (ConditionallySelectableInst :
  subtle.ConditionallySelectable T) :
  Array T N → Array T N → subtle.Choice → Result (Array T N)

/-- [subtle::{impl subtle::ConditionallyNegatable for T}::conditional_negate]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/subtle-2.6.1/src/lib.rs', lines 620:4-620:52
    Name pattern: [subtle::{subtle::ConditionallyNegatable<@T>}::conditional_negate]
    Visibility: public -/
@[rust_fun "subtle::{subtle::ConditionallyNegatable<@T>}::conditional_negate"]
axiom subtle.ConditionallyNegatable.Blanket.conditional_negate
  {T : Type} (ConditionallySelectableInst : subtle.ConditionallySelectable T)
  (coreopsarithNegShared0TTInst : core.ops.arith.Neg T T) :
  T → subtle.Choice → Result T

/-- [subtle::{subtle::CtOption<T>}::new]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/subtle-2.6.1/src/lib.rs', lines 678:4-678:56
    Name pattern: [subtle::{subtle::CtOption<@T>}::new]
    Visibility: public -/
@[rust_fun "subtle::{subtle::CtOption<@T>}::new"]
axiom subtle.CtOption.new
  {T : Type} : T → subtle.Choice → Result (subtle.CtOption T)

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

/-- [zeroize::{impl zeroize::Zeroize for alloc::vec::Vec<Z>}::zeroize]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/zeroize-1.8.2/src/lib.rs', lines 551:4-551:25
    Name pattern: [zeroize::{zeroize::Zeroize<alloc::vec::Vec<@Z>>}::zeroize]
    Visibility: public -/
@[rust_fun "zeroize::{zeroize::Zeroize<alloc::vec::Vec<@Z>>}::zeroize"]
axiom alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize
  {Z : Type} (ZeroizeInst : zeroize.Zeroize Z) :
  alloc.vec.Vec Z → Result (alloc.vec.Vec Z)

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

/-- [curve25519_dalek::montgomery::{impl core::ops::arith::Mul<curve25519_dalek::scalar::Scalar, curve25519_dalek::montgomery::MontgomeryPoint> for &'a curve25519_dalek::montgomery::MontgomeryPoint}::mul]:
    Source: 'curve25519-dalek/src/macros.rs', lines 100:12-102:13
    Visibility: public -/
axiom SharedAMontgomeryPoint.Insts.CoreOpsArithMulScalarMontgomeryPoint.mul
  :
  montgomery.MontgomeryPoint → scalar.Scalar → Result
    montgomery.MontgomeryPoint

/-- [curve25519_dalek::montgomery::{impl core::ops::arith::Mul<curve25519_dalek::montgomery::MontgomeryPoint, curve25519_dalek::montgomery::MontgomeryPoint> for &'a curve25519_dalek::scalar::Scalar}::mul]:
    Source: 'curve25519-dalek/src/macros.rs', lines 100:12-102:13
    Visibility: public -/
axiom SharedAScalar.Insts.CoreOpsArithMulMontgomeryPointMontgomeryPoint.mul
  :
  scalar.Scalar → montgomery.MontgomeryPoint → Result
    montgomery.MontgomeryPoint

/-- [curve25519_dalek::montgomery::{impl core::ops::arith::Mul<curve25519_dalek::scalar::Scalar, curve25519_dalek::montgomery::MontgomeryPoint> for curve25519_dalek::montgomery::MontgomeryPoint}::mul]:
    Source: 'curve25519-dalek/src/macros.rs', lines 107:12-109:13
    Visibility: public -/
axiom montgomery.MontgomeryPoint.Insts.CoreOpsArithMulScalarMontgomeryPoint.mul
  :
  montgomery.MontgomeryPoint → scalar.Scalar → Result
    montgomery.MontgomeryPoint

/-- [curve25519_dalek::montgomery::{impl core::ops::arith::Mul<curve25519_dalek::montgomery::MontgomeryPoint, curve25519_dalek::montgomery::MontgomeryPoint> for curve25519_dalek::scalar::Scalar}::mul]:
    Source: 'curve25519-dalek/src/macros.rs', lines 107:12-109:13
    Visibility: public -/
axiom scalar.Scalar.Insts.CoreOpsArithMulMontgomeryPointMontgomeryPoint.mul
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

/-- [curve25519_dalek::ristretto::{curve25519_dalek::ristretto::RistrettoPoint}::double_and_compress_batch]:
    Source: 'curve25519-dalek/src/ristretto.rs', lines 568:4-665:5
    Visibility: public -/
axiom ristretto.RistrettoPoint.double_and_compress_batch
  {I : Type} {Clause0_IntoIter : Type}
  (coreitertraitscollectIntoIteratorISharedARistrettoPointClause0_IntoIterInst
  : core.iter.traits.collect.IntoIterator I ristretto.RistrettoPoint
  Clause0_IntoIter) :
  I → Result (alloc.vec.Vec ristretto.CompressedRistretto)
