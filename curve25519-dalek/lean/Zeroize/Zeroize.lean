module
public import Aeneas
public import Curve25519Dalek.Types
@[expose] public section

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

/-! Lean models for the `zeroize::Zeroize`. Volatile writes and memory fences are not observable
in the functional model: zeroizing simply replaces each value with its zero value. -/

/-- Mapping a function that sends every input to the same `z` produces
    `List.replicate`. -/
private theorem List.mapM_with_length_const_spec {α β : Type} (f : α → Result β) (z : β)
    (hz : ∀ x, f x = ok z) (l : List α) :
    List.mapM_with_length f l ⦃ r => r.val = List.replicate l.length z ⦄ := by
  apply spec_mono (List.mapM_with_length_spec (post := fun _ y => y = z) (l := l)
    (by intro i hi; simp [hz, spec_ok]))
  intro r hr
  refine List.eq_replicate_iff.mpr ⟨r.property, fun y hy => ?_⟩
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hy
  exact hr i hi

/-! ### `Zeroize for Z where Z: DefaultIsZeroes` -/

/-- [zeroize::{impl zeroize::Zeroize for Z}::zeroize]:
    Source: 'zeroize-1.8.2/src/lib.rs', lines 301:4-301:25
    Name pattern: [zeroize::{zeroize::Zeroize<@Z>}::zeroize]

    Mirrors `volatile_write(self, Z::default())`: the value is overwritten with
    its `Default`. -/
@[nolint defsWithUnderscore unusedArguments, rust_fun "zeroize::{zeroize::Zeroize<@Z>}::zeroize"]
def zeroize.Zeroize.Blanket.zeroize
  {Z : Type} (DefaultIsZeroesInst : zeroize.DefaultIsZeroes Z) (_self : Z) : Result Z :=
  DefaultIsZeroesInst.coredefaultDefaultInst.default

/-- The blanket `Zeroize` impl replaces the value by `Z::default()`.
    Docs: zeroize-1.8.2/src/lib.rs:297-304. -/
@[step]
theorem zeroize.Zeroize.Blanket.zeroize_spec
    {Z : Type} (inst : zeroize.DefaultIsZeroes Z) (d : Z)
    (hd : inst.coredefaultDefaultInst.default = ok d) (x : Z) :
    zeroize.Zeroize.Blanket.zeroize inst x ⦃ (r : Z) => r = d ⦄ := by
  unfold zeroize.Zeroize.Blanket.zeroize; simp [hd, spec_ok]

/-! ### `Zeroize for IterMut<'_, Z>` -/

/-- [zeroize::{impl zeroize::Zeroize for core::slice::iter::IterMut<'_0, Z>}::zeroize]:
    Source: 'zeroize-1.8.2/src/lib.rs', lines 385:4-385:25
    Name pattern: [zeroize::{zeroize::Zeroize<core::slice::iter::IterMut<'0, @Z>>}::zeroize]

    Mirrors `for elem in self { elem.zeroize(); }`: every element not yet yielded
    by the iterator (indices `it.i ..`) is zeroized and the iterator is left
    exhausted. The zeroized elements are written into the returned iterator, so
    the backward function (ending the `'0` borrow) is the identity. -/
@[nolint defsWithUnderscore, rust_fun
  "zeroize::{zeroize::Zeroize<core::slice::iter::IterMut<'0, @Z>>}::zeroize"]
def core.slice.iter.IterMut.Insts.ZeroizeZeroize.zeroize
  {Z : Type} (ZeroizeInst : zeroize.Zeroize Z) (it : core.slice.iter.IterMut Z) :
  Result ((core.slice.iter.IterMut Z) ×
    (core.slice.iter.IterMut Z → core.slice.iter.IterMut Z)) := do
  let rest ← List.mapM_with_length ZeroizeInst.zeroize (it.slice.val.drop it.i)
  let slice : Slice Z :=
    .from (it.slice.val.take it.i ++ rest.val) (by
      have h := rest.property
      have := it.slice.property
      simp only [List.length_append, List.length_take, List.length_drop] at h ⊢
      omega)
  ok ({ slice, i := slice.length }, id)

/-- Zeroizing an `IterMut` whose element `zeroize` always yields `z` keeps the
    already-yielded prefix, replaces the remaining elements by `z`, and exhausts
    the iterator; the backward function is the identity.
    Docs: zeroize-1.8.2/src/lib.rs:381-390. -/
@[step]
theorem core.slice.iter.IterMut.Insts.ZeroizeZeroize.zeroize_spec
    {Z : Type} (inst : zeroize.Zeroize Z) (z : Z) (hz : ∀ x, inst.zeroize x = ok z)
    (it : core.slice.iter.IterMut Z) :
    core.slice.iter.IterMut.Insts.ZeroizeZeroize.zeroize inst it ⦃
      (r : (core.slice.iter.IterMut Z) ×
        (core.slice.iter.IterMut Z → core.slice.iter.IterMut Z)) =>
        r.1.slice.val = it.slice.val.take it.i ++
          List.replicate (it.slice.length - it.i) z ∧
        r.1.i = it.slice.length ∧ r.2 = id ⦄ := by
  unfold core.slice.iter.IterMut.Insts.ZeroizeZeroize.zeroize
  apply spec_bind (List.mapM_with_length_const_spec inst.zeroize z hz _)
  intro rest hrest
  simp only [spec_ok, Slice.from_val, hrest, List.length_drop, Slice.length,
    List.length_append, List.length_take, List.length_replicate, true_and, and_true]
  omega

/-! ### `Zeroize for [Z; N]` -/

/-- [zeroize::{impl zeroize::Zeroize for [Z; N]}::zeroize]:
    Source: 'zeroize-1.8.2/src/lib.rs', lines 373:4-373:25
    Name pattern: [zeroize::{zeroize::Zeroize<[@Z; @N]>}::zeroize]

    Mirrors `self.iter_mut().zeroize()`. -/
@[nolint defsWithUnderscore, rust_fun "zeroize::{zeroize::Zeroize<[@Z; @N]>}::zeroize"]
def Array.Insts.ZeroizeZeroize.zeroize
  {Z : Type} {N : Std.Usize} (ZeroizeInst : zeroize.Zeroize Z) (a : Array Z N) :
  Result (Array Z N) := do
  let (s, to_slice_mut_back) ← lift (Array.to_slice_mut a)
  let (im, iter_mut_back) ← core.slice.Slice.iter_mut s
  let (im1, zeroize_back) ←
    core.slice.iter.IterMut.Insts.ZeroizeZeroize.zeroize ZeroizeInst im
  ok (to_slice_mut_back (iter_mut_back (zeroize_back im1)))

/-- Zeroizing an array whose element `zeroize` always yields `z` produces the
    array with every element equal to `z`. Docs: zeroize-1.8.2/src/lib.rs:368-375. -/
@[step]
theorem Array.Insts.ZeroizeZeroize.zeroize_spec
    {Z : Type} {N : Std.Usize} (inst : zeroize.Zeroize Z) (z : Z)
    (hz : ∀ x, inst.zeroize x = ok z) (a : Array Z N) :
    Array.Insts.ZeroizeZeroize.zeroize inst a ⦃ (r : Array Z N) =>
      r = Array.repeat N z ⦄ := by
  unfold Array.Insts.ZeroizeZeroize.zeroize
  simp only [lift, Array.to_slice_mut, core.slice.Slice.iter_mut, bind_ok]
  apply spec_bind (core.slice.iter.IterMut.Insts.ZeroizeZeroize.zeroize_spec inst z hz _)
  rintro ⟨it, back⟩ ⟨h1, h2, rfl⟩
  exact (spec_ok _).mpr (by
    simp only [id] at h1 h2 ⊢
    ext1
    rw [Array.from_slice_val] <;> simp_all [Array.to_slice, Array.repeat_val])

/-! ### `Zeroize for Vec<Z>` -/

/-- [zeroize::{impl zeroize::Zeroize for alloc::vec::Vec<Z>}::zeroize]:
    Source: 'zeroize-1.8.2/src/lib.rs', lines 551:4-551:25
    Name pattern: [zeroize::{zeroize::Zeroize<alloc::vec::Vec<@Z>>}::zeroize]

    Mirrors the Rust body: `self.iter_mut().zeroize()` zeroizes every element,
    then `self.clear()` sets the length to `0`, then
    `self.spare_capacity_mut().zeroize()` zeroes the (unmodelled) spare
    capacity. The result is therefore the empty vector. -/
@[nolint defsWithUnderscore, rust_fun "zeroize::{zeroize::Zeroize<alloc::vec::Vec<@Z>>}::zeroize"]
def alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize
  {Z : Type} (ZeroizeInst : zeroize.Zeroize Z) (v : alloc.vec.Vec Z) :
  Result (alloc.vec.Vec Z) := do
  let (im, _iter_mut_back) ← core.slice.Slice.iter_mut v.slice
  let _ ← core.slice.iter.IterMut.Insts.ZeroizeZeroize.zeroize ZeroizeInst im
  ok (alloc.vec.Vec.new Z)

/-- Zeroizing a `Vec` (whose element `zeroize` succeeds) leaves it empty: the
    elements are zeroized and then the vector is `clear`ed.
    Docs: zeroize-1.8.2/src/lib.rs:542-559. -/
@[step]
theorem alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize_spec
    {Z : Type} (inst : zeroize.Zeroize Z) (z : Z) (hz : ∀ x, inst.zeroize x = ok z)
    (v : alloc.vec.Vec Z) :
    alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize inst v ⦃ (r : alloc.vec.Vec Z) =>
      r = alloc.vec.Vec.new Z ⦄ := by
  unfold alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize
  simp only [core.slice.Slice.iter_mut, bind_ok]
  apply spec_bind (core.slice.iter.IterMut.Insts.ZeroizeZeroize.zeroize_spec inst z hz _)
  intro _ _
  simp [spec_ok]
