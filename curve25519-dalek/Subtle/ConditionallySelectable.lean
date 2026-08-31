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

/-! ### `ConditionallySelectable for u8` -/

/-- [subtle::{impl subtle::ConditionallySelectable for u8}::conditional_select]:
    Name pattern: [subtle::{subtle::ConditionallySelectable<u8>}::conditional_select] -/
@[rust_fun "subtle::{subtle::ConditionallySelectable<u8>}::conditional_select"]
def U8.Insts.SubtleConditionallySelectable.conditional_select
  (a : Std.U8) (b : Std.U8) (choice : subtle.Choice) : Result Std.U8 :=
  ok (if choice = 1#u8 then b else a)

/-- `conditional_select` returns `a` when `choice == Choice(0)` and `b` when
    `choice == Choice(1)`. Docs: subtle-2.6.1/src/lib.rs:395-420. -/
@[step]
theorem U8.Insts.SubtleConditionallySelectable.conditional_select_spec
    (a b : Std.U8) (choice : subtle.Choice) :
    U8.Insts.SubtleConditionallySelectable.conditional_select a b choice ⦃
      (res : Std.U8) =>
        (choice = Choice.zero → res = a) ∧ (choice = Choice.one → res = b) ⦄ := by
  unfold U8.Insts.SubtleConditionallySelectable.conditional_select
  simp only [spec_ok, Choice.zero, Choice.one]
  refine ⟨fun h => ?_, fun h => ?_⟩ <;> subst h <;> simp

/-- [subtle::{impl subtle::ConditionallySelectable for u8}::conditional_assign]:
    Name pattern: [subtle::{subtle::ConditionallySelectable<u8>}::conditional_assign] -/
@[rust_fun "subtle::{subtle::ConditionallySelectable<u8>}::conditional_assign"]
def U8.Insts.SubtleConditionallySelectable.conditional_assign
  (a : Std.U8) (b : Std.U8) (choice : subtle.Choice) : Result Std.U8 :=
  ok (if choice = 1#u8 then b else a)

/-- `conditional_assign(self, other, choice)` assigns `other` to `self` when
    `choice == Choice(1)`, leaving it unchanged when `choice == Choice(0)`.
    Docs: subtle-2.6.1/src/lib.rs:421-443. -/
@[step]
theorem U8.Insts.SubtleConditionallySelectable.conditional_assign_spec
    (a b : Std.U8) (choice : subtle.Choice) :
    U8.Insts.SubtleConditionallySelectable.conditional_assign a b choice ⦃
      (res : Std.U8) =>
        (choice = Choice.zero → res = a) ∧ (choice = Choice.one → res = b) ⦄ := by
  unfold U8.Insts.SubtleConditionallySelectable.conditional_assign
  simp only [spec_ok, Choice.zero, Choice.one]
  refine ⟨fun h => ?_, fun h => ?_⟩ <;> subst h <;> simp

/-- [subtle::{impl subtle::ConditionallySelectable for u8}::conditional_swap]:
    Name pattern: [subtle::{subtle::ConditionallySelectable<u8>}::conditional_swap] -/
@[rust_fun "subtle::{subtle::ConditionallySelectable<u8>}::conditional_swap"]
def U8.Insts.SubtleConditionallySelectable.conditional_swap
  (a : Std.U8) (b : Std.U8) (choice : subtle.Choice) : Result (Std.U8 × Std.U8) :=
  ok (if choice = 1#u8 then (b, a) else (a, b))

/-- `conditional_swap(a, b, choice)` swaps `a` and `b` when `choice == Choice(1)`,
    leaving them unchanged when `choice == Choice(0)`.
    Docs: subtle-2.6.1/src/lib.rs:445-473. -/
@[step]
theorem U8.Insts.SubtleConditionallySelectable.conditional_swap_spec
    (a b : Std.U8) (choice : subtle.Choice) :
    U8.Insts.SubtleConditionallySelectable.conditional_swap a b choice ⦃
      (res : Std.U8 × Std.U8) =>
        (choice = Choice.zero → res = (a, b)) ∧ (choice = Choice.one → res = (b, a)) ⦄ := by
  unfold U8.Insts.SubtleConditionallySelectable.conditional_swap
  simp only [spec_ok, Choice.zero, Choice.one]
  refine ⟨fun h => ?_, fun h => ?_⟩ <;> subst h <;> simp

/-! ### `ConditionallySelectable for u64` -/

/-- [subtle::{impl subtle::ConditionallySelectable for u64}::conditional_select]:
    Name pattern: [subtle::{subtle::ConditionallySelectable<u64>}::conditional_select] -/
@[rust_fun "subtle::{subtle::ConditionallySelectable<u64>}::conditional_select"]
def U64.Insts.SubtleConditionallySelectable.conditional_select
  (a : Std.U64) (b : Std.U64) (choice : subtle.Choice) : Result Std.U64 :=
  ok (if choice = 1#u8 then b else a)

/-- `conditional_select` returns `a` when `choice == Choice(0)` and `b` when
    `choice == Choice(1)`. Docs: subtle-2.6.1/src/lib.rs:395-420. -/
@[step]
theorem U64.Insts.SubtleConditionallySelectable.conditional_select_spec
    (a b : Std.U64) (choice : subtle.Choice) :
    U64.Insts.SubtleConditionallySelectable.conditional_select a b choice ⦃
      (res : Std.U64) =>
        (choice = Choice.zero → res = a) ∧ (choice = Choice.one → res = b) ⦄ := by
  unfold U64.Insts.SubtleConditionallySelectable.conditional_select
  simp only [spec_ok, Choice.zero, Choice.one]
  refine ⟨fun h => ?_, fun h => ?_⟩ <;> subst h <;> simp

/-- [subtle::{impl subtle::ConditionallySelectable for u64}::conditional_assign]:
    Name pattern: [subtle::{subtle::ConditionallySelectable<u64>}::conditional_assign] -/
@[rust_fun "subtle::{subtle::ConditionallySelectable<u64>}::conditional_assign"]
def U64.Insts.SubtleConditionallySelectable.conditional_assign
  (a : Std.U64) (b : Std.U64) (choice : subtle.Choice) : Result Std.U64 :=
  ok (if choice = 1#u8 then b else a)

/-- `conditional_assign(self, other, choice)` assigns `other` to `self` when
    `choice == Choice(1)`, leaving it unchanged when `choice == Choice(0)`.
    Docs: subtle-2.6.1/src/lib.rs:421-443. -/
@[step]
theorem U64.Insts.SubtleConditionallySelectable.conditional_assign_spec
    (a b : Std.U64) (choice : subtle.Choice) :
    U64.Insts.SubtleConditionallySelectable.conditional_assign a b choice ⦃
      (res : Std.U64) =>
        (choice = Choice.zero → res = a) ∧ (choice = Choice.one → res = b) ⦄ := by
  unfold U64.Insts.SubtleConditionallySelectable.conditional_assign
  simp only [spec_ok, Choice.zero, Choice.one]
  refine ⟨fun h => ?_, fun h => ?_⟩ <;> subst h <;> simp

/-- [subtle::{impl subtle::ConditionallySelectable for u64}::conditional_swap]:
    Name pattern: [subtle::{subtle::ConditionallySelectable<u64>}::conditional_swap] -/
@[rust_fun "subtle::{subtle::ConditionallySelectable<u64>}::conditional_swap"]
def U64.Insts.SubtleConditionallySelectable.conditional_swap
  (a : Std.U64) (b : Std.U64) (choice : subtle.Choice) : Result (Std.U64 × Std.U64) :=
  ok (if choice = 1#u8 then (b, a) else (a, b))

/-- `conditional_swap(a, b, choice)` swaps `a` and `b` when `choice == Choice(1)`,
    leaving them unchanged when `choice == Choice(0)`.
    Docs: subtle-2.6.1/src/lib.rs:445-473. -/
@[step]
theorem U64.Insts.SubtleConditionallySelectable.conditional_swap_spec
    (a b : Std.U64) (choice : subtle.Choice) :
    U64.Insts.SubtleConditionallySelectable.conditional_swap a b choice ⦃
      (res : Std.U64 × Std.U64) =>
        (choice = Choice.zero → res = (a, b)) ∧ (choice = Choice.one → res = (b, a)) ⦄ := by
  unfold U64.Insts.SubtleConditionallySelectable.conditional_swap
  simp only [spec_ok, Choice.zero, Choice.one]
  refine ⟨fun h => ?_, fun h => ?_⟩ <;> subst h <;> simp

/-! ### `ConditionallySelectable for u32` (needed by the serial u32 backend) -/

/-- [subtle::{impl subtle::ConditionallySelectable for u32}::conditional_select]:
    Name pattern: [subtle::{subtle::ConditionallySelectable<u32>}::conditional_select] -/
@[rust_fun "subtle::{subtle::ConditionallySelectable<u32>}::conditional_select"]
def U32.Insts.SubtleConditionallySelectable.conditional_select
  (a : Std.U32) (b : Std.U32) (choice : subtle.Choice) : Result Std.U32 :=
  ok (if choice = 1#u8 then b else a)

/-- `conditional_select` returns `a` when `choice == Choice(0)` and `b` when
    `choice == Choice(1)`. Docs: subtle-2.6.1/src/lib.rs:395-420. -/
@[step]
theorem U32.Insts.SubtleConditionallySelectable.conditional_select_spec
    (a b : Std.U32) (choice : subtle.Choice) :
    U32.Insts.SubtleConditionallySelectable.conditional_select a b choice ⦃
      (res : Std.U32) =>
        (choice = Choice.zero → res = a) ∧ (choice = Choice.one → res = b) ⦄ := by
  unfold U32.Insts.SubtleConditionallySelectable.conditional_select
  simp only [spec_ok, Choice.zero, Choice.one]
  refine ⟨fun h => ?_, fun h => ?_⟩ <;> subst h <;> simp

/-- [subtle::{impl subtle::ConditionallySelectable for u32}::conditional_assign]:
    Name pattern: [subtle::{subtle::ConditionallySelectable<u32>}::conditional_assign] -/
@[rust_fun "subtle::{subtle::ConditionallySelectable<u32>}::conditional_assign"]
def U32.Insts.SubtleConditionallySelectable.conditional_assign
  (a : Std.U32) (b : Std.U32) (choice : subtle.Choice) : Result Std.U32 :=
  ok (if choice = 1#u8 then b else a)

/-- `conditional_assign(self, other, choice)` assigns `other` to `self` when
    `choice == Choice(1)`, leaving it unchanged when `choice == Choice(0)`.
    Docs: subtle-2.6.1/src/lib.rs:421-443. -/
@[step]
theorem U32.Insts.SubtleConditionallySelectable.conditional_assign_spec
    (a b : Std.U32) (choice : subtle.Choice) :
    U32.Insts.SubtleConditionallySelectable.conditional_assign a b choice ⦃
      (res : Std.U32) =>
        (choice = Choice.zero → res = a) ∧ (choice = Choice.one → res = b) ⦄ := by
  unfold U32.Insts.SubtleConditionallySelectable.conditional_assign
  simp only [spec_ok, Choice.zero, Choice.one]
  refine ⟨fun h => ?_, fun h => ?_⟩ <;> subst h <;> simp

/-- [subtle::{impl subtle::ConditionallySelectable for u32}::conditional_swap]:
    Name pattern: [subtle::{subtle::ConditionallySelectable<u32>}::conditional_swap] -/
@[rust_fun "subtle::{subtle::ConditionallySelectable<u32>}::conditional_swap"]
def U32.Insts.SubtleConditionallySelectable.conditional_swap
  (a : Std.U32) (b : Std.U32) (choice : subtle.Choice) : Result (Std.U32 × Std.U32) :=
  ok (if choice = 1#u8 then (b, a) else (a, b))

/-- `conditional_swap(a, b, choice)` swaps `a` and `b` when `choice == Choice(1)`,
    leaving them unchanged when `choice == Choice(0)`.
    Docs: subtle-2.6.1/src/lib.rs:445-473. -/
@[step]
theorem U32.Insts.SubtleConditionallySelectable.conditional_swap_spec
    (a b : Std.U32) (choice : subtle.Choice) :
    U32.Insts.SubtleConditionallySelectable.conditional_swap a b choice ⦃
      (res : Std.U32 × Std.U32) =>
        (choice = Choice.zero → res = (a, b)) ∧ (choice = Choice.one → res = (b, a)) ⦄ := by
  unfold U32.Insts.SubtleConditionallySelectable.conditional_swap
  simp only [spec_ok, Choice.zero, Choice.one]
  refine ⟨fun h => ?_, fun h => ?_⟩ <;> subst h <;> simp

/-! ### `ConditionallySelectable for [T; N]` -/

/-- [subtle::{impl subtle::ConditionallySelectable for [T; N]}::conditional_select]:
    Name pattern: [subtle::{subtle::ConditionallySelectable<[@T; @N]>}::conditional_select] -/
@[rust_fun "subtle::{subtle::ConditionallySelectable<[@T; @N]>}::conditional_select"]
def Array.Insts.SubtleConditionallySelectable.conditional_select
  {T : Type} {N : Std.Usize} (_ConditionallySelectableInst : subtle.ConditionallySelectable T)
  (a : Array T N) (b : Array T N) (choice : subtle.Choice) : Result (Array T N) :=
  ok (if choice = 1#u8 then b else a)

/-- `conditional_select` returns `a` when `choice == Choice(0)` and `b` when
    `choice == Choice(1)` (element-wise). Docs: subtle-2.6.1/src/lib.rs:395-420. -/
@[step]
theorem Array.Insts.SubtleConditionallySelectable.conditional_select_spec
    {T : Type} {N : Std.Usize} (inst : subtle.ConditionallySelectable T)
    (a b : Array T N) (choice : subtle.Choice) :
    Array.Insts.SubtleConditionallySelectable.conditional_select inst a b choice ⦃
      (res : Array T N) =>
        (choice = Choice.zero → res = a) ∧ (choice = Choice.one → res = b) ⦄ := by
  unfold Array.Insts.SubtleConditionallySelectable.conditional_select
  simp only [spec_ok, Choice.zero, Choice.one]
  refine ⟨fun h => ?_, fun h => ?_⟩ <;> subst h <;> simp

/-! ### Trait-default methods

    These provided-method defaults are kept as concrete `def`s. Aeneas elaborates
    every downstream `ConditionallySelectable` impl (e.g. the curve point types)
    as an `impl_def` that INHERITS these; that macro can only resolve the
    inherited (recursively self-referential) fields when the default has a
    concrete body. Each body matches the `subtle` docs, so no separate spec is
    needed (the body IS the characterisation). -/

/-- [subtle::ConditionallySelectable::conditional_assign]:
    Name pattern: [subtle::ConditionallySelectable::conditional_assign]

    Default: `conditional_assign(self, other, choice) = conditional_select(self,
    other, choice)`. Docs: subtle-2.6.1/src/lib.rs:441-443. -/
@[trait_default, rust_fun "subtle::ConditionallySelectable::conditional_assign"]
def subtle.ConditionallySelectable.conditional_assign.default
  {Self : Type} (ConditionallySelectableInst : subtle.ConditionallySelectable Self) :
  Self → Self → subtle.Choice → Result Self :=
  fun a b choice => ConditionallySelectableInst.conditional_select a b choice

/-- [subtle::ConditionallySelectable::conditional_swap]:
    Name pattern: [subtle::ConditionallySelectable::conditional_swap]

    Default: reassign `a := select(a, b, choice)` and `b := select(b, a₀, choice)`
    (with `a₀` the original `a`), i.e. swap iff `choice == Choice(1)`.
    Docs: subtle-2.6.1/src/lib.rs:469-473. -/
@[trait_default, rust_fun "subtle::ConditionallySelectable::conditional_swap"]
def subtle.ConditionallySelectable.conditional_swap.default
  {Self : Type} (ConditionallySelectableInst : subtle.ConditionallySelectable Self) :
  Self → Self → subtle.Choice → Result (Self × Self) :=
  fun a b choice => do
    let a_new ← ConditionallySelectableInst.conditional_select a b choice
    let b_new ← ConditionallySelectableInst.conditional_select b a choice
    ok (a_new, b_new)

/-! ### `ConditionallyNegatable::conditional_negate` -/

/-- [subtle::{impl subtle::ConditionallyNegatable for T}::conditional_negate]:
    Name pattern: [subtle::{subtle::ConditionallyNegatable<@T>}::conditional_negate]

    Negate `self` when `choice == Choice(1)`, otherwise leave it unchanged;
    implemented as `conditional_select(self, -self, choice)`.
    Docs: subtle-2.6.1/src/lib.rs:604-624. -/
@[rust_fun "subtle::{subtle::ConditionallyNegatable<@T>}::conditional_negate"]
def subtle.ConditionallyNegatable.Blanket.conditional_negate
  {T : Type} (ConditionallySelectableInst : subtle.ConditionallySelectable T)
  (coreopsarithNegShared0TTInst : core.ops.arith.Neg T T) :
  T → subtle.Choice → Result T :=
  fun self choice => do
    let self_neg ← coreopsarithNegShared0TTInst.neg self
    ConditionallySelectableInst.conditional_select self self_neg choice
