import Aeneas
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option linter.style.whitespace false
set_option linter.style.setOption false
set_option linter.style.longLine false

/-- [subtle::Choice]
    Source: 'subtle-2.6.1/src/lib.rs', lines 120:0-120:17
    Name pattern: [subtle::Choice]

    `subtle::Choice` is a single-field tuple struct `struct Choice(u8)`. Aeneas
    renders single-field tuple structs as a reducible alias to the inner type
    (cf. `FieldElement51 := Array U64 5`), so we model it as a reducible alias to
    `U8`. The 0/1 invariant is NOT baked into the type; see `Choice.IsValid`. -/
@[reducible, rust_type "subtle::Choice"]
def subtle.Choice : Type := Std.U8

/-- [subtle::CtOption]
    Source: 'subtle-2.6.1/src/lib.rs', lines 647:0-647:22
    Name pattern: [subtle::CtOption]

    `struct CtOption<T> { value: T, is_some: Choice }`. -/
structure subtle.CtOption (T : Type) where
  value : T
  is_some : subtle.Choice

/-- The canonical "false" `Choice`. -/
def Choice.zero : subtle.Choice := 0#u8

/-- The canonical "true" `Choice`. -/
def Choice.one : subtle.Choice := 1#u8

/-- A `Choice` is valid when its underlying byte is `0` or `1`.

    Since `subtle.Choice` is definitionally `U8`, this predicate is NOT always
    true: producers must establish it and consumers may rely on it. -/
def subtle.Choice.IsValid (c : subtle.Choice) : Prop := c = 0#u8 ∨ c = 1#u8

@[simp] theorem Choice.zero_eq : Choice.zero = 0#u8 := rfl
@[simp] theorem Choice.one_eq : Choice.one = 1#u8 := rfl

@[simp] theorem Choice.isValid_zero : subtle.Choice.IsValid Choice.zero := Or.inl rfl
@[simp] theorem Choice.isValid_one : subtle.Choice.IsValid Choice.one := Or.inr rfl

@[simp] theorem Choice.one_ne_zero : Choice.one ≠ Choice.zero := by decide
@[simp] theorem Choice.zero_ne_one : Choice.zero ≠ Choice.one := by decide

/-- A valid `Choice` is either `Choice.zero` or `Choice.one`. -/
theorem Choice.isValid_eq_zero_or_one {c : subtle.Choice} (h : subtle.Choice.IsValid c) :
    c = Choice.zero ∨ c = Choice.one := h
