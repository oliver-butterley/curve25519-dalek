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

/-- [subtle::{subtle::CtOption<T>}::new]:
    Name pattern: [subtle::{subtle::CtOption<@T>}::new] -/
@[rust_fun "subtle::{subtle::CtOption<@T>}::new"]
def subtle.CtOption.new
  {T : Type} (value : T) (is_some : subtle.Choice) : Result (subtle.CtOption T) :=
  ok { value := value, is_some := is_some }

/-- `CtOption::new(value, is_some)` stores `value` and the `is_some` flag; the
    value is always stored (and only exposed when `is_some` is true).
    Docs: subtle-2.6.1/src/lib.rs:671-687. -/
@[step]
theorem subtle.CtOption.new_spec
    {T : Type} (value : T) (is_some : subtle.Choice) :
    subtle.CtOption.new value is_some ⦃ (opt : subtle.CtOption T) =>
      opt.value = value ∧ opt.is_some = is_some ⦄ := by
  unfold subtle.CtOption.new; simp [spec_ok]
