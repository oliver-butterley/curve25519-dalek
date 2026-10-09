module
public import Specs.Lemmas.Array
public import Specs.Lemmas.Bitwise
public section

/-! # Opt-in `step` specifications

Alternative `step` specifications for library functions, registered as scoped attributes so that a
proof activates them with `open scoped …`. They are registered once, here: re-registering a `step`
theorem in a file that imports another registration triggers a warning. -/

open Aeneas Aeneas.Std

/- Array and slice reads and updates described with `getElem!`. -/
namespace Specs.GetElemSteps
attribute [scoped step] Array.index_usize_getElem!_spec Slice.index_usize_getElem!_spec
  Array.update_getElem!_spec
end Specs.GetElemSteps

/- Masking with `2 ^ n - 1` as reduction modulo `2 ^ n` (`n` is inferred from a local
hypothesis `m.val = 2 ^ n - 1`). -/
namespace Specs.MaskStep
attribute [scoped step] UScalar.and_two_pow_sub_one_spec
end Specs.MaskStep
