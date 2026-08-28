-- [curve25519_dalek]: external types.
import Aeneas
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

/-- [core::iter::sources::empty::Empty]
    Source: '/rustc/library/core/src/iter/sources/empty.rs', lines 30:0-30:19
    Name pattern: [core::iter::sources::empty::Empty]
    Visibility: public -/
@[rust_type "core::iter::sources::empty::Empty"]
axiom core.iter.sources.empty.Empty (T : Type) : Type

/-- [core::slice::iter::Chunks]
    Source: '/rustc/library/core/src/slice/iter.rs', lines 1478:0-1478:28
    Name pattern: [core::slice::iter::Chunks]
    Visibility: public -/
@[rust_type "core::slice::iter::Chunks"]
axiom core.slice.iter.Chunks (T : Type) : Type

/-- [subtle::Choice]
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/subtle-2.6.1/src/lib.rs', lines 120:0-120:17
    Name pattern: [subtle::Choice]
    Visibility: public -/
@[rust_type "subtle::Choice"]
axiom subtle.Choice : Type

/-- [subtle::CtOption]
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/subtle-2.6.1/src/lib.rs', lines 647:0-647:22
    Name pattern: [subtle::CtOption]
    Visibility: public -/
@[rust_type "subtle::CtOption"]
axiom subtle.CtOption (T : Type) : Type
