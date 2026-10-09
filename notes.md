# To do

1. Add std lib models to Aeneas
2. Incorporate all proofs
  - Serial 64 backend (field.rs, scalar.rs)
  - primality of p, L
  - src/field.rs
  - src.scalar.rs
  - Serial 32 backend
  - Elliptic curves
  - All the other files
3. Make it so Aeneas supports project-defined traits for external-crate (see below)
4. Incorporate the new formalisation of elliptic curve models

## Conventions

The repository layout, translation rules, external-crate libraries and the spec/proof
conventions are in `verif-guidelines.md`.

## To do: project-defined traits for external-crate libraries

Aeneas generates every external trait used by the crate (`subtle::ConditionallySelectable`,
`zeroize::Zeroize`, ...) into `Curve25519Dalek/Types.lean`, in namespace `curve25519_dalek`. Only
traits in Aeneas's built-in table are skipped, and that table is compiled into the `aeneas` binary
from Aeneas's own Lean library (the `@[rust_trait "..."]` attribute); there is no option to add a
project's own declarations. So `Subtle` (its 5 trait-generic functions) and `Zeroize` (all of it)
depend on the generated types and are specific to this translation.

- Add upstream: let a project register its own `rust_trait` declarations as built-ins, so the
  trait structures can live in `Subtle`/`Zeroize` themselves and those libraries become
  independent of the curve25519-dalek translation.
- Until then, leave `Subtle` and `Zeroize` as they are. Afterwards: move the trait structures
  into the libraries, and drop their `Curve25519Dalek.Types` imports.

## Spec campaign status

- `src/backend/serial/u64/field.rs`, `constants.rs`: all statements proved (no `sorryAx`); audit
  modules in the strict CI build. The `EdwardsPoint` constants and tables wait for the curve model.
- Next: `src/backend/serial/u64/scalar.rs`.
