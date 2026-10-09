## Plan for integrating Lean proof code into curve25519-dalek:

1. Translation (clean translation of entire crate without tweaks)
2. Std lib models ~100 (upstream models to Aeneas)
3. Adjust spec statements to fit Michael's preferences (very little to do following latest discussion)
4. Incorporate the new formalisation of elliptic curve models (a version has already been prepared)
5. Additional specs and proofs (for new parts in updated Rust code)
6. Shadow main repo to test workflow of updating proofs

## Conventions

The repository layout, translation rules, external-crate libraries and the spec/proof
conventions are in `guidelines.md`.

## Specs campaign

One Rust file at a time, starting with the u64 backend (`src/backend/serial/u64/`):
`constants.rs` and `field.rs` have their statements (proofs `sorry`), awaiting review;
`scalar.rs` is next.

To do (later): define `FieldElement51.asNat`, `Scalar52.asNat` and the byte-array `asNat` via one
general radix-`2^k` `Array.asNat`, so that lemmas about it are shared.

## Std library models

Many more need to be added to Aeneas.

## To do: project-defined traits for external-crate libraries

Aeneas generates every external trait used by the crate (`subtle::ConditionallySelectable`,
`zeroize::Zeroize`, ...) into `Curve25519Dalek/Types.lean`, in namespace `curve25519_dalek`. Only
traits in Aeneas's built-in table are skipped, and that table is compiled into the `aeneas` binary
from Aeneas's own Lean library (the `@[rust_trait "..."]` attribute); there is no option to add a
project's own declarations. So `Subtle` (its 5 trait-generic functions) and `Zeroize` (all of it)
depend on the generated types and are specific to this translation.

- Raise upstream: let a project register its own `rust_trait` declarations as built-ins, so the
  trait structures can live in `Subtle`/`Zeroize` themselves and those libraries become
  independent of the curve25519-dalek translation.
- Until then, leave `Subtle` and `Zeroize` as they are. Afterwards: move the trait structures
  into the libraries, and drop their `Curve25519Dalek.Types` imports.
