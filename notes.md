# To do

1. Add std lib models to Aeneas
2. Incorporate all proofs
  - Serial 64 backend (field.rs, scalar.rs)
  - primality of p, L: currently axioms (see below)
  - src/field.rs
  - src/scalar.rs
  - Serial 32 backend
  - Elliptic curves
  - All the other files
3. Make it so Aeneas supports project-defined traits for external-crate (see below)
4. Incorporate the new formalisation of elliptic curve models

## Conventions

The repository layout, translation rules, external-crate libraries and the spec/proof
conventions are in `verif-guidelines.md`.

## To do: shorter target names

Rename the four translation targets to `x86_64`, `x86_64_no_tables`, `i686`, `i686_no_tables`
(valid Lean identifiers, so no `«…»`): in `scripts/aeneas-translate.sh`, use JSON target specs
(copied from `rustc --print target-spec-json`) for all four configurations, so that the spec file
names become the target names. Then retranslate and rename the per-target spec statements
(`….«x86_64-unknown-linux-gnu_spec»` → `….x86_64_spec`, etc.) and the docs.

## To do: primality of `p` and `L` (currently axioms)

`curve25519.p_prime` and `curve25519.L_prime` in `Curve25519/Prime.lean` are axioms for now, so
they appear in the `#print axioms` lists of every spec that uses them. Replace them with proofs by
`PrimeCert` (https://github.com/b-mehta/PrimeCert, Pocklington certificates checked by the
kernel) when the toolchain is updated: its releases before v4.33.0 do not use the module system,
and Lean refuses non-module imports from our module files. Certificates for both numbers are in
the old project (`~/Projects/curve25519-dalek-lean-verify/Curve25519Dalek/Math/PrimeCerts.lean`).
Fallback that works today: Lucas/Pratt certificates with Mathlib's `lucas_primality` and
`reduce_mod_char` (17 certificates, builds in ~2 s; not committed).

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

## To do: decide what to do about copyright headers

Currently the Lean files have nothing. Copy across from the previous files in the original Dalek project?

## Spec campaign status

- `src/backend/serial/u64/field.rs`, `scalar.rs`, `constants.rs`: all statements proved (no
  `sorryAx`); audit modules in the strict CI build. The `EdwardsPoint` constants and tables wait
  for the curve model.
- `src/field.rs` (u64 backend, `FieldElement51`): all statements proved; in the strict CI build.
  `invert`, `sqrt_ratio_i`, `invsqrt` and the batch inversions rest on the axiom `p_prime`.
- Next: `src/scalar.rs` (the `Scalar` type).
