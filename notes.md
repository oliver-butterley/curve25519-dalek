## Plan for integrating Lean proof code into curve25519-dalek:

1. Translation (clean translation of entire crate without tweaks)
2. Std lib models ~100 (upstream models to Aeneas)
3. Adjust spec statements to fit Michael's preferences (very little to do following latest discussion)
4. Incorporate the new formalisation of elliptic curve models (a version has already been prepared)
5. Additional specs and proofs (for new parts in updated Rust code)
6. Shadow main repo to test workflow of updating proofs

## Translation workflow

```
./scripts/aeneas-install.sh     # charon + aeneas for the release pinned in lakefile.toml
./scripts/aeneas-translate.sh   # apply curve25519-dalek/translation-patches/, run charon + aeneas, revert patches
```

## CI 

- `lean-translation.yml` check that the committed translation is faithful to the source code.
- `lean-build.yml` checks the Lean project builds and runs the linter.

- **External files are hand-written.** `FunsExternal.lean` and `TypesExternal.lean` are never
  overwritten; after each translation compare them against the (gitignored)
  `*External_Template.lean` files Aeneas emits and update them by hand.
- **Rust changes only as translation patches.** `curve25519-dalek/src/` stays upstream. A
  construct Aeneas cannot translate is rewritten in a patch file
  `curve25519-dalek/translation-patches/<file-stem>-<function>.patch`, one per function
  (insert `-<Type>` before `<function>` when the name alone is ambiguous). Its free-text
  header says what changes, why the original does not translate, why behaviour is identical.
  Create using `git diff -W -- <file>`. Patches are applied one by one and reverted in
  reverse order, so each must apply on its own: if two patches touch neighbouring
  functions, trim the context at the boundary so that neither's context contains lines
  the other changes (see `montgomery-MontgomeryPoint-mul.patch` / `scalar-div_by_2.patch`).
- **Charon settings** live in `[package.metadata.charon]` in `curve25519-dalek/Cargo.toml`.
  The crate is translated with its default features (`alloc`, `precomputed-tables`,
  `zeroize`).
  - `exclude`: only items we will never verify (Debug, Hash, derived `Eq`).
  - `opaque`: only items verification needs but we deliberately do not translate (the
    precomputed basepoint table data).
  - Everything else is translated; constructs Aeneas cannot handle are patched.
- **Patches that change behaviour.** Patches must keep behaviour identical, except
  `edwards-multiscalar_mul`, `edwards-optional_multiscalar_mul` and
  `pippenger-optional_multiscalar_mul`. These replace `Iterator::size_hint`, which Aeneas
  cannot model, with the length of the collected inputs; the patch headers spell out the
  difference.

## Std library models

Many more need to be added to Aeneas.
