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

CI (`.github/workflows/lean-translation.yml`) reruns both and fails if the committed
translation differs from the script's output.

- **External files are hand-written.** `FunsExternal.lean` and `TypesExternal.lean` are never
  overwritten; after each translation compare them against the (gitignored)
  `*External_Template.lean` files Aeneas emits and update them by hand.
- **Rust changes only as translation patches.** `curve25519-dalek/src/` stays upstream. A
  construct Aeneas cannot translate is rewritten in a patch file
  `curve25519-dalek/translation-patches/<file-stem>-<function>.patch`, one per function
  (insert `-<Type>` before `<function>` when the name alone is ambiguous). Its free-text
  header says what changes, why the original does not translate, why behaviour is identical.
  Create using `git diff -W -- <file>`.
- **Charon settings** (excluded and opaque items) live in `[package.metadata.charon]` in
  `curve25519-dalek/Cargo.toml`.

## Std library models

Many more need to be added to Aeneas.
