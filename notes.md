## Plan for integrating Lean proof code into curve25519-dalek:

1. Translation (clean translation of entire crate without tweaks)
2. Std lib models ~100 (upstream models to Aeneas)
3. Adjust spec statements to fit Michael's preferences (very little to do following latest discussion)
4. Incorporate the new formalisation of elliptic curve models (a version has already been prepared)
5. Additional specs and proofs (for new parts in updated Rust code)
6. Shadow main repo to test workflow of updating proofs

## Remaining translation issues:

See: https://github.com/Beneficial-AI-Foundation/curve25519-dalek-lean-verify/issues/860

## Std library models

massive overlap with the other repos

Once all translation issues are fixed, produce the definitive list of all std
library functions we need (from `translated/FunsExternal_Template.lean`). The list
is a moving target until then — each translation workaround changes it (e.g. the
iterator→index-loop workarounds dropped the stdlib externals from ~100 to ~40).
Only a clean, final translation gives the stable, authoritative set of models to
implement upstream in Aeneas.