module
public import Curve25519
public section

/-! # Lemmas shared by the proofs of `field.rs` -/

namespace Curve25519Dalek.field

open curve25519

theorem one_mod_p : 1 % p = 1 :=
  Nat.mod_eq_of_lt (by have := p_add_nineteen; omega)

end Curve25519Dalek.field
