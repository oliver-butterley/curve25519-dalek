module
public import Mathlib.Data.ZMod.Basic
@[expose] public section

/-! # Curve25519 parameters

The field prime, the prime-order subgroup's order, and the constants of the twisted Edwards form
`a x² + y² = 1 + d x² y²` (RFC 8032 §5.1) and the Montgomery form `y² = x³ + A x² + x`
(RFC 7748 §4.1). -/

namespace curve25519

/-- The field prime `p = 2^255 - 19`. -/
def p : ℕ := 2 ^ 255 - 19

/-- The order of the prime-order subgroup, `ℓ = 2^252 + 27742317777372353535851937790883648493`. -/
def L : ℕ := 2 ^ 252 + 27742317777372353535851937790883648493

/-- The Edwards coefficient `a = -1`. -/
def a : ZMod p := -1

/-- The Edwards coefficient `d = -121665 / 121666`. -/
def d : ZMod p := -121665 * (121666 : ZMod p)⁻¹

/-- The Montgomery coefficient `A = 486662`. -/
def A : ℕ := 486662

end curve25519
