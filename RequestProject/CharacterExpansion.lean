import Mathlib

/-! Finite character orthogonality core for the prime/unit expansion.
The Gauss-sum Fourier formula itself remains externally audited in the ledger. -/

namespace ShiftedMobiusBank

/-- Finite orthogonality over all complex Dirichlet characters. For prime `p`,
`p.totient = p - 1`, giving the denominator in the standard expansion. -/
theorem FINITE_MULTIPLICATIVE_CHARACTER_ORTHOGONALITY
    (p : ℕ) [NeZero p] (a : ZMod p) :
    ∑ χ : DirichletCharacter ℂ p, χ a =
      if a = 1 then (p.totient : ℂ) else 0 := by
  exact DirichletCharacter.sum_characters_eq ℂ a

/-- Unit-to-unit delta orthogonality, the exact finite core used to derive the
multiplicative character expansion of an additive character. -/
theorem FINITE_MULTIPLICATIVE_CHARACTER_EXPANSION_CORE
    (p : ℕ) [NeZero p] {a : ZMod p} (ha : IsUnit a) (b : ZMod p) :
    ∑ χ : DirichletCharacter ℂ p, χ a⁻¹ * χ b =
      if a = b then (p.totient : ℂ) else 0 := by
  exact DirichletCharacter.sum_char_inv_mul_char_eq ℂ ha b

end ShiftedMobiusBank
