/-
# Gate 1B v8.4 — normalised prime-character collapse

**Status: PROVED_ALGEBRAIC.**

With the standard `√p` normalisation of the Gauss sums, the nonprincipal
collapse of `PrimeCharacterCollapse.lean` reads

  `(1/√p) ∑_{χ ≠ χ₀} τ_p(χ) χ(A) = ((p-1)/√p) ψ(A⁻¹) + 1/√p`.

The correction `1/√p` is recorded as a separate **exact** term
(`primeCollapseCorrection`).  No analytic estimate is made on it.
-/
import Mathlib
import Gate1B.SafeAlgebra.PrimeCharacterCollapse

namespace Gate1B.SafeAlgebra

open Finset

/-- The exact correction term of the normalised prime collapse. -/
noncomputable def primeCollapseCorrection (p : ℕ) : ℂ := 1 / Real.sqrt p

/-- The exact main term coefficient of the normalised prime collapse. -/
noncomputable def primeCollapseMainCoeff (p : ℕ) : ℂ := ((p : ℂ) - 1) / Real.sqrt p

/-- **Normalised prime collapse.** -/
theorem nonprincipal_gauss_collapse_normalized {p : ℕ} [Fact p.Prime]
    {psi : AddChar (ZMod p) ℂ} (hpsi : psi ≠ 1) {A : ZMod p} (hA : IsUnit A) :
    (1 / (Real.sqrt p : ℂ)) *
        ∑ chi ∈ ({1}ᶜ : Finset (DirichletCharacter ℂ p)), gaussSum chi psi * chi A
      = primeCollapseMainCoeff p * psi A⁻¹ + primeCollapseCorrection p := by
  rw [nonprincipal_gauss_collapse hpsi hA]
  unfold primeCollapseMainCoeff primeCollapseCorrection
  ring

/-- The normalised statement, exhibited as `main term + exact correction`: the
correction is *not* absorbed into the main term. -/
theorem normalized_collapse_correction_isolated {p : ℕ} [Fact p.Prime]
    {psi : AddChar (ZMod p) ℂ} (hpsi : psi ≠ 1) {A : ZMod p} (hA : IsUnit A) :
    (1 / (Real.sqrt p : ℂ)) *
        (∑ chi ∈ ({1}ᶜ : Finset (DirichletCharacter ℂ p)), gaussSum chi psi * chi A)
      - primeCollapseMainCoeff p * psi A⁻¹ = primeCollapseCorrection p := by
  rw [nonprincipal_gauss_collapse_normalized hpsi hA]; ring

end Gate1B.SafeAlgebra
