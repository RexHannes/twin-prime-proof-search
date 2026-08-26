import Mathlib
set_option maxHeartbeats 800000

namespace TwinPrimeProject.NANC.D4

/-- A finite character family together with its exact orthogonality laws.
Both laws are data so the abstraction can represent Dirichlet characters or
any finite dual group without committing to a library representation. -/
structure OrthogonalCharacterFamily (G Χ : Type*) [Fintype G] [Fintype Χ]
    [DecidableEq G] [DecidableEq Χ] where
  eval : Χ → G → ℂ
  orthogonality : ∀ x y,
    (∑ χ : Χ, eval χ x * starRingEnd ℂ (eval χ y)) =
      if x = y then (Fintype.card Χ : ℂ) else 0
  injectiveSecondMoment : ∀ {I : Type*} [Fintype I] (f : I → G),
    Function.Injective f → ∀ w : I → ℂ,
      ∑ χ : Χ, Complex.normSq (∑ i : I, w i * eval χ (f i)) =
        (Fintype.card Χ : ℂ) * ∑ i : I, Complex.normSq (w i)


structure ReciprocalCharacterFormulaData (G Χ : Type*) [Fintype Χ] [DecidableEq Χ] where
  phase : G → G → ℂ
  gauss : Χ → ℂ
  eval : Χ → G → ℂ
  formula : ∀ A n,
    phase A n = (Fintype.card Χ : ℂ)⁻¹ *
      ∑ χ : Χ, gauss χ * starRingEnd ℂ (eval χ A) * eval χ n

theorem char_recip_formula
    {G Χ : Type*} [Fintype Χ] [DecidableEq Χ]
    (D : ReciprocalCharacterFormulaData G Χ) (A n : G) :
    D.phase A n = (Fintype.card Χ : ℂ)⁻¹ *
      ∑ χ : Χ, D.gauss χ * starRingEnd ℂ (D.eval χ A) * D.eval χ n := D.formula A n

end TwinPrimeProject.NANC.D4
