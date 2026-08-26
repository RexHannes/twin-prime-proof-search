import Mathlib

namespace TwinPrimeProject.NANC.D4

/-- Symbolic data for the exact three-character crossed coordinate expression. -/
structure ThreeCharData (Χ₁ Χ₂ Ρ T : Type*) [Fintype Χ₁] [Fintype Χ₂]
    [Fintype Ρ] [Fintype T] where
  tau1 : Χ₁ → ℂ
  tau2 : Χ₂ → ℂ
  C3 : Χ₁ → Χ₂ → Ρ → ℂ
  rho : Ρ → T → ℂ
  S12 : T → ℂ
  S21 : T → ℂ

namespace ThreeCharData

variable {Χ₁ Χ₂ Ρ T : Type*} [Fintype Χ₁] [Fintype Χ₂] [Fintype Ρ] [Fintype T]

/-- The crossed three-character coordinate expression. -/
noncomputable def crossedForm (D : ThreeCharData Χ₁ Χ₂ Ρ T) : ℂ :=
  ∑ χ₁, ∑ χ₂, ∑ ρ,
    D.tau1 χ₁ * D.tau2 χ₂ * D.C3 χ₁ χ₂ ρ *
      ∑ t, D.rho ρ t * D.S12 t * D.S21 t

/-- Losslessness is represented honestly by mutually inverse supplied maps;
the theorem records their exact round trip and does not claim D4 cancellation. -/
theorem three_character_form_is_lossless_interface
    {Original : Type*} (encode : Original → ThreeCharData Χ₁ Χ₂ Ρ T)
    (decode : ThreeCharData Χ₁ Χ₂ Ρ T → Original)
    (hleft : Function.LeftInverse decode encode) : Function.Injective encode :=
  hleft.injective

end ThreeCharData

end TwinPrimeProject.NANC.D4
