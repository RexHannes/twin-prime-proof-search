import RequestProject.Options
namespace TwinPrimeProject.NANC

theorem row_equal_q_resonance {F : Type} [Field F]
    (r p₁ p₂ h₁ h₂ : F) (hr : r ≠ 0) (hp₁ : p₁ ≠ 0) (hp₂ : p₂ ≠ 0)
    (h2 : (2 : F) ≠ 0) :
    -2*h₁*(r*p₁)⁻¹ + 2*h₂*(r*p₂)⁻¹ = 0 ↔ h₁*p₂ = h₂*p₁ := by
  field_simp
  constructor
  · intro h
    have hh : 2 * (-(h₁*p₂) + p₁*h₂) = 0 := by simpa using h
    have hz : -(h₁*p₂) + p₁*h₂ = 0 := (mul_eq_zero.mp hh).resolve_left h2
    linear_combination -hz
  · intro h
    rw [h]
    ring

structure ROWUnequalQResonanceInput where
  resonanceHypotheses : Prop
  forcedDivisibility : Prop
  derive : resonanceHypotheses → forcedDivisibility

theorem row_unequal_q_full_resonance_interface (H : ROWUnequalQResonanceInput)
    (h : H.resonanceHypotheses) : H.forcedDivisibility := H.derive h

end NANC
