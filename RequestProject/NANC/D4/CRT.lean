import Mathlib

namespace TwinPrimeProject.NANC.D4

/-- Multiplying a numerator by the complementary modulus reduces to the
original numerator in the indicated component. -/
theorem crt_complementary_modulus_left
    (q₁ q₂ A : ℕ) :
    ((q₂ * A : ℕ) : ZMod q₁) = (q₂ : ZMod q₁) * A := by
  norm_cast

/-- A complementary-modulus term vanishes in the other CRT component. -/
theorem crt_complementary_modulus_vanishes
    (q₁ q₂ A : ℕ) : ((q₂ * A : ℕ) : ZMod q₂) = 0 := by
  simp

/-- Pure algebra behind the direct-graph numerator split.  The inverse
identities needed in an application are explicit hypotheses. -/
theorem direct_graph_phase_CRT
    {R : Type*} [CommRing R]
    (two k h₁ h₂ q₁ q₂ p₁ p₂ u v u₁ u₂ : R)
    (hu₁ : p₂ * u * v = u₁)
    (hu₂ : p₁ * u * v = u₂) :
    two * k * (h₂ * q₁ * p₁ - h₁ * q₂ * p₂) * u * v =
      -two * h₁ * k * q₂ * u₁ + two * h₂ * k * q₁ * u₂ := by
  rw [← hu₁, ← hu₂]
  ring

end TwinPrimeProject.NANC.D4
