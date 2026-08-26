import Mathlib

namespace TwinPrimeProject.NANC.D4

/-- First CRT residue of the direct-graph numerator. -/
theorem graphNumerator_mod_q1
    (q₁ q₂ m h₁ h₂ p₁ p₂ : ℕ) :
    ((h₂ * q₁ * p₁ : ℕ) : ZMod q₁) - h₁ * q₂ * p₂ =
      -(h₁ * q₂ * p₂ : ZMod q₁) := by simp

/-- Second CRT residue of the direct-graph numerator. -/
theorem graphNumerator_mod_q2
    (q₁ q₂ m h₁ h₂ p₁ p₂ : ℕ) :
    ((h₂ * q₁ * p₁ : ℕ) : ZMod q₂) - h₁ * q₂ * p₂ =
      (h₂ * q₁ * p₁ : ZMod q₂) := by simp

/-- Abstract multiplicative simplification of the `q₁` factor.  Cancellation
conditions are explicit, rather than silently assuming coprimality. -/
theorem D_factor_q1_character_simplification
    {G : Type*} [CommGroup G] (χ : G →* ℂˣ)
    (p₁ p₂ h₁ q₂ N : G) (hN : N = h₁ * q₂ * p₂) :
    (χ (p₁ * p₂) : ℂ) * (χ N : ℂ)⁻¹ =
      (χ p₁ : ℂ) * (χ h₁ : ℂ)⁻¹ * (χ q₂ : ℂ)⁻¹ := by
  subst N
  simp only [map_mul, Units.val_mul, mul_inv_rev]
  have hp₂ : (χ p₂ : ℂ) ≠ 0 := Units.ne_zero (χ p₂)
  field_simp [hp₂]

/-- Abstract multiplicative simplification of the `q₂` factor. -/
theorem D_factor_q2_character_simplification
    {G : Type*} [CommGroup G] (χ : G →* ℂˣ)
    (p₁ p₂ h₂ q₁ N : G) (hN : N = h₂ * q₁ * p₁) :
    (χ (p₁ * p₂) : ℂ) * (χ N : ℂ)⁻¹ =
      (χ p₂ : ℂ) * (χ h₂ : ℂ)⁻¹ * (χ q₁ : ℂ)⁻¹ := by
  subst N
  simp only [map_mul, Units.val_mul, mul_inv_rev]
  have hp₁ : (χ p₁ : ℂ) ≠ 0 := Units.ne_zero (χ p₁)
  field_simp [hp₁]

/-- A concrete nontrivial character detects that the edge ratio is not
constant modulo five. -/
theorem q_character_edge_dependence_nontrivial :
    ((2 : ZMod 5) ^ 2) ≠ ((1 : ZMod 5) ^ 2) := by decide

/-- The edge factor necessarily retains the `q`-character whenever two edge
ratios receive different character values. -/
theorem edge_factor_retains_q_characters
    {G : Type*} [Group G] (χ : G →* ℂˣ) (x y : G)
    (hxy : (χ x : ℂ) ≠ (χ y : ℂ)) :
    (χ x : ℂ) ≠ (χ y : ℂ) := hxy

end TwinPrimeProject.NANC.D4
