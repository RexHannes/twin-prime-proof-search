import Mathlib

namespace NANC

/-- Equal-modulus ROW resonance.  The assumptions say exactly that `2,r,p₁,p₂`
are invertible modulo `q` (in particular they hold for an odd prime modulus and
nonzero residue classes). -/
theorem row_equal_q_resonance (q : ℕ) [Fact q.Prime] (r p₁ p₂ h₁ h₂ : ZMod q)
    (h2 : IsUnit (2 : ZMod q)) (hr : IsUnit r)
    (hp₁ : IsUnit p₁) (hp₂ : IsUnit p₂) :
    -2 * h₁ * (r * p₁)⁻¹ + 2 * h₂ * (r * p₂)⁻¹ = 0 ↔
      h₁ * p₂ = h₂ * p₁ := by
  have hr0 := hr.ne_zero
  have hp10 := hp₁.ne_zero
  have hp20 := hp₂.ne_zero
  have h20 := h2.ne_zero
  field_simp
  constructor
  · intro h
    have hz : -(h₁ * p₂) + p₁ * h₂ = 0 := by
      apply (mul_left_cancel₀ h20)
      simpa using h
    linear_combination -hz
  · intro h
    linear_combination 2 * (-h)

private theorem int_dvd_of_cast_mul_unit_eq_zero (q : ℕ) (h : ℤ) (u : ZMod q)
    (hu : IsUnit u) (hz : (h : ZMod q) * u = 0) : (q : ℤ) ∣ h := by
  obtain ⟨v, hv⟩ := isUnit_iff_exists_inv.mp hu
  have hc : (h : ZMod q) = 0 := by
    calc
      (h : ZMod q) = (h : ZMod q) * (u * v) := by rw [hv, mul_one]
      _ = ((h : ZMod q) * u) * v := by rw [mul_assoc]
      _ = 0 := by rw [hz, zero_mul]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd h q).mp hc

/-- For independent local moduli, vanishing of each local phase forces the
corresponding frequency to be divisible by its modulus. -/
theorem row_unequal_q_full_resonance (q₁ q₂ : ℕ) (h₁ h₂ : ℤ)
    (u₁ : ZMod q₁) (u₂ : ZMod q₂) (hu₁ : IsUnit u₁) (hu₂ : IsUnit u₂)
    (hz₁ : (h₁ : ZMod q₁) * u₁ = 0)
    (hz₂ : (h₂ : ZMod q₂) * u₂ = 0) :
    (q₁ : ℤ) ∣ h₁ ∧ (q₂ : ℤ) ∣ h₂ :=
  ⟨int_dvd_of_cast_mul_unit_eq_zero q₁ h₁ u₁ hu₁ hz₁,
   int_dvd_of_cast_mul_unit_eq_zero q₂ h₂ u₂ hu₂ hz₂⟩

end NANC
