import RequestProject.Options
namespace TwinPrimeProject.NANC

/-- Correct three-factor CRT reconstruction.  The factors multiplying `xᵢ` are
exactly the complementary cofactors; omitting them is the retired false formula. -/
theorem t0_crt_cofactor_split
    (p₁ p₂ p₃ q x₁ x₂ x₃ : ℤ)
    (h₁ : q*(p₂*p₃)*x₁ ≡ 1 [ZMOD p₁])
    (h₂ : q*(p₁*p₃)*x₂ ≡ 1 [ZMOD p₂])
    (h₃ : q*(p₁*p₂)*x₃ ≡ 1 [ZMOD p₃])
    (hcop12 : IsCoprime p₁ p₂) (hcop13 : IsCoprime p₁ p₃)
    (hcop23 : IsCoprime p₂ p₃) :
    q*((p₂*p₃)*x₁ + (p₁*p₃)*x₂ + (p₁*p₂)*x₃) ≡ 1
      [ZMOD p₁*p₂*p₃] := by
  rw [Int.modEq_iff_dvd] at h₁ h₂ h₃ ⊢
  have hp₁ : p₁ ∣ 1 - q*((p₂*p₃)*x₁ + (p₁*p₃)*x₂ + (p₁*p₂)*x₃) := by
    obtain ⟨z, hz⟩ := h₁
    use z - q*(p₃*x₂ + p₂*x₃)
    linear_combination hz
  have hp₂ : p₂ ∣ 1 - q*((p₂*p₃)*x₁ + (p₁*p₃)*x₂ + (p₁*p₂)*x₃) := by
    obtain ⟨z, hz⟩ := h₂
    use z - q*(p₃*x₁ + p₁*x₃)
    linear_combination hz
  have hp₃ : p₃ ∣ 1 - q*((p₂*p₃)*x₁ + (p₁*p₃)*x₂ + (p₁*p₂)*x₃) := by
    obtain ⟨z, hz⟩ := h₃
    use z - q*(p₂*x₁ + p₁*x₂)
    linear_combination hz
  exact (hcop13.mul_left hcop23).mul_dvd (hcop12.mul_dvd hp₁ hp₂) hp₃
end TwinPrimeProject.NANC
