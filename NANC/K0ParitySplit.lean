import Mathlib

namespace NANC

theorem k0_even_parity_band (Aminus Aplus C : ℚ)
    (hadd : Aplus = Aminus + C) (hpar : Aminus = -Aplus) :
    Aminus = -(1 / 2 : ℚ) * C := by linarith

theorem k0_odd_parity_band_zero (Aminus Aplus C : ℚ)
    (hadd : Aplus = Aminus + C) (hpar : Aminus = Aplus) : C = 0 := by linarith

theorem k0_parity_split (Aminus Aplus C μ : ℚ)
    (hμ : μ = -1 ∨ μ = 1)
    (hadd : Aplus = Aminus + C) (hpar : Aminus = -μ * Aplus) :
    Aminus = (1 - μ) / 2 * Aminus - (1 + μ) / 4 * C := by
  rcases hμ with rfl | rfl
  · simp
  · have := k0_even_parity_band Aminus Aplus C hadd (by simpa using hpar)
    linarith

/-- Regression: the erroneous plus-sign formula fails at `μ=1, C=2`. -/
theorem k0_plus_sign_regression :
    let μ : ℚ := 1
    let C : ℚ := 2
    ¬ (-(1 / 2 : ℚ) * C = (1 + μ) / 4 * C) := by norm_num

end NANC
