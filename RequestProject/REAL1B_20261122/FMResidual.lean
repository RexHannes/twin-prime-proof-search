import Mathlib

namespace REAL1B.FM

/-- Gold 4.53-FM §1: the stronger historical residual target. -/
theorem historical_margin (T S Pneg R E₁ E₂ : ℝ)
    (lower : (0.361755018 - (10 : ℝ)⁻¹ ^ 58) * S + Pneg - R - E₁ ≤ T)
    (residual : R - Pneg ≤ (0.359892818 - (10 : ℝ)⁻¹ ^ 58) * S + E₂) :
    0.0018622 * S - E₁ - E₂ ≤ T := by
  linarith only [lower, residual]

/-- Gold 4.53-FM target (T) omits the tiny subtraction on the residual side. -/
theorem current_margin (T S Pneg R E₁ E₂ : ℝ)
    (lower : (0.361755018 - (10 : ℝ)⁻¹ ^ 58) * S + Pneg - R - E₁ ≤ T)
    (residual : R - Pneg ≤ 0.359892818 * S + E₂) :
    (0.0018622 - (10 : ℝ)⁻¹ ^ 58) * S - E₁ - E₂ ≤ T := by
  linarith only [lower, residual]

end REAL1B.FM

#print axioms REAL1B.FM.historical_margin
#print axioms REAL1B.FM.current_margin
