/-
# UniversalV8 Module G — budgeted synthesis principle

Purely order-theoretic / algebraic.  Its importance is architectural: the admissible
congestion budget `B` may GROW; nothing here encodes `C = o(1)`, and nothing here
asserts that an actual arithmetic congestion `C` satisfies any particular bound.
-/
import Mathlib

namespace UniversalV8

/-- **Budgeted synthesis.**  `E ≤ ρ C E_nat` and `C ≤ B` give `E ≤ ρ B E_nat`. -/
theorem budgetedSynthesis (E Enat rho C B : ℝ) (hrho : 0 ≤ rho) (hEnat : 0 ≤ Enat)
    (hE : E ≤ rho * C * Enat) (hCB : C ≤ B) : E ≤ rho * B * Enat := by
  have : rho * C * Enat ≤ rho * B * Enat := by
    have h1 : rho * C ≤ rho * B := mul_le_mul_of_nonneg_left hCB hrho
    exact mul_le_mul_of_nonneg_right h1 hEnat
  linarith

/-- **Budgeted synthesis closes the target.**  If moreover `ρ B E_nat ≤ T` then `E ≤ T`. -/
theorem budgetedSynthesis_closes (E Enat rho C B T : ℝ) (hrho : 0 ≤ rho) (hEnat : 0 ≤ Enat)
    (hE : E ≤ rho * C * Enat) (hCB : C ≤ B) (hT : rho * B * Enat ≤ T) : E ≤ T :=
  le_trans (budgetedSynthesis E Enat rho C B hrho hEnat hE hCB) hT

/-- Ratio form, when the natural energy is positive. -/
theorem budgetedSynthesis_ratio (E Enat rho C B : ℝ) (hrho : 0 ≤ rho) (hEnat : 0 < Enat)
    (hE : E ≤ rho * C * Enat) (hCB : C ≤ B) : E / Enat ≤ rho * B := by
  rw [div_le_iff₀ hEnat]
  exact budgetedSynthesis E Enat rho C B hrho hEnat.le hE hCB

end UniversalV8
