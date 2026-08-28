import Mathlib

/-!
# V11 · Gate 1B — pair-modulus capacity arithmetic

**Classification: CAPACITY_ONLY.**  Rational/exponent arithmetic only.  Nothing
in this file is an analytic theorem, and nothing here proves that either saving
is achievable.

Banked figures:

* shifted fixed-multiplier saving `1/32`;
* QK lower-endpoint worst fixed-multiplier saving `1/108`;
* common worst margin `min(1/32, 1/108) = 1/108`.

Proved: a multiplier-family tax exponent below `1/108` leaves a positive
fixed-power margin, and the `Y^{1/2} = X^{1/18}` family tax exceeds `1/108`,
hence kills the worst QK margin.
-/

namespace TwinPrimeProject
namespace Gate1BV11

/-- The shifted fixed-multiplier saving exponent. -/
def shiftedFixedMultiplierSaving : ℚ := 1 / 32

/-- The QK lower-endpoint worst fixed-multiplier saving exponent. -/
def qkLowerEndpointSaving : ℚ := 1 / 108

/-- The common worst margin. -/
def worstMargin : ℚ := min shiftedFixedMultiplierSaving qkLowerEndpointSaving

/-- `min(1/32, 1/108) = 1/108`. -/
theorem worstMargin_eq : worstMargin = 1 / 108 := by
  unfold worstMargin shiftedFixedMultiplierSaving qkLowerEndpointSaving
  norm_num

/-- The QK endpoint is the binding constraint. -/
theorem qk_is_the_binding_constraint : qkLowerEndpointSaving < shiftedFixedMultiplierSaving := by
  unfold qkLowerEndpointSaving shiftedFixedMultiplierSaving
  norm_num

/-- **A family tax below `1/108` leaves a positive fixed-power margin.** -/
theorem tax_below_worst_leaves_margin (tax : ℚ) (h : tax < 1 / 108) : 0 < worstMargin - tax := by
  rw [worstMargin_eq]
  linarith

/-- …and the margin is still positive against the shifted endpoint. -/
theorem tax_below_worst_leaves_shifted_margin (tax : ℚ) (h : tax < 1 / 108) :
    0 < shiftedFixedMultiplierSaving - tax := by
  unfold shiftedFixedMultiplierSaving
  linarith

/-- **`1/18 > 1/108`.** -/
theorem oneEighteenth_gt_oneOneOhEight : (1 : ℚ) / 18 > 1 / 108 := by norm_num

/-- **A `Y^{1/2} = X^{1/18}` family tax kills the worst QK margin.** -/
theorem sqrtY_familyTax_kills_qk_margin : worstMargin - 1 / 18 < 0 := by
  rw [worstMargin_eq]; norm_num

/-- The same statement in the form "no positive margin survives". -/
theorem sqrtY_familyTax_no_margin : ¬ (0 < worstMargin - 1 / 18) := by
  have := sqrtY_familyTax_kills_qk_margin
  linarith

/-- The exact deficit created by the `X^{1/18}` tax at the QK endpoint. -/
theorem sqrtY_familyTax_deficit : worstMargin - 1 / 18 = -(5 : ℚ) / 108 := by
  rw [worstMargin_eq]; norm_num

/-- Feasibility window: the set of admissible family taxes is exactly the open
interval below `1/108`, and it is nonempty. -/
theorem admissible_tax_window_nonempty : ∃ tax : ℚ, 0 < tax ∧ 0 < worstMargin - tax :=
  ⟨1 / 216, by norm_num, by rw [worstMargin_eq]; norm_num⟩

end Gate1BV11
end TwinPrimeProject
