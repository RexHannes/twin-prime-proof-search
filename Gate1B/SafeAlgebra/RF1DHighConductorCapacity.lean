/-
# Gate 1B v8.4 — RF1D high-conductor threshold capacity

**Status: CAPACITY_ONLY (rational exponent bookkeeping).**

All quantities are *exponents*, measured in the scale `Y` (so a quantity of
size `Y ^ t` is recorded by the rational number `t`).  Write

  `Q = Y ^ qe`,  `C = Y ^ ce`.

The two abstract capacity ratios supplied by the RF1D analysis are

  `ratio(C) = C / Q`            for `C ≤ Y ^ 4`,
  `ratio(C) = C ^ 2 / (Q Y ^ 4)` for `C ≥ Y ^ 4`,

whose exponents are `ce - qe` and `2 * ce - qe - 4` respectively.  Nothing here
asserts that these ratios *are* the RF1D bound: they are abstract capacity
formulas carried under supplied hypotheses.  **The analytic RF1D theorem is not
declared anywhere in this file.**
-/
import Mathlib

namespace Gate1B.SafeAlgebra

/-! ## The two capacity exponents -/

/-- Exponent of the low-branch capacity ratio `C / Q`. -/
def rf1dLowRatioExponent (qe ce : ℚ) : ℚ := ce - qe

/-- Exponent of the high-branch capacity ratio `C ^ 2 / (Q Y ^ 4)`. -/
def rf1dHighRatioExponent (qe ce : ℚ) : ℚ := 2 * ce - qe - 4

/-- The transition conductor `C₀ = Q ^ (1/2) Y ^ 2`, in exponent form. -/
def rf1dTransitionExponent (qe : ℚ) : ℚ := qe / 2 + 2

/-- **Transition point.**  At `C = C₀ = Q ^ (1/2) Y ^ 2` the high-branch ratio
`C ^ 2 / (Q Y ^ 4)` has exponent `0`, i.e. equals `1`. -/
theorem rf1d_transition_exponent (qe : ℚ) :
    rf1dHighRatioExponent qe (rf1dTransitionExponent qe) = 0 := by
  unfold rf1dHighRatioExponent rf1dTransitionExponent; ring

/-- **Margin below the transition.**  If `C ≤ C₀ Y ^ (-η)`, i.e.
`ce ≤ rf1dTransitionExponent qe - η`, then the high-branch ratio exponent is at
most `-2 η`, i.e. the ratio is at most `Y ^ (-2 η)`. -/
theorem rf1d_belowTransition_margin (qe ce eta : ℚ)
    (hce : ce ≤ rf1dTransitionExponent qe - eta) :
    rf1dHighRatioExponent qe ce ≤ -2 * eta := by
  unfold rf1dHighRatioExponent rf1dTransitionExponent at *
  linarith

/-- Strict version: strictly below the transition gives a strictly negative
exponent, for `η > 0`. -/
theorem rf1d_belowTransition_neg (qe ce eta : ℚ) (heta : 0 < eta)
    (hce : ce ≤ rf1dTransitionExponent qe - eta) :
    rf1dHighRatioExponent qe ce < 0 := by
  have := rf1d_belowTransition_margin qe ce eta hce
  linarith

/-- Above the transition the high-branch ratio exponent is nonnegative: the
capacity formula gives no saving there. -/
theorem rf1d_aboveTransition_nonneg (qe ce : ℚ)
    (hce : rf1dTransitionExponent qe ≤ ce) :
    0 ≤ rf1dHighRatioExponent qe ce := by
  unfold rf1dHighRatioExponent rf1dTransitionExponent at *
  linarith

/-- The two branches agree at the branch point `C = Y ^ 4` (`ce = 4`). -/
theorem rf1d_branches_agree_at_four (qe : ℚ) :
    rf1dLowRatioExponent qe 4 = rf1dHighRatioExponent qe 4 := by
  unfold rf1dLowRatioExponent rf1dHighRatioExponent; ring

/-- Instantiated capacity statement: a supplied bound of the abstract shape
`ratio ≤ Y ^ (rf1dHighRatioExponent qe ce)` transfers to `Y ^ (-2 η)` below the
transition, for `Y ≥ 1`.  This is a monotonicity statement about the *formula*,
not an RF1D estimate. -/
theorem rf1d_capacity_transfer {Y ratio : ℝ} (qe ce eta : ℚ) (hY : 1 ≤ Y)
    (hce : ce ≤ rf1dTransitionExponent qe - eta)
    (hratio : ratio ≤ Y ^ ((rf1dHighRatioExponent qe ce : ℚ) : ℝ)) :
    ratio ≤ Y ^ ((-2 * eta : ℚ) : ℝ) := by
  refine hratio.trans (Real.rpow_le_rpow_of_exponent_le hY ?_)
  exact_mod_cast rf1d_belowTransition_margin qe ce eta hce

end Gate1B.SafeAlgebra
