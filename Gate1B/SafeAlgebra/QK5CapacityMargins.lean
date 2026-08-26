/-
# Gate 1B v8.2 — QK5 capacity margins (exact rational exponents)

Every statement in this file is **exponent arithmetic in ℚ**.  Nothing here is
an analytic estimate: the exponents of the sources (`Q`, `C`, `J`, `D`, …) are
inputs, and the theorems only check that the recorded budgets are internally
consistent.  Each theorem name contains `Capacity` or `Exponent` to make this
scope explicit.

Recorded margins:

* PV medium range: `Q ≥ Y^{13/2}` and `C ≤ Y⁷/Q` give `C²Y⁵/Q ≤ Y^{-1/2}`;
* with `Y = X^{1/9}`, `Y^{-1/2} = X^{-1/18}`;
* overlap point `J = Y^{1/2}`, threshold `C_* = Y^{2/3}`, with both the PV and
  the large-sieve exponents equal to `−1/6`, i.e. `X^{-1/54}`;
* the axis budget is `X^{-1/9}`;
* the source-mass identity `(D/Y)·(Q²/D) = Q²/Y`.
-/
import Mathlib

namespace Gate1B.SafeAlgebra

/-- **PV medium-range capacity margin in `Y`.**  With `q = log_Y Q ≥ 13/2` and
`c = log_Y C ≤ 7 − q`, the exponent of `C²Y⁵/Q` is at most `−1/2`. -/
theorem pvMedium_marginY_Exponent {q c : ℚ} (hq : (13 : ℚ) / 2 ≤ q) (hc : c ≤ 7 - q) :
    2 * c + 5 - q ≤ -(1 / 2) := by linarith

/-- **Conversion of the PV margin to `X`.**  With `Y = X^{1/9}`, the margin
`Y^{-1/2}` is `X^{-1/18}`. -/
theorem pvMedium_marginX_Exponent : (-(1 : ℚ) / 2) * (1 / 9) = -(1 / 18) := by norm_num

/-- The overlap point of the two QK5 ranges is `J = Y^{1/2}`. -/
def overlapPointExponent : ℚ := 1 / 2

/-- The overlap threshold is `C_* = Y^{2/3}`. -/
def overlapThresholdExponent : ℚ := 2 / 3

/-- The PV exponent at the overlap point. -/
def pvOverlapExponent : ℚ := -(1 / 6)

/-- The large-sieve exponent at the overlap point. -/
def largeSieveOverlapExponent : ℚ := -(1 / 6)

/-- **The two overlap exponents agree.** -/
theorem overlapExponents_agree : pvOverlapExponent = largeSieveOverlapExponent := rfl

/-- **The overlap margin in `X`** is `X^{-1/54}`. -/
theorem overlapMargin_X_Exponent : pvOverlapExponent * (1 / 9) = -(1 / 54) := by
  norm_num [pvOverlapExponent]

/-- The axis budget exponent is `X^{-1/9}`. -/
def axisBudgetExponent : ℚ := -(1 / 9)

/-- **The axis budget is negative**, i.e. it is a genuine saving. -/
theorem axisBudget_negative_Exponent : axisBudgetExponent < 0 := by
  norm_num [axisBudgetExponent]

/-- **Source-mass capacity identity** `(D/Y)·(Q²/D) = Q²/Y`, in exponents. -/
theorem sourceMass_capacity_Exponent (d y qexp : ℚ) :
    (d - y) + (2 * qexp - d) = 2 * qexp - y := by ring

/-- **Real form of the PV medium margin.**  For `Y ≥ 1` the exponent inequality
transfers to the corresponding power comparison. -/
theorem pvMedium_marginY_Capacity {Y : ℝ} (hY : 1 ≤ Y) {q c : ℚ}
    (hq : (13 : ℚ) / 2 ≤ q) (hc : c ≤ 7 - q) :
    Y ^ ((2 * c + 5 - q : ℚ) : ℝ) ≤ Y ^ ((-(1 / 2) : ℚ) : ℝ) :=
  Real.rpow_le_rpow_of_exponent_le hY (by exact_mod_cast pvMedium_marginY_Exponent hq hc)

end Gate1B.SafeAlgebra
