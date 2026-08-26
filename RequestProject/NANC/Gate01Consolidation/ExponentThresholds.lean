import RequestProject.NANC.Gate01Consolidation.R9Regrouping

/-!
# BANK R / S — completion-threshold and pointwise-deficit exponent arithmetic

Exact rational arithmetic only.  Every statement below is a comparison of
`ℚ`-exponents of `X`; no analytic estimate, and in particular no claim that the
actual error term is of size `√Q`, is made anywhere.

At the switched endpoint `Q = X^{13/18}`, so `√Q = X^{13/36}`.

* **BANK R.**  `2/9 < 13/36` with deficit `13/36 − 2/9 = 5/36`; and for the
  `4|5` split `4/9 − 13/36 = 1/12`, `5/9 − 13/36 = 7/36`: both regrouped
  variables lie strictly above the square-root modulus scale.
* **BANK S.**  With `UV = X` and `Q = X^{13/18}` the progression count scale is
  `X^{5/18}` and **WEIL-DEF** `13/36 − 5/18 = 1/12`.
-/

namespace TwinPrimeProject
namespace Gate01Consolidation

/-- The switched endpoint modulus exponent `Q = X^{13/18}`. -/
def expQ : ℚ := 13 / 18

/-- The square-root modulus exponent `√Q = X^{13/36}`. -/
def expSqrtQ : ℚ := 13 / 36

theorem expSqrtQ_eq_half_expQ : expSqrtQ = expQ / 2 := by
  unfold expSqrtQ expQ; norm_num

/-- **twoSeven_short_below_sqrtQ.**  The `2|7` short variable `X^{2/9}` lies
strictly below the square-root modulus scale. -/
theorem twoSeven_short_below_sqrtQ : expTwoSeven < expSqrtQ := by
  unfold expTwoSeven expSqrtQ; norm_num

/-- The exact deficit of the `2|7` short variable. -/
theorem twoSeven_short_deficit : expSqrtQ - expTwoSeven = 5 / 36 := by
  unfold expSqrtQ expTwoSeven; norm_num

/-- **fourFive_left_above_sqrtQ.**  `4/9 − 13/36 = 1/12 > 0`. -/
theorem fourFive_left_above_sqrtQ : expU - expSqrtQ = 1 / 12 := by
  unfold expU expSqrtQ; norm_num

/-- **fourFive_right_above_sqrtQ.**  `5/9 − 13/36 = 7/36 > 0`. -/
theorem fourFive_right_above_sqrtQ : expV - expSqrtQ = 7 / 36 := by
  unfold expV expSqrtQ; norm_num

/-- **fourFive_crosses_completion_threshold.**  Both regrouped variables lie
strictly above the square-root modulus scale. -/
theorem fourFive_crosses_completion_threshold :
    expSqrtQ < expU ∧ expSqrtQ < expV := by
  unfold expSqrtQ expU expV
  constructor <;> norm_num

/-- The natural progression-count scale `UV/Q = X^{5/18}`. -/
def expUVoverQ : ℚ := 5 / 18

theorem expUVoverQ_eq : expUVoverQ = (expU + expV) - expQ := by
  unfold expUVoverQ expU expV expQ; norm_num

/-- **WEIL-DEF.**  The pointwise square-root-modulus scale exceeds the
progression-count scale by exactly `X^{1/12}`.  *Ledger interpretation only*:
this compares exponents, it does not assert that the true error is `√Q`. -/
theorem weil_deficit : expSqrtQ - expUVoverQ = 1 / 12 := by
  unfold expSqrtQ expUVoverQ; norm_num

end Gate01Consolidation
end TwinPrimeProject
