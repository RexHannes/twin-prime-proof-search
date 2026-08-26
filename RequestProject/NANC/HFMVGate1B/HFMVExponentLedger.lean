import Mathlib

/-!
# HFMV Gate 1B, Module 4: the exact rational exponent ledger

The HFMV parameter choice is banked *symbolically*, as exact rational
exponents:

  `U = X^(4/9)`,  `V = X^(5/9)`,  `Q = D P = X^(13/18)`,

hence

  `U V / Q = X^(5/18)`  and  `Q² / V² = X^(1/3)`.

Two layers are provided:

* the rational identities between the exponents (`expU`, `expV`, `expQ` : ℚ);
* their `Real.rpow` corollaries for a fixed base `X > 0`, which are genuine
  equalities of real powers — no asymptotic notation is encoded as an exact
  equality.
-/

namespace TwinPrimeProject
namespace HFMVGate1B

/-! ## 1. Rational exponent ledger -/

/-- Exponent of the `u`-variable. -/
def expU : ℚ := 4 / 9

/-- Exponent of the `v`-variable. -/
def expV : ℚ := 5 / 9

/-- Exponent of the modulus `Q = D P`. -/
def expQ : ℚ := 13 / 18

theorem expU_value : expU = 4 / 9 := rfl
theorem expV_value : expV = 5 / 9 := rfl
theorem expQ_value : expQ = 13 / 18 := rfl

/-- `U V = X`. -/
theorem expU_add_expV : expU + expV = 1 := by norm_num [expU, expV]

/-- `U V / Q = X^(5/18)`. -/
theorem expUV_sub_expQ : expU + expV - expQ = 5 / 18 := by
  norm_num [expU, expV, expQ]

/-- `Q² / V² = X^(1/3)`. -/
theorem two_expQ_sub_two_expV : 2 * expQ - 2 * expV = 1 / 3 := by
  norm_num [expQ, expV]

/-- `Q` sits strictly between `U` and `V`-free trivial ranges: `1/2 < 13/18 < 1`. -/
theorem expQ_bounds : (1 : ℚ) / 2 < expQ ∧ expQ < 1 := by
  constructor <;> norm_num [expQ]

/-- `Q > V`, with the exact gap `13/18 − 5/9 = 1/6`. -/
theorem expQ_sub_expV : expQ - expV = 1 / 6 := by norm_num [expQ, expV]

/-- `Q > U`, with the exact gap `13/18 − 4/9 = 5/18`. -/
theorem expQ_sub_expU : expQ - expU = 5 / 18 := by norm_num [expQ, expU]

/-! ## 2. Real-power corollaries (exact, for a fixed base `X > 0`) -/

open Real

/-- `X^(4/9) * X^(5/9) = X`. -/
theorem rpow_U_mul_V {X : ℝ} (hX : 0 < X) :
    X ^ ((expU : ℝ)) * X ^ ((expV : ℝ)) = X ^ (1 : ℝ) := by
  rw [← Real.rpow_add hX]
  norm_num [expU, expV]

/-- `X^(4/9) * X^(5/9) / X^(13/18) = X^(5/18)`. -/
theorem rpow_UV_div_Q {X : ℝ} (hX : 0 < X) :
    X ^ ((expU : ℝ)) * X ^ ((expV : ℝ)) / X ^ ((expQ : ℝ)) = X ^ ((5 : ℝ) / 18) := by
  rw [← Real.rpow_add hX, ← Real.rpow_sub hX]
  norm_num [expU, expV, expQ]

/-- `(X^(13/18))² / (X^(5/9))² = X^(1/3)`. -/
theorem rpow_Qsq_div_Vsq {X : ℝ} (hX : 0 < X) :
    (X ^ ((expQ : ℝ))) ^ (2 : ℝ) / (X ^ ((expV : ℝ))) ^ (2 : ℝ) = X ^ ((1 : ℝ) / 3) := by
  rw [← Real.rpow_mul hX.le, ← Real.rpow_mul hX.le, ← Real.rpow_sub hX]
  norm_num [expQ, expV]

/-! ## 3. Guard: the ledger carries no analytic content -/

/-- **Guard.**  The exponent ledger is pure arithmetic: from the identities of
this module no statement about the HFMV sums follows.  Formally, the ledger
identities hold for every base, and in particular they are equally true at
`X = 1`, where every power equals `1`. -/
theorem ledger_has_no_analytic_content :
    (1 : ℝ) ^ ((expU : ℝ)) * (1 : ℝ) ^ ((expV : ℝ)) / (1 : ℝ) ^ ((expQ : ℝ))
      = (1 : ℝ) ^ ((5 : ℝ) / 18) := by
  simp

end HFMVGate1B
end TwinPrimeProject
