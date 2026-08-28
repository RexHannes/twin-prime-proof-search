import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Phase A7 · endpoint `u`-diagonal exponent bank

**CAPACITY_ONLY.**  This module banks the *rational exponent arithmetic* of the
endpoint diagonal and nothing else.  No large-sieve, BDH or variance input is
encoded as proved; the analytic input is exposed as an explicit hypothesis of
the conditional compiler in `Gate1BEndpointCompiler.lean`.

Current endpoint powers in `Y`:

  `U = Y^4`, `V = Y^5`, `R = Y^(5/2)`, `H = Y^(5/2)`, `X = Y^9`.

The diagonal physical scale is `V * sqrt (R * U)`, of `Y`-exponent

  `5 + (5/2 + 4)/2 = 33/4`,

while `X = Y^(36/4)`.  The margin is `3/4` in `Y`, i.e. `X^(-1/12)`.
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace EndpointExponents

/-! ## 1. Exact rational arithmetic -/

/-- `Y`-exponent of `U`. -/
def eU : ℚ := 4
/-- `Y`-exponent of `V`. -/
def eV : ℚ := 5
/-- `Y`-exponent of `R`. -/
def eR : ℚ := 5 / 2
/-- `Y`-exponent of `H`. -/
def eH : ℚ := 5 / 2
/-- `Y`-exponent of `X`. -/
def eX : ℚ := 9

/-- `Y`-exponent of the diagonal physical scale `V * sqrt (R U)`. -/
def eDiag : ℚ := eV + (eR + eU) / 2

/-- **A7.**  The diagonal `Y`-exponent is exactly `33/4`. -/
theorem eDiag_value : eDiag = 33 / 4 := by
  norm_num [eDiag, eV, eR, eU]

/-- `X` has `Y`-exponent `36/4`. -/
theorem eX_quarters : eX = 36 / 4 := by norm_num [eX]

/-- **A7.**  The `Y`-margin is exactly `3/4`. -/
theorem eMargin_Y : eX - eDiag = 3 / 4 := by
  norm_num [eX, eDiag, eV, eR, eU]

/-- **A7.**  Converted to the `X`-scale (`Y = X^(1/9)`), the margin exponent is
exactly `1/12`. -/
theorem eMargin_X : (eX - eDiag) / eX = 1 / 12 := by
  norm_num [eX, eDiag, eV, eR, eU]

/-- The diagonal scale relative to `X`, in the `X`-exponent: `-1/12`. -/
theorem eDiag_relative_X : eDiag / eX - 1 = -(1 / 12) := by
  norm_num [eX, eDiag, eV, eR, eU]

/-! ## 2. `rpow` translation for a positive base -/

section Rpow
variable {Y : ℝ}

/-- **A7, real form.**  For `Y > 0`, with `U = Y^4`, `V = Y^5`, `R = Y^(5/2)`,
the diagonal physical scale `V * sqrt (R * U)` equals `Y ^ (33/4)`. -/
theorem diag_scale_rpow (hY : 0 < Y) :
    (Y ^ (5 : ℝ)) * Real.sqrt ((Y ^ ((5 : ℝ) / 2)) * (Y ^ (4 : ℝ)))
      = Y ^ ((33 : ℝ) / 4) := by
  have h1 : (Y ^ ((5 : ℝ) / 2)) * (Y ^ (4 : ℝ)) = Y ^ ((13 : ℝ) / 2) := by
    rw [← Real.rpow_add hY]; norm_num
  rw [h1, Real.sqrt_eq_rpow, ← Real.rpow_mul hY.le, ← Real.rpow_add hY]
  norm_num

/-- **A7, real form.**  With `X = Y^9` and `Y > 0`, the diagonal scale is
`X * X ^ (-(1/12))`. -/
theorem diag_scale_relative_X (hY : 0 < Y) :
    (Y ^ (5 : ℝ)) * Real.sqrt ((Y ^ ((5 : ℝ) / 2)) * (Y ^ (4 : ℝ)))
      = (Y ^ (9 : ℝ)) * (Y ^ (9 : ℝ)) ^ (-((1 : ℝ) / 12)) := by
  rw [diag_scale_rpow hY, ← Real.rpow_mul hY.le, ← Real.rpow_add hY]
  norm_num

/-- The margin is a genuine power saving: `X ^ (-(1/12)) < 1` for `X > 1`. -/
theorem margin_lt_one {X : ℝ} (hX : 1 < X) : X ^ (-((1 : ℝ) / 12)) < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg hX (by norm_num)

end Rpow

/-! ## 3. Firewall

The exponent bank is `CAPACITY_ONLY`: it says *where* the diagonal sits, not
that the diagonal is bounded.  The following theorem records that the exponent
arithmetic alone implies no bound on any analytic quantity — it is an identity
between numbers, with no analytic content. -/

/-- **Counterguard.**  The exponent identity `eMargin_X` holds regardless of
any analytic input, so it cannot by itself furnish a diagonal estimate:
there exist real data `D` violating the diagonal target while the exponent
arithmetic is unchanged. -/
theorem exponent_bank_is_not_an_estimate :
    ∃ D : ℝ, ¬ (D ≤ (2 : ℝ) ^ (-((1 : ℝ) / 12))) :=
  ⟨2, by
    have h : (2 : ℝ) ^ (-((1 : ℝ) / 12)) < 1 := margin_lt_one (by norm_num)
    intro hle; linarith⟩

end EndpointExponents
end CurrentProgramme
end TwinPrimeProject
