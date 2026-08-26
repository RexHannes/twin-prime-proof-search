/-
# Gate 1B safe algebra — the AK physical exponent ledger (exact ℚ arithmetic)

Every statement here is an identity or inequality between explicit rational
numbers.  **These are exponent certificates only.**  In particular this file
does *not* assert

    E_AK ≤ X^(223/144 + o(1))

or any other analytic estimate; the exponents are bookkeeping for an externally
supplied analytic input (see `Gate1B/SafeExtensions/AKGMInterfaces.lean`).
-/
import Mathlib

namespace Gate1B.SafeAlgebra

/-- The physical `U`-exponent. -/
def akUExponent : ℚ := 4 / 9

/-- The physical `V`-exponent. -/
def akVExponent : ℚ := 5 / 9

/-- `U V = X` at the level of exponents. -/
theorem ak_UV_exponent_sum : akUExponent + akVExponent = 1 := by
  unfold akUExponent akVExponent; norm_num

/-- **Large-cell spectral tax.**  If `lam ≥ 5/9` and `0 ≤ theta ≤ 7/64`, then
`theta (1 − lam) ≤ 7/144`. -/
theorem ak_largeCell_spectralTax_le {lam theta : ℚ} (hlam : 5 / 9 ≤ lam)
    (hθ0 : 0 ≤ theta) (hθ : theta ≤ 7 / 64) : theta * (1 - lam) ≤ 7 / 144 := by
  nlinarith [hlam, hθ0, hθ]

/-- **Energy output exponent.**  `1/2 + 4/9 + 5/9 + 7/144 = 223/144`. -/
theorem ak_energyOutputExponent :
    (1 / 2 : ℚ) + akUExponent + akVExponent + 7 / 144 = 223 / 144 := by
  unfold akUExponent akVExponent; norm_num

/-- **Physical target exponent.**  `2 − 4/9 = 224/144`. -/
theorem ak_physicalTargetExponent : (2 : ℚ) - akUExponent = 224 / 144 := by
  unfold akUExponent; norm_num

/-- **Exact energy margin.**  `224/144 − 223/144 = 1/144`. -/
theorem ak_energyMargin_exact : (224 / 144 : ℚ) - 223 / 144 = 1 / 144 := by norm_num

/-- **Exact amplitude margin.**  Half the energy margin is `1/288`. -/
theorem ak_amplitudeMargin_exact : ((1 / 144 : ℚ)) / 2 = 1 / 288 := by norm_num

/-- The ledger assembled: target exponent minus output exponent is exactly
`1/144`, and its half is exactly `1/288`. -/
theorem ak_exponentLedger :
    ((2 : ℚ) - akUExponent) - ((1 / 2 : ℚ) + akUExponent + akVExponent + 7 / 144) = 1 / 144 ∧
      (((2 : ℚ) - akUExponent) -
        ((1 / 2 : ℚ) + akUExponent + akVExponent + 7 / 144)) / 2 = 1 / 288 := by
  unfold akUExponent akVExponent
  constructor <;> norm_num

end Gate1B.SafeAlgebra
