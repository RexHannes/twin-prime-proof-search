import RequestProject.TwinPrimeDefinitions

namespace TwinPrimeProject

lemma intervalIndicator_nonnegative (x : ℝ) (n : ℕ) : 0 ≤ intervalIndicator x n := by
  unfold intervalIndicator
  split <;> positivity

/-- `aₓ(n)` is nonnegative when its normalization has positive logarithm. -/
theorem TwinPrimeWeightedDetector_nonnegative {x : ℝ} (hx : 1 < x) (n : ℕ) :
    0 ≤ TwinPrimeWeightedDetector x n := by
  unfold TwinPrimeWeightedDetector
  exact div_nonneg (mul_nonneg (intervalIndicator_nonnegative x n)
    ArithmeticFunction.vonMangoldt_nonneg) (Real.log_nonneg (le_of_lt hx))

/-- Nonnegativity of the residue-aware candidate. -/
theorem ResidueAwareNonnegative {x : ℝ} {z n : ℕ} (hx : 1 < x) (hV : 0 < V0 z) :
    0 ≤ ResidueAwareComparisonCandidate x z n := by
  unfold ResidueAwareComparisonCandidate
  exact div_nonneg (mul_nonneg (intervalIndicator_nonnegative x n) (by split <;> positivity))
    (mul_nonneg (Real.log_nonneg (le_of_lt hx)) hV.le)

/-- Support of the weighted detector. -/
theorem TwinPrimeWeightedDetector_support {x : ℝ} {n : ℕ}
    (h : TwinPrimeWeightedDetector x n ≠ 0) : x / 2 < n ∧ (n : ℝ) ≤ x := by
  by_contra hn
  simp [TwinPrimeWeightedDetector, intervalIndicator, hn] at h

/-- Support of the residue-aware candidate. -/
theorem ResidueAwareSupport {x : ℝ} {z n : ℕ}
    (h : ResidueAwareComparisonCandidate x z n ≠ 0) : x / 2 < n ∧ (n : ℝ) ≤ x := by
  by_contra hn
  simp [ResidueAwareComparisonCandidate, intervalIndicator, hn] at h

/-- Even arguments vanish identically. -/
theorem ResidueAwareEvenVanishing {x : ℝ} {z n : ℕ} (hn : 2 ∣ n) :
    ResidueAwareComparisonCandidate x z n = 0 := by
  have hnot : ¬ Odd n := Nat.not_odd_iff_even.mpr (even_iff_two_dvd.mpr hn)
  simp [ResidueAwareComparisonCandidate, hnot]

/-- Coefficient independence is definitional: later coefficients are not arguments
of `ResidueAwareComparisonCandidate`. -/
theorem ResidueAwareCoefficientIndependent (x : ℝ) (z n : ℕ) :
    ResidueAwareComparisonCandidate x z n = ResidueAwareComparisonCandidate x z n := rfl

/-- Conditional pointwise bound from the lower half of a Mertens comparison
`V₀(z) ≥ c/log z`. -/
theorem ResidueAwarePointwiseBound {x : ℝ} {z n : ℕ}
    (hx : 1 < x) (hz : 1 < z) {c : ℝ} (hc : 0 < c)
    (hMertens : c / Real.log z ≤ V0 z) :
    ResidueAwareComparisonCandidate x z n ≤ Real.log z / (c * Real.log x) := by
  have hlogx : 0 < Real.log x := Real.log_pos hx
  have hlogz : 0 < Real.log (z : ℝ) := Real.log_pos (by exact_mod_cast hz)
  have hsmall : 0 < c / Real.log (z : ℝ) := div_pos hc hlogz
  have hV : 0 < V0 z := lt_of_lt_of_le hsmall hMertens
  have hinv : (V0 z)⁻¹ ≤ (c / Real.log (z : ℝ))⁻¹ := by
    rw [inv_le_inv₀ hV hsmall]
    exact hMertens
  have hind : intervalIndicator x n ≤ 1 := by
    unfold intervalIndicator
    split <;> norm_num
  unfold ResidueAwareComparisonCandidate
  split_ifs
  · calc
      intervalIndicator x n * 1 / (Real.log x * V0 z)
          ≤ 1 / (Real.log x * V0 z) := by
            apply div_le_div_of_nonneg_right
            · simpa using hind
            · positivity
      _ = (Real.log x)⁻¹ * (V0 z)⁻¹ := by field_simp
      _ ≤ (Real.log x)⁻¹ * (c / Real.log (z : ℝ))⁻¹ := by
        exact mul_le_mul_of_nonneg_left hinv (inv_nonneg.mpr hlogx.le)
      _ = Real.log z / (c * Real.log x) := by field_simp
  · simp only [mul_zero, zero_div]
    positivity

end TwinPrimeProject
