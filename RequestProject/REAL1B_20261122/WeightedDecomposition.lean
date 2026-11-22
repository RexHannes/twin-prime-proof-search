import RequestProject.WeightedTwinCount

open scoped BigOperators

namespace TwinPrimeProject

/-- Construct the finite decomposition input in the historical GitHub bank. -/
theorem weighted_decomposition_input : Nonempty WeightedTwinPrimeCountDecompositionInput := by
  classical
  refine ⟨⟨?_⟩⟩
  intro x _
  unfold dyadicTwinPrimes primePowerError primePowerContamination
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  have hi := (Finset.mem_filter.mp hp).2.2
  unfold TwinPrimeWeightedDetector intervalIndicator
  rw [if_pos hi, one_mul]
  by_cases h : (p + 2).Prime
  · simp [h, ArithmeticFunction.vonMangoldt_apply_prime h]
  · by_cases hpow : IsPrimePow (p + 2)
    · simp [h, hpow]
    · simp [h, hpow, ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hpow]

/-- No proof-carrying input record is required of callers. -/
theorem weighted_decomposition {x : ℝ} (hx : 1 < x) :
    ∑ p ∈ dyadicPrimes x, TwinPrimeWeightedDetector x p =
      (∑ p ∈ dyadicTwinPrimes x, Real.log (p + 2) / Real.log x) + primePowerError x := by
  obtain ⟨I⟩ := weighted_decomposition_input
  exact WeightedTwinPrimeCountDecomposition I hx

end TwinPrimeProject

#print axioms TwinPrimeProject.weighted_decomposition_input
#print axioms TwinPrimeProject.weighted_decomposition
