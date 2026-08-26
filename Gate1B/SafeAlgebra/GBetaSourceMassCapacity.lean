/-
# Gate 1B v8.2 — GCD-β source-mass capacity

Abstract capacity bookkeeping: a stratified source mass bounded stratum by
stratum is bounded by (number of strata) × (stratum bound), and the
corresponding exponent budget clears a `Y^{-1}` target exactly when the
exponents add up correctly.

**The stratum bounds are inputs.**  No `GCD_BETA_TARGET_PASS` is asserted here;
that phrase appears in this project only as a description of what the inputs
would give.
-/
import Mathlib
import Gate1B.SafeAlgebra.GCDSchurCapacity

namespace Gate1B.SafeAlgebra

open Finset

/-- **Stratified source mass.**  A per-stratum bound gives a total bound. -/
theorem gcdBetaMass_of_strata_bounds {ι : Type*} (s : Finset ι) (m : ι → ℝ) (b : ℝ)
    (hm : ∀ i ∈ s, m i ≤ b) : ∑ i ∈ s, m i ≤ (s.card : ℝ) * b := by
  calc ∑ i ∈ s, m i ≤ ∑ _i ∈ s, b := Finset.sum_le_sum hm
    _ = (s.card : ℝ) * b := by simp [mul_comm]

/-- **Exponent form of the source-mass capacity.**  If the strata count has
exponent `sExp` and each stratum has mass exponent `bExp` with
`sExp + bExp ≤ −1`, the total mass budget clears `Y^{-1}`. -/
theorem gcdBetaMass_capacity_Exponent {Y : ℝ} (hY : 1 ≤ Y) {sExp bExp : ℚ}
    (h : sExp + bExp ≤ -1) :
    Y ^ ((sExp : ℝ) + (bExp : ℝ)) ≤ Y ^ ((-1 : ℚ) : ℝ) :=
  Real.rpow_le_rpow_of_exponent_le hY (by exact_mod_cast h)

/-- **GCD-β weighted Schur capacity.**  Combining a uniform cross-term majorant
with the banked weighted Schur bound gives the synthesised energy bound with the
explicit budget `#Γ · c`. -/
theorem gcdBetaWeightedSchur_of_bounds {H K : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K]
    {Γ : Type*} [Fintype Γ] (B : Γ → (H →L[ℂ] K)) (f : Γ → H) (k : Γ → Γ → ℝ) (c : ℝ)
    (hk : ∀ γ γ', ‖ContinuousLinearMap.adjoint (B γ) ∘L B γ'‖ ≤ k γ γ')
    (hknn : ∀ γ γ', 0 ≤ k γ γ') (hsymm : ∀ γ γ', k γ γ' = k γ' γ)
    (hc : ∀ γ γ', k γ γ' ≤ c) :
    ‖UniversalV8.synthesis B f‖ ^ 2 ≤ ((Fintype.card Γ : ℝ) * c) * ∑ γ, ‖f γ‖ ^ 2 :=
  gcdSchurCapacity B f k ((Fintype.card Γ : ℝ) * c) hk hknn hsymm
    (fun γ => gcdSchur_rowBudget_of_uniform k c hc γ)

end Gate1B.SafeAlgebra
