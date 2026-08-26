/-
# Gate 1B safe extension — prime-centered square mass

Exact finite decomposition and finite upper bounds for

    ∑_{p ∈ S} L_p² ρ_p(N)²,      ρ_p(N) = 1_{p ∣ N} − 1/p,

with `ρ` the already banked centering weight
`TwinPrimeProject.Gate01Consolidation.rho`.

No prime number theorem, no prime-counting estimate, no logarithmic weight and
no `X^{o(1)}` claim occurs here: the bounds are in terms of the two finite
quantities `∑_{p ∣ N} L_p²` and `∑_p L_p²/p²`.
-/
import RequestProject.NANC.Gate01Consolidation.CRTCentering

namespace Gate1B.SafeExtensions

open Finset TwinPrimeProject.Gate01Consolidation

/-- **Prime-centered square-mass split.**  The exact decomposition into the
`p ∣ N` and `p ∤ N` parts. -/
theorem primeCenteredSquareMass_split (S : Finset ℕ) (L : ℕ → ℝ) (N : ℕ) :
    ∑ p ∈ S, L p ^ 2 * (rho p N) ^ 2
      = (∑ p ∈ S.filter (fun p => p ∣ N), L p ^ 2 * (1 - 1 / (p : ℝ)) ^ 2)
        + ∑ p ∈ S.filter (fun p => ¬ p ∣ N), L p ^ 2 * (1 / (p : ℝ)) ^ 2 := by
  rw [← Finset.sum_filter_add_sum_filter_not S (fun p => p ∣ N)
        (fun p => L p ^ 2 * (rho p N) ^ 2)]
  congr 1
  · refine Finset.sum_congr rfl fun p hp => ?_
    rw [show rho p N = 1 - 1 / (p : ℝ) by simp [rho, (Finset.mem_filter.mp hp).2]]
  · refine Finset.sum_congr rfl fun p hp => ?_
    have h : ¬ p ∣ N := (Finset.mem_filter.mp hp).2
    rw [show rho p N = -(1 / (p : ℝ)) by simp [rho, h]]
    ring

/-- **Prime-centered square-mass bound.**  For indices `p ≥ 1`,

    ∑_{p ∈ S} L_p² ρ_p(N)² ≤ ∑_{p ∈ S, p ∣ N} L_p² + ∑_{p ∈ S} L_p²/p². -/
theorem primeCenteredSquareMass_le (S : Finset ℕ) (L : ℕ → ℝ) (N : ℕ)
    (hS : ∀ p ∈ S, 1 ≤ p) :
    ∑ p ∈ S, L p ^ 2 * (rho p N) ^ 2
      ≤ (∑ p ∈ S.filter (fun p => p ∣ N), L p ^ 2) + ∑ p ∈ S, L p ^ 2 / (p : ℝ) ^ 2 := by
  rw [primeCenteredSquareMass_split S L N]
  refine add_le_add ?_ ?_
  · refine Finset.sum_le_sum fun p hp => ?_
    have hp1 : 1 ≤ p := hS p (Finset.mem_filter.mp hp).1
    have hpR : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp1
    have h0 : (0 : ℝ) < (p : ℝ) := lt_of_lt_of_le zero_lt_one hpR
    have hle : 1 / (p : ℝ) ≤ 1 := by rw [div_le_one h0]; exact hpR
    have hge : (0 : ℝ) ≤ 1 / (p : ℝ) := by positivity
    have hsq : (1 - 1 / (p : ℝ)) ^ 2 ≤ 1 := by nlinarith
    calc L p ^ 2 * (1 - 1 / (p : ℝ)) ^ 2 ≤ L p ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left hsq (sq_nonneg (L p))
      _ = L p ^ 2 := mul_one _
  · calc (∑ p ∈ S.filter (fun p => ¬ p ∣ N), L p ^ 2 * (1 / (p : ℝ)) ^ 2)
        = ∑ p ∈ S.filter (fun p => ¬ p ∣ N), L p ^ 2 / (p : ℝ) ^ 2 :=
          Finset.sum_congr rfl fun p _ => by rw [div_pow, one_pow]; ring
      _ ≤ ∑ p ∈ S, L p ^ 2 / (p : ℝ) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun p _ _ => by positivity)

end Gate1B.SafeExtensions
