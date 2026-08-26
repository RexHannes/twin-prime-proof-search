import RequestProject.TwinPrimeDefinitions

open scoped BigOperators

namespace TwinPrimeProject

/-- The elementary factor identity underlying the twin-prime product. -/
theorem TwinPrimeFiniteEulerFactor {p : ℕ} (hp : 2 < p) :
    ((p : ℝ) * (p - 2)) / ((p - 1 : ℕ) : ℝ) ^ 2 =
      1 - 1 / ((p - 1 : ℕ) : ℝ) ^ 2 := by
  norm_num [Nat.cast_sub (show 1 ≤ p by omega)]
  have h : (p : ℝ) - 1 ≠ 0 := by
    exact sub_ne_zero.mpr (by exact_mod_cast (show p ≠ 1 by omega))
  field_simp
  ring

/-- Exact quotient identity, retaining the parity normalization in `V0`. -/
theorem W0DivV0Identity {z : ℕ} (hz : 3 ≤ z) :
    W0 z / V0 z =
      2 * ∏ p ∈ oddPrimesUpTo z,
        ((p : ℝ) * (p - 2)) / ((p - 1 : ℕ) : ℝ) ^ 2 := by
  unfold W0 V0
  have h2ne : (1 : ℝ) / 2 ≠ 0 := by norm_num
  field_simp
  rw [← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  have hp2 : 2 < p := (Finset.mem_filter.mp hp).2.2
  have hpne : (p : ℝ) ≠ 0 := by exact_mod_cast Nat.Prime.ne_zero ((Finset.mem_filter.mp hp).2.1)
  have hp1pos : (p : ℝ) - 1 > 0 := by linarith [show (p : ℝ) ≥ 3 by exact_mod_cast hp2]
  have hp1ne : (p : ℝ) - 1 ≠ 0 := ne_of_gt hp1pos
  have hp1ne' : (1 : ℝ) - 1 / p ≠ 0 := by
    rw [ne_eq, sub_eq_zero]
    field_simp
    exact_mod_cast Nat.Prime.ne_one ((Finset.mem_filter.mp hp).2.1)
  have hpmin1 : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
    have : 1 ≤ p := by omega
    rw [Nat.cast_sub this]
    norm_num
  calc (1 - 1 / ((p : ℝ) - 1)) / (1 - 1 / (p : ℝ))
      = (((p : ℝ) - 2) / ((p : ℝ) - 1)) / (((p : ℝ) - 1) / (p : ℝ)) := by field_simp; ring
    _ = ((p : ℝ) * ((p : ℝ) - 2)) / ((p : ℝ) - 1)^2 := by field_simp
    _ = ((p : ℝ) * ((p : ℝ) - 2)) / (((p - 1 : ℕ) : ℝ)) ^ 2 := by rw [hpmin1]
    _ = ((p : ℝ) * (p - 2)) / ((p - 1 : ℕ) : ℝ) ^ 2 := by rfl

/-- Exact finite singular-series identity.  No convergence claim is made. -/
theorem FiniteTwinPrimeSingularSeries_identity {z : ℕ} (hz : 3 ≤ z) :
    W0 z / V0 z = FiniteTwinPrimeSingularSeries z := by
  rw [W0DivV0Identity hz]
  unfold FiniteTwinPrimeSingularSeries
  congr 1
  apply Finset.prod_congr rfl
  intro p hp
  apply TwinPrimeFiniteEulerFactor
  exact (Finset.mem_filter.mp hp).2.2

end TwinPrimeProject
