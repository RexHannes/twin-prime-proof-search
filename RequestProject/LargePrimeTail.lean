import RequestProject.LocalDensity

open scoped BigOperators

namespace TwinPrimeProject

/-- Prime divisors of `m` above the sieve cutoff. -/
def largePrimeDivisors (z m : ℕ) : Finset ℕ :=
  m.primeFactors.filter fun p => z < p

/-- Explicit interface for the exact totient-factor split.  This is kept visible
rather than installed as an axiom while its full factorization proof is pending. -/
structure TotientLocalFactorSplitInput where
  split : ∀ {z m : ℕ}, 0 < m → Odd m →
    (m : ℝ) / Nat.totient m =
      ResidueAwareDensityFactor z m *
        ∏ p ∈ largePrimeDivisors z m, (1 - (1 : ℝ) / p)⁻¹

/-- Conditional accessor displaying the exact dependency. -/
theorem TotientLocalFactorSplit (I : TotientLocalFactorSplitInput)
    {z m : ℕ} (hm : 0 < m) (hmodd : Odd m) :
    (m : ℝ) / Nat.totient m =
      ResidueAwareDensityFactor z m *
        ∏ p ∈ largePrimeDivisors z m, (1 - (1 : ℝ) / p)⁻¹ :=
  I.split hm hmodd

/-- Elementary count of distinct prime divisors above `z`. -/
theorem LargePrimeDivisorCount {z m : ℕ} (hz : 1 < z) (hm : 0 < m) :
    ((largePrimeDivisors z m).card : ℝ) ≤ Real.log m / Real.log z := by
  have h1 : z ^ (largePrimeDivisors z m).card ≤ m := by
    have hprod_dvd : (largePrimeDivisors z m).prod id ∣ m := by
      have := Finset.prod_dvd_prod_of_subset (s := largePrimeDivisors z m) (t := m.primeFactors) id (Finset.filter_subset _ _)
      exact dvd_trans this (Nat.prod_primeFactors_dvd m)
    have hprod_ge : z ^ (largePrimeDivisors z m).card ≤ (largePrimeDivisors z m).prod id := by
      have hle : ∀ p ∈ largePrimeDivisors z m, z ≤ p := fun p hp => le_of_lt (Finset.mem_filter.mp hp).2
      calc z ^ (largePrimeDivisors z m).card = (largePrimeDivisors z m).prod (fun _ => z) := by simp [Finset.prod_const]
        _ ≤ (largePrimeDivisors z m).prod id := Finset.prod_le_prod' hle
    exact Nat.le_trans hprod_ge (Nat.le_of_dvd hm hprod_dvd)
  have h2 : (largePrimeDivisors z m).card * Real.log z ≤ Real.log m := by
    have : Real.log (z ^ (largePrimeDivisors z m).card) ≤ Real.log m := by
      apply Real.log_le_log (by positivity)
      exact_mod_cast h1
    simp [Real.log_pow] at this
    exact this
  rw [le_div_iff₀ (Real.log_pos (by norm_cast : (1 : ℝ) < z))]
  exact h2

/-- Reciprocal tail bound obtained from the count and `p>z`. -/
theorem LargePrimeReciprocalTail {z m : ℕ} (hz : 1 < z) (hm : 0 < m) :
    ∑ p ∈ largePrimeDivisors z m, (1 : ℝ) / p ≤
      Real.log m / ((z : ℝ) * Real.log z) := by
  have hterm : ∀ p ∈ largePrimeDivisors z m, (1 : ℝ) / p ≤ 1 / (z : ℝ) := by
    intro p hp
    have hpz : z < p := (Finset.mem_filter.mp hp).2
    exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast hpz.le)
  calc
    ∑ p ∈ largePrimeDivisors z m, (1 : ℝ) / p
        ≤ ∑ _p ∈ largePrimeDivisors z m, (1 / (z : ℝ)) :=
          Finset.sum_le_sum fun p hp => hterm p hp
    _ = ((largePrimeDivisors z m).card : ℝ) / z := by simp [div_eq_mul_inv]
    _ ≤ (Real.log m / Real.log z) / z := by
      gcongr
      exact LargePrimeDivisorCount hz hm
    _ = Real.log m / ((z : ℝ) * Real.log z) := by ring

end TwinPrimeProject
