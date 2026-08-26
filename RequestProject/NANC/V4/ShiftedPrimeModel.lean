/-
NANC V4 — shifted-prime weights and the comparison-model structure.

Only elementary facts are proved here.  No analytic (PNT / progression-mean /
singular-series) statement is proved or assumed.
-/
import Mathlib
import RequestProject.NANC.V4.Status

namespace NANC.V4

open scoped BigOperators

/-- The shifted-prime weight `n ↦ log(n+2) · 1_{n+2 prime}`. -/
noncomputable def shiftedPrimeWeight (n : ℕ) : ℝ :=
  if Nat.Prime (n + 2) then Real.log (n + 2) else 0

theorem shiftedPrimeWeight_nonneg (n : ℕ) : 0 ≤ shiftedPrimeWeight n := by
  unfold shiftedPrimeWeight
  split
  · exact Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by omega))
  · exact le_refl 0

theorem shiftedPrimeWeight_eq_zero_of_not_prime {n : ℕ} (h : ¬ Nat.Prime (n + 2)) :
    shiftedPrimeWeight n = 0 := by
  simp [shiftedPrimeWeight, h]

/-- The weight is strictly positive exactly on the shifted primes (for `n ≥ 1`). -/
theorem shiftedPrimeWeight_pos {n : ℕ} (hn : 1 ≤ n) (h : Nat.Prime (n + 2)) :
    0 < shiftedPrimeWeight n := by
  have h3 : (1 : ℝ) < (n : ℝ) + 2 := by
    have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  simp only [shiftedPrimeWeight, if_pos h]
  exact Real.log_pos h3

/-- A generic nonnegative prime weight, used when `Real.log` positivity is
inconvenient: positivity on the relevant set is then an explicit hypothesis. -/
structure PrimeWeight where
  w : ℕ → ℝ
  w_nonneg : ∀ n, 0 ≤ w n
  w_eq_zero_of_not_shifted_prime : ∀ n, ¬ Nat.Prime (n + 2) → w n = 0

/-- The concrete logarithmic shifted-prime weight as a `PrimeWeight`. -/
noncomputable def logShiftedPrimeWeight : PrimeWeight where
  w := shiftedPrimeWeight
  w_nonneg := shiftedPrimeWeight_nonneg
  w_eq_zero_of_not_shifted_prime := fun _ h => shiftedPrimeWeight_eq_zero_of_not_prime h

/-- The Ford–Maynard comparison model: a sequence `w = a - b`, where `a` is the
"true" nonnegative weight and `b` the nonnegative comparison weight. -/
structure ShiftedPrimeComparisonModel where
  a : ℕ → ℝ
  b : ℕ → ℝ
  w : ℕ → ℝ
  a_nonneg : ∀ n, 0 ≤ a n
  b_nonneg : ∀ n, 0 ≤ b n
  w_eq : ∀ n, w n = a n - b n

namespace ShiftedPrimeComparisonModel

variable (M : ShiftedPrimeComparisonModel)

theorem w_add_b (n : ℕ) : M.w n + M.b n = M.a n := by rw [M.w_eq]; ring

theorem sum_w (S : Finset ℕ) : ∑ n ∈ S, M.w n = (∑ n ∈ S, M.a n) - ∑ n ∈ S, M.b n := by
  simp [M.w_eq, Finset.sum_sub_distrib]

end ShiftedPrimeComparisonModel

/-- Status: the analytic properties of any concrete comparison sequence `b`
are *not* banked here. -/
def statusComparisonAsymptotics : BankStatus := BankStatus.externalAnalyticInput

end NANC.V4
