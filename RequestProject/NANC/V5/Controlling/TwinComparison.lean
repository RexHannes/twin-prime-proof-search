/-
NANC V5 CONTROLLING LAYER — TWIN COMPARISON: PARITY FACTS.

The candidate triple

    a_n = log(n+2) · 1_{n+2 prime},
    b_n = 2·C₂ · 1_{n odd} · ∏_{p ∣ n, p > 2} (p-1)/(p-2),
    w_n = a_n - b_n

is the V5 candidate (`candidateA`, `candidateB`, `candidateW`); it is not
redefined.  What is added here are the elementary *parity* facts that the
controlling audit uses, in particular the multiplier form

    m even  ⟹  b(m·n) = 0,
    m even, m·n ≠ 0  ⟹  a(m·n) = 0  and hence  w(m·n) = 0.

No analytic property of `b` is proved or assumed.
-/
import Mathlib
import RequestProject.NANC.V5.Controlling.TypeIIExactConvention

namespace NANC.V5.Controlling

open scoped BigOperators
open NANC.V4 NANC.V5

/-- For even `n > 0` the shifted-prime weight vanishes: `n + 2` is then an even
number greater than `2`. -/
theorem shiftedPrimeWeight_even_pos_eq_zero {n : ℕ} (heven : 2 ∣ n) (hpos : 0 < n) :
    shiftedPrimeWeight n = 0 := by
  refine shiftedPrimeWeight_eq_zero_of_not_prime ?_
  intro hp
  have hdvd : 2 ∣ n + 2 := Dvd.dvd.add heven (dvd_refl 2)
  rcases (Nat.Prime.eq_one_or_self_of_dvd hp 2 hdvd) with h | h
  · exact absurd h (by norm_num)
  · omega

/-- Multiplier form: if the multiplier `m` is even, the comparison weight of
`m·n` vanishes. -/
theorem candidateB_mul_even {C2 : ℝ} {m : ℕ} (hm : 2 ∣ m) (n : ℕ) :
    candidateB C2 (m * n) = 0 :=
  twinComparisonWeight_even (Dvd.dvd.mul_right hm n)

/-- Multiplier form: if the multiplier `m` is even and `m·n ≠ 0`, the prime-side
weight of `m·n` vanishes as well. -/
theorem candidateA_mul_even {m : ℕ} (hm : 2 ∣ m) {n : ℕ} (hpos : 0 < m * n) :
    candidateA (m * n) = 0 :=
  shiftedPrimeWeight_even_pos_eq_zero (Dvd.dvd.mul_right hm n) hpos

/-- Consequently the whole comparison sequence vanishes on even multiplier
products: `w(m·n) = 0` for even `m` and `m·n > 0`. -/
theorem candidateW_mul_even {C2 : ℝ} {m : ℕ} (hm : 2 ∣ m) {n : ℕ} (hpos : 0 < m * n) :
    candidateW C2 (m * n) = 0 := by
  simp [candidateW, candidateA_mul_even hm hpos, candidateB_mul_even hm n]

/-- The prime side is nonnegative. -/
theorem candidateA_nonneg (n : ℕ) : 0 ≤ candidateA n := shiftedPrimeWeight_nonneg n

/-- The comparison side is nonnegative for `0 ≤ C₂`. -/
theorem candidateB_nonneg {C2 : ℝ} (hC : 0 ≤ C2) (n : ℕ) : 0 ≤ candidateB C2 n :=
  twinComparisonWeight_nonneg hC n

/-- `w = a - b`, by definition. -/
theorem candidateW_eq (C2 : ℝ) (n : ℕ) : candidateW C2 n = candidateA n - candidateB C2 n := rfl

/-- The value of the comparison side at `n = 1` is `2·C₂`. -/
theorem candidateB_one (C2 : ℝ) : candidateB C2 1 = 2 * C2 := twinComparisonWeight_one C2

/-- On an even-multiplier dyadic block the whole Type-I inner sum vanishes. -/
theorem candidateW_sum_even_multiplier {C2 : ℝ} {m : ℕ} (hm : 2 ∣ m) (hm0 : 0 < m)
    (S : Finset ℕ) (hS : ∀ n ∈ S, 0 < n) :
    ∑ n ∈ S, candidateW C2 (m * n) = 0 := by
  refine Finset.sum_eq_zero ?_
  intro n hn
  exact candidateW_mul_even hm (Nat.mul_pos hm0 (hS n hn))

/-- Status entry: the twin comparison layer is elementary algebra only. -/
def twinComparisonEntry : ControlEntry where
  name := "twin comparison candidate (a, b, w) — parity algebra"
  status := ControlStatus.leanProved
  notes := "Only elementary parity/positivity facts.  Progression asymptotics stay uninhabited."

/-- Status entry: the analytic behaviour of `b` remains open. -/
def twinComparisonAnalyticEntry : ControlEntry where
  name := "comparison progression asymptotics for b"
  status := ControlStatus.uninhabitedInterface
  notes := "Never proved or assumed in this bank."

theorem twinComparisonAnalyticEntry_not_leanEvidence :
    ControlEntry.IsLeanEvidence twinComparisonAnalyticEntry = false := rfl

end NANC.V5.Controlling
