/-
NANC V5 — THE TWIN COMPARISON CANDIDATE (ALGEBRA ONLY).

The local factor itself is the V4 object `twinLocalFactor`; it is *not*
redefined here.  What this file adds is

* the named comparison weight `twinComparisonWeight C₂`;
* the concrete candidate triple `a = shifted-prime log weight`,
  `b = twinComparisonWeight C₂`, `w = a - b`;
* the abstract positive-prime-weight variant of the same triple.

No analytic property of `b` is proved or assumed.
-/
import Mathlib
import RequestProject.NANC.V5.FordMaynardSource

namespace NANC.V5

open scoped BigOperators
open NANC.V4

/-- The twin comparison weight: the V4 local factor, named for the V5 bank. -/
noncomputable def twinComparisonWeight (C2 : ℝ) (n : ℕ) : ℝ := twinLocalFactor C2 n

theorem twinComparisonWeight_eq (C2 : ℝ) (n : ℕ) :
    twinComparisonWeight C2 n = twinLocalFactor C2 n := rfl

theorem twinComparisonWeight_nonneg {C2 : ℝ} (hC : 0 ≤ C2) (n : ℕ) :
    0 ≤ twinComparisonWeight C2 n := twinLocalFactor_nonneg hC n

theorem twinComparisonWeight_even {C2 : ℝ} {n : ℕ} (h : 2 ∣ n) :
    twinComparisonWeight C2 n = 0 := twinLocalFactor_even h

theorem twinComparisonWeight_one (C2 : ℝ) : twinComparisonWeight C2 1 = 2 * C2 :=
  twinLocalFactor_one C2

/-- The shifted-prime side of the candidate: `a_n = log(n+2)·1_{n+2 prime}`. -/
noncomputable def candidateA (n : ℕ) : ℝ := shiftedPrimeWeight n

/-- The comparison side of the candidate: `b_n = twinComparisonWeight C₂ n`. -/
noncomputable def candidateB (C2 : ℝ) (n : ℕ) : ℝ := twinComparisonWeight C2 n

/-- The comparison sequence of the candidate: `w_n = a_n - b_n`. -/
noncomputable def candidateW (C2 : ℝ) (n : ℕ) : ℝ := candidateA n - candidateB C2 n

/-- The candidate as a V4 comparison model. -/
noncomputable def twinCandidateModel (C2 : ℝ) (hC : 0 ≤ C2) : ShiftedPrimeComparisonModel :=
  twinComparisonModel C2 hC candidateA (fun n => shiftedPrimeWeight_nonneg n)

@[simp] theorem twinCandidateModel_a (C2 : ℝ) (hC : 0 ≤ C2) (n : ℕ) :
    (twinCandidateModel C2 hC).a n = candidateA n := rfl

@[simp] theorem twinCandidateModel_b (C2 : ℝ) (hC : 0 ≤ C2) (n : ℕ) :
    (twinCandidateModel C2 hC).b n = candidateB C2 n := rfl

@[simp] theorem twinCandidateModel_w (C2 : ℝ) (hC : 0 ≤ C2) (n : ℕ) :
    (twinCandidateModel C2 hC).w n = candidateW C2 n := rfl

/-- The candidate `w` vanishes on even `n` up to the prime side only:
for even `n` the comparison term drops out entirely. -/
theorem candidateW_even {C2 : ℝ} {n : ℕ} (h : 2 ∣ n) : candidateW C2 n = candidateA n := by
  simp [candidateW, candidateB, twinComparisonWeight_even h]

/-- The abstract variant: an arbitrary nonnegative prime weight in place of the
logarithmic one, for use when `Real.log` is inconvenient. -/
noncomputable def genericCandidateModel (C2 : ℝ) (hC : 0 ≤ C2) (W : PrimeWeight) :
    ShiftedPrimeComparisonModel :=
  twinComparisonModel C2 hC W.w W.w_nonneg

theorem genericCandidateModel_w (C2 : ℝ) (hC : 0 ≤ C2) (W : PrimeWeight) (n : ℕ) :
    (genericCandidateModel C2 hC W).w n = W.w n - twinComparisonWeight C2 n := rfl

/-- Provenance of the candidate: it is a *definition*, not a theorem about primes. -/
def twinCandidateProvenance : Provenance where
  status := AuditStatus.leanProved
  sourceName := "NANC V5 TwinComparison"
  sourceVersion := "this repository"
  scope := "elementary algebra of the comparison candidate only"
  notes := "All analytic properties of b (progression mean, singular series) stay uninhabited."

end NANC.V5
