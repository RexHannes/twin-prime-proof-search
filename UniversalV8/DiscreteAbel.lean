/-
# UniversalV8 Module A — exact discrete Abel summation (summation by parts)

This file proves ONLY exact finite algebra and its immediate normed consequence.

It does NOT contain any analytic number theory: no Mertens estimate, no
Vinogradov–Korobov zero-free region, no Möbius cancellation.  Those are listed
as external interfaces in `UniversalV8/Interfaces.lean`.
-/
import Mathlib

open Finset

namespace UniversalV8

/-- Local partial sum `P(t) = ∑_{m ≤ k ≤ t} a k`. -/
noncomputable def partialSum (m : ℕ) (a : ℕ → ℂ) (t : ℕ) : ℂ := ∑ k ∈ Finset.Icc m t, a k

@[simp] theorem partialSum_self (m : ℕ) (a : ℕ → ℂ) : partialSum m a m = a m := by
  simp [partialSum]

theorem partialSum_succ (m n : ℕ) (h : m ≤ n) (a : ℕ → ℂ) :
    partialSum m a (n + 1) = partialSum m a n + a (n + 1) := by
  simp [partialSum, Finset.sum_Icc_succ_top (by omega : m ≤ n + 1)]

/-- **(ABEL), successor form.**  Exact discrete summation by parts on `[m, n]`. -/
theorem local_sum_by_parts_succ (m n : ℕ) (hmn : m ≤ n) (a w : ℕ → ℂ) :
    ∑ k ∈ Finset.Ico m (n + 1), a k * w k
      = partialSum m a n * w n
        - ∑ k ∈ Finset.Ico m n, partialSum m a k * (w (k + 1) - w k) := by
  induction n, hmn using Nat.le_induction with
  | base => simp [partialSum]
  | succ n hn ih =>
      rw [Finset.sum_Ico_succ_top (by omega), ih, Finset.sum_Ico_succ_top hn,
        partialSum_succ m n hn]
      ring

/-- **(ABEL).**  For `m < n`,
`∑_{m ≤ k < n} a k w k = P(n-1) w(n-1) − ∑_{m ≤ k < n-1} P(k) (w(k+1) − w(k))`. -/
theorem local_sum_by_parts (m n : ℕ) (hmn : m < n) (a w : ℕ → ℂ) :
    ∑ k ∈ Finset.Ico m n, a k * w k
      = partialSum m a (n - 1) * w (n - 1)
        - ∑ k ∈ Finset.Ico m (n - 1), partialSum m a k * (w (k + 1) - w k) := by
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
  simpa using local_sum_by_parts_succ m j (by omega) a w

/-- Discrete variation of `w` across the increments of `[m, n)`. -/
noncomputable def variation (m n : ℕ) (w : ℕ → ℂ) : ℝ := ∑ k ∈ Finset.Ico m n, ‖w (k + 1) - w k‖

/-- **(ABEL-BV).**  A uniform bound `Δ` on the partial sums controls the weighted sum by
the endpoint weight plus the discrete variation of the weight. -/
theorem norm_sum_le_partialSumBound_mul_variation (m n : ℕ) (hmn : m < n) (a w : ℕ → ℂ)
    (Δ : ℝ) (hP : ∀ t, m ≤ t → t < n → ‖partialSum m a t‖ ≤ Δ) :
    ‖∑ k ∈ Finset.Ico m n, a k * w k‖
      ≤ Δ * (‖w (n - 1)‖ + variation m (n - 1) w) := by
  have hΔ : 0 ≤ Δ := le_trans (norm_nonneg _) (hP m le_rfl hmn)
  rw [local_sum_by_parts m n hmn a w]
  refine le_trans (norm_sub_le _ _) ?_
  have h1 : ‖partialSum m a (n - 1) * w (n - 1)‖ ≤ Δ * ‖w (n - 1)‖ := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hP _ (by omega) (by omega)) (norm_nonneg _)
  have h2 : ‖∑ k ∈ Finset.Ico m (n - 1), partialSum m a k * (w (k + 1) - w k)‖
      ≤ Δ * variation m (n - 1) w := by
    refine le_trans (norm_sum_le _ _) ?_
    rw [variation, Finset.mul_sum]
    refine Finset.sum_le_sum ?_
    intro k hk
    simp only [Finset.mem_Ico] at hk
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hP _ hk.1 (by omega)) (norm_nonneg _)
  calc ‖partialSum m a (n - 1) * w (n - 1)‖
        + ‖∑ k ∈ Finset.Ico m (n - 1), partialSum m a k * (w (k + 1) - w k)‖
      ≤ Δ * ‖w (n - 1)‖ + Δ * variation m (n - 1) w := add_le_add h1 h2
    _ = Δ * (‖w (n - 1)‖ + variation m (n - 1) w) := by ring

end UniversalV8
