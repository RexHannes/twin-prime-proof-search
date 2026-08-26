/-
# Gate 1B — routing variation (abstract form only)

This file combines the UniversalV8 discrete-Abel and jump-count theorems into the single
abstract statement that a routed weight with few jumps is cheap in the backend-dual norm.

CRITICAL: the antecedent is NOT asserted for the actual Gate routing.  `ROUTE-BV45` is a
source-open interface: whether the literal routing multiplicity is piecewise constant with
few jumps is unknown here and must be supplied externally.  Nothing in this file may be
read as evidence for it.
-/
import UniversalV8.BoundedVariation

open Finset

namespace Gate1B.SafeAlgebra

open UniversalV8

/-- **Abstract routed backend-dual bound.**  If the backend partial sums of `a` on `[m,n)`
are bounded by `Δ`, and the routing weight `w` is bounded by `M` with `J` jumps in
`[m, n-1)`, then `|∑ a w| ≤ Δ M (1 + 2 J)`. -/
theorem routed_weighted_sum_bound (m n : ℕ) (hmn : m < n) (a w : ℕ → ℂ) (Δ M : ℝ)
    (hP : ∀ t, m ≤ t → t < n → ‖partialSum m a t‖ ≤ Δ)
    (hM : ∀ k, m ≤ k → k < n → ‖w k‖ ≤ M) :
    ‖∑ k ∈ Finset.Ico m n, a k * w k‖
      ≤ Δ * (M * (1 + 2 * (jumpSet m (n - 1) w).card)) := by
  have hΔ : 0 ≤ Δ := le_trans (norm_nonneg _) (hP m le_rfl hmn)
  refine le_trans (weighted_sum_le_partialSum_mul_dBV m n hmn a w Δ M hP hM) ?_
  have hjump := dBV_le_of_jumpCount m (n - 1) w M (fun k hk1 hk2 => hM k hk1 (by omega))
  exact mul_le_mul_of_nonneg_left hjump hΔ

end Gate1B.SafeAlgebra
