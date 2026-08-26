/-
# Universal safe algebra — finite Abel summation (re-export)

The exact identity and the backend-dual-norm inequality are proved once, in
`UniversalV8/DiscreteAbel.lean`, and are re-exported here under the `Universal.SafeAlgebra`
namespace.  Nothing is duplicated or re-proved.
-/
import UniversalV8.DiscreteAbel

namespace Universal.SafeAlgebra

export UniversalV8 (partialSum local_sum_by_parts local_sum_by_parts_succ
  norm_sum_le_partialSumBound_mul_variation)

/-- **Backend-Dual Norm principle (D3).**  A cumulative-sum backend bound plus the discrete
variation of the coefficient weight bound the weighted sum.  Named corollary of the
finite Abel identity; no Mertens/Vinogradov–Korobov decay is involved. -/
theorem backendDualNorm_discreteBV (m n : ℕ) (hmn : m < n) (a w : ℕ → ℂ) (Δ : ℝ)
    (hP : ∀ t, m ≤ t → t < n → ‖UniversalV8.partialSum m a t‖ ≤ Δ) :
    ‖∑ k ∈ Finset.Ico m n, a k * w k‖
      ≤ Δ * (‖w (n - 1)‖ + UniversalV8.variation m (n - 1) w) :=
  UniversalV8.norm_sum_le_partialSumBound_mul_variation m n hmn a w Δ hP

end Universal.SafeAlgebra
