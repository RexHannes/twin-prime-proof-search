/-
# Universal safe algebra — discrete bounded variation (re-export)

Proved in `UniversalV8/BoundedVariation.lean`: variation and `dBV`, the closure rules
(constant, scalar multiple, sum, difference, product, restriction, concatenation,
piecewise constant), the jump-count bounds, and the `dBV` form of the weighted-sum
inequality.  Re-exported here; nothing is duplicated.

No asymptotic `X^{o(1)}` statement occurs anywhere in this layer.
-/
import UniversalV8.BoundedVariation

namespace Universal.SafeAlgebra

export UniversalV8 (variation dBV jumpSet variation_const variation_smul variation_add
  variation_sub variation_mul variation_concat variation_mono variation_piecewise_const
  variation_le_two_mul_bound_mul_jumpCount dBV_le_of_jumpCount
  weighted_sum_le_partialSum_mul_dBV)

/-- An interval indicator has `O(1)` discrete variation: at most two jumps, hence
variation at most `2` (with `M = 1`). -/
theorem variation_indicator_le (m n A B : ℕ) :
    UniversalV8.variation m n (fun k => if A ≤ k ∧ k < B then (1 : ℂ) else 0)
      ≤ 2 * 1 * ((UniversalV8.jumpSet m n (fun k => if A ≤ k ∧ k < B then (1 : ℂ) else 0)).card) := by
  refine UniversalV8.variation_le_two_mul_bound_mul_jumpCount m n _ 1 ?_
  intro k _ _
  dsimp only
  split <;> simp

end Universal.SafeAlgebra
