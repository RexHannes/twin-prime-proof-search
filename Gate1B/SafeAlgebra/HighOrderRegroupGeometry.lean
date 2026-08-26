/-
# Gate 1B v8.3 — general high-order regroup exponent geometry

**Status: PROVED_FINITE.**

Pure finite arithmetic of the nine-coordinate defect/model split.  With `j`
defect coordinates there are `9 - j` model coordinates.  If two models are kept
for completion and all the remaining models are absorbed into the coefficient
`B`, the number of coordinates carried by `B` is

    j + (9 - j - 2) = 7,

independently of `j`, for every `j ≤ 7`.  Orders `8` and `9` are the degenerate
cases: exactly one model, respectively none, remains.

Nothing here is analytic: no Kloosterman estimate, no completion bound, no
claim that `B ~ Y^7` is *small*.  Only the exponent bookkeeping is asserted.
-/
import Mathlib

namespace Gate1B.SafeAlgebra

/-- Number of model coordinates left at defect order `j` out of nine. -/
def remainingModels (j : ℕ) : ℕ := 9 - j

/-- Number of coordinates absorbed into `B` once two models are retained for
completion. -/
def absorbedModels (j : ℕ) : ℕ := remainingModels j - 2

/-- The exponent of the regrouped coefficient `B`: the `j` defect coordinates
together with the absorbed models. -/
def regroupBExponent (j : ℕ) : ℕ := j + absorbedModels j

/-- At defect order at most seven, at least two model coordinates remain. -/
theorem hasTwoModels_of_order_le_seven {j : ℕ} (hj : j ≤ 7) :
    2 ≤ remainingModels j := by
  unfold remainingModels; omega

/-- **The exact high-order regroup identity.**  For every `j ≤ 7`,
`j + (9 - j - 2) = 7`. -/
theorem regroupBExponent_eq_seven {j : ℕ} (hj : j ≤ 7) : regroupBExponent j = 7 := by
  unfold regroupBExponent absorbedModels remainingModels; omega

/-- Order five: `5` defects, `2` absorbed models, `2` completion models. -/
theorem regroup_order_five :
    remainingModels 5 = 4 ∧ absorbedModels 5 = 2 ∧ regroupBExponent 5 = 7 := by
  exact ⟨rfl, rfl, rfl⟩

/-- Order six: `6` defects, `1` absorbed model, `2` completion models. -/
theorem regroup_order_six :
    remainingModels 6 = 3 ∧ absorbedModels 6 = 1 ∧ regroupBExponent 6 = 7 := by
  exact ⟨rfl, rfl, rfl⟩

/-- Order seven: `7` defects, `0` absorbed models, `2` completion models. -/
theorem regroup_order_seven :
    remainingModels 7 = 2 ∧ absorbedModels 7 = 0 ∧ regroupBExponent 7 = 7 := by
  exact ⟨rfl, rfl, rfl⟩

/-- Order eight: exactly one model coordinate remains, so the two-model regroup
is unavailable. -/
theorem orderEight_oneModel : remainingModels 8 = 1 ∧ ¬ (2 ≤ remainingModels 8) := by
  refine ⟨rfl, by decide⟩

/-- Order nine: no model coordinate remains (pure defect shell). -/
theorem orderNine_noModel : remainingModels 9 = 0 ∧ ¬ (1 ≤ remainingModels 9) := by
  refine ⟨rfl, by decide⟩

/-- The defect and model counts always partition the nine coordinates. -/
theorem defects_add_models (j : ℕ) (hj : j ≤ 9) : j + remainingModels j = 9 := by
  unfold remainingModels; omega

end Gate1B.SafeAlgebra
