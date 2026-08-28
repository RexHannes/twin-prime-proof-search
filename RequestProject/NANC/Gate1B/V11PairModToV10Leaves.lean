import RequestProject.NANC.Gate1B.V11PairModParentCompiler
import RequestProject.NANC.Gate1B.V10FullTypeIICompiler

/-!
# V11 · Gate 1B — the pair-modulus ⟶ V10 analytic-leaf bridge

## The exact V10 field types

`TwinPrimeProject.Gate1BV10.Gate1BClosureInputs` declares, for
`leafValue leafBudget : Gate1BLeaf → ℝ`:

    highPrimeLeaf : |leafValue .highPrime| ≤ leafBudget .highPrime
    sameQLeaf     : |leafValue .sameQ|     ≤ leafBudget .sameQ
    crossModLeaf  : |leafValue .crossMod|  ≤ leafBudget .crossMod
    H9Leaf        : |leafValue .h9|        ≤ leafBudget .h9

These four types are *exactly* real absolute-value bounds, so a pair-modulus
package that bounds a complex parent quantity attached to each leaf, together
with a dictionary identifying the leaf value with (the real part of) that
parent, does imply them.  **No type mismatch arises.**

`V11AnalyticLeafBundle` collects only those four fields.  A full
`Gate1BClosureInputs` is deliberately *not* constructed here: V10 also requires
`zeroFork`, `S1NormalizationPin`, `S2DeltaScalarPin`, the partition and the
budget, none of which a pair-modulus analytic package supplies.  The safe
compatibility statement is in `V11V10Compatibility.lean`.
-/

namespace TwinPrimeProject
namespace Gate1BV11

open Finset

/-- **The four V10 analytic leaves, and nothing else.** -/
structure V11AnalyticLeafBundle (leafValue leafBudget : Gate1BV10.Gate1BLeaf → ℝ) where
  /-- HIGHPRIME-MSWITCH. -/
  highPrimeLeaf : |leafValue .highPrime| ≤ leafBudget .highPrime
  /-- SAMEQ. -/
  sameQLeaf : |leafValue .sameQ| ≤ leafBudget .sameQ
  /-- CROSSMOD. -/
  crossModLeaf : |leafValue .crossMod| ≤ leafBudget .crossMod
  /-- H9. -/
  H9Leaf : |leafValue .h9| ≤ leafBudget .h9

/-- Generic bridge: parent bounds plus a dictionary and a budget pin give the
four leaves. -/
theorem v10AnalyticLeaves_of_parentBounds
    (leafValue leafBudget : Gate1BV10.Gate1BLeaf → ℝ) (X : ℝ) (s : ℚ)
    (parent : Gate1BV10.Gate1BLeaf → ℂ)
    (hb : ∀ l, ShiftedQuotientParentBound (parent l) X s)
    (hdict : ∀ l, leafValue l = (parent l).re)
    (hpin : ∀ l, X ^ (1 - (s : ℝ)) ≤ leafBudget l) :
    V11AnalyticLeafBundle leafValue leafBudget := by
  have key : ∀ l, |leafValue l| ≤ leafBudget l := by
    intro l
    rw [hdict l]
    exact le_trans (le_trans (Complex.abs_re_le_norm (parent l)) (hb l)) (hpin l)
  exact ⟨key _, key _, key _, key _⟩

variable {c : ℕ} [NeZero c] {Θ U V Γ₁ Γ₂ : Type} [Fintype Θ] [Fintype U] [Fintype V]
  [Fintype Γ₁] [Fintype Γ₂] {X : ℝ}

/-- **PAIRMOD ⟶ V10 FOUR LEAVES.**

From a supplied pair-modulus analytic package, an assignment of each V10
analytic leaf to one of the two pair-modulus parents, the dictionary and the
budget pin, the four V10 leaf fields follow — with their exact V10 types.

The package is uninhabited in this project, so nothing is asserted
unconditionally. -/
theorem pairModPackage_to_v10AnalyticLeaves
    (H : FMPerronPairModSourceMultiplierInput c Θ U V Γ₁ Γ₂ X)
    (leafValue leafBudget : Gate1BV10.Gate1BLeaf → ℝ)
    (assign : Gate1BV10.Gate1BLeaf → Fin 2)
    (hdict : ∀ l, leafValue l = (H.parentValue (assign l)).re)
    (hpin : ∀ l, X ^ (1 - (qkLowerEndpointSaving : ℝ)) ≤ leafBudget l) :
    V11AnalyticLeafBundle leafValue leafBudget := by
  refine v10AnalyticLeaves_of_parentBounds leafValue leafBudget X qkLowerEndpointSaving
    (fun l => H.parentValue (assign l)) ?_ hdict hpin
  intro l
  exact pairMod_to_qk56FullCovariance H (assign l)

/-! ### Guard -/

/-- **Guard.**  The bundle is not automatic: leaf values can exceed their
budgets. -/
theorem leafBundle_not_automatic :
    ¬ Nonempty (V11AnalyticLeafBundle (fun _ => 2) (fun _ => 1)) := by
  rintro ⟨h⟩
  have := h.highPrimeLeaf
  norm_num at this

end Gate1BV11
end TwinPrimeProject
