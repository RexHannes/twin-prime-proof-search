/-
# Gate 1B v8.2 — κ₄ normalisation (finite combinatorics only)

Exact finite combinatorics: `C(9,2) = 36`, `C(9,4) = 126`, and over ℚ their
ratio is `2/7`.  The labelled fixed-subset multiplicity is `1`, i.e. a *fixed*
subset occurs exactly once among the labelled subsets.

No source application is made beyond these counts.
-/
import Mathlib

namespace Gate1B.SafeAlgebra

open Finset

/-- `C(9,2) = 36`. -/
theorem chooseNineTwo : Nat.choose 9 2 = 36 := by rfl

/-- `C(9,4) = 126`. -/
theorem chooseNineFour : Nat.choose 9 4 = 126 := by rfl

/-- **`κ₄/κ₂ = 2/7`** in exact rational arithmetic. -/
theorem kappa4_over_kappa2_eq_two_sevenths :
    ((Nat.choose 9 2 : ℚ)) / (Nat.choose 9 4 : ℚ) = 2 / 7 := by
  rw [chooseNineTwo, chooseNineFour]
  norm_num

/-- The number of four-element subsets of `Fin 9` really is `C(9,4)`. -/
theorem card_powersetCard_four :
    ((Finset.univ : Finset (Fin 9)).powersetCard 4).card = 126 := by
  rw [Finset.card_powersetCard]
  simp [chooseNineFour]

/-- The number of two-element subsets of `Fin 9` really is `C(9,2)`. -/
theorem card_powersetCard_two :
    ((Finset.univ : Finset (Fin 9)).powersetCard 2).card = 36 := by
  rw [Finset.card_powersetCard]
  simp [chooseNineTwo]

/-- **Labelled fixed-subset multiplicity is one**: a fixed labelled subset
occurs exactly once in the powerset. -/
theorem labelledFixedSubset_multiplicity_one (J : Finset (Fin 9)) :
    ((Finset.univ : Finset (Fin 9)).powerset.filter (fun K => K = J)).card = 1 := by
  classical
  have : (Finset.univ : Finset (Fin 9)).powerset.filter (fun K => K = J) = {J} := by
    ext K
    simp
  rw [this]
  simp

end Gate1B.SafeAlgebra
