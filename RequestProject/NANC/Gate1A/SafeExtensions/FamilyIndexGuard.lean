/-
# NANC Gate 1A v9 — family-index firewall (finite countermodel)

A coherent sum over `N` family indices can have squared norm `N²` even though
every individual slice has norm `1`.  Hence **fixing one exact family index is
not lossless**: the family index carries a genuine factor, and any step that
"selects" one index must pay for it explicitly.
-/
import Mathlib

namespace TwinPrimeProject.NANC.Gate1A.V9

open Finset

/-- **Family-index countermodel.**  For every `N`, there is a family of `N`
unit-norm slices whose coherent sum has squared norm `N²`, while the sum of the
individual squared norms is only `N`. -/
theorem familyIndex_counterexample (N : ℕ) :
    ∃ c : Fin N → ℂ, (∀ i, ‖c i‖ = 1) ∧
      ‖∑ i, c i‖ ^ 2 = (N : ℝ) ^ 2 ∧ ∑ i, ‖c i‖ ^ 2 = (N : ℝ) := by
  refine ⟨fun _ => 1, fun _ => by simp, ?_, ?_⟩
  · simp
  · simp

/-- **The firewall statement.**  Selecting a single family index is not
lossless: with the family above, one slice has squared norm `1` while the
coherent family sum has squared norm `N²`. -/
theorem familyIndex_selection_not_lossless (N : ℕ) (hN : 2 ≤ N) :
    ∃ c : Fin N → ℂ, ∃ i : Fin N,
      ‖c i‖ ^ 2 = 1 ∧ ‖∑ j, c j‖ ^ 2 = (N : ℝ) ^ 2 ∧ (1 : ℝ) < ‖∑ j, c j‖ ^ 2 := by
  have hN' : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  refine ⟨fun _ => 1, ⟨0, by omega⟩, by simp, by simp, ?_⟩
  have : ‖∑ _j : Fin N, (1 : ℂ)‖ ^ 2 = (N : ℝ) ^ 2 := by simp
  rw [this]
  nlinarith

end TwinPrimeProject.NANC.Gate1A.V9
