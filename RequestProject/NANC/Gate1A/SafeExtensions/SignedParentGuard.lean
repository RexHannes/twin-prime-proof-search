/-
# NANC Gate 1A v9 — signed-parent firewall (finite countermodel)

The coefficient-blind quantity `∑ |σ_i|²|K_i|²` carries **no** information about
the cancellation in the signed parent `|∑ σ_i K_i|`: two data sets can share the
blind energy while one parent vanishes and the other does not.

The point is not that ℓ² is useless; the point is to block the automatic
promotion of a child kernel estimate to a signed parent bound.
-/
import Mathlib

namespace TwinPrimeProject.NANC.Gate1A.V9

open Finset

/-- **Signed parent ≠ child energy.**  Two `Fin 2` data sets with identical
coefficient-blind energies, one with vanishing signed parent and one with
signed parent of modulus `2`. -/
theorem signedParent_child_not_parent :
    ∃ sigma K K' : Fin 2 → ℂ,
      (∑ i, ‖sigma i‖ ^ 2 * ‖K i‖ ^ 2) = (∑ i, ‖sigma i‖ ^ 2 * ‖K' i‖ ^ 2) ∧
      ‖∑ i, sigma i * K i‖ = 0 ∧ ‖∑ i, sigma i * K' i‖ = 2 := by
  refine ⟨fun _ => 1, fun i => if i = 0 then (1 : ℂ) else -1, fun _ => 1, ?_, ?_, ?_⟩
  · simp [Fin.sum_univ_two]
    norm_num
  · simp [Fin.sum_univ_two]
  · simp

end TwinPrimeProject.NANC.Gate1A.V9
