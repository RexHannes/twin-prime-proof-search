import RequestProject.REAL1B_20261122.QuarterRough
import RequestProject.REAL1B_20261122.FMResidual
import RequestProject.REAL1B_20261122.WeightedDecomposition
import RequestProject.REAL1B_20261122.SourceBridge
import RequestProject.REAL1B_20261122.SieveInputs
import RequestProject.REAL1B_20261122.FMDirect
import RequestProject.REAL1B_20261122.FMOwners
import RequestProject.REAL1B_20261122.FMSemantics
import RequestProject.REAL1B_20261122.FMCompleteLabel

/-! Entry point for the REAL 1B proofs of 22–23 November 2026.
The Gold 4.66 endpoint is Direct.infinite_of_direct. The joint FM endpoints are Closing.infinite_of_joint_complement and
Closing.infinite_of_boxwise_complement inside REAL1B.FM.
The earlier FM residual and H2 reductions remain separately callable.
The scalar theorem below consumes both H2 source estimates on one unbounded
sequence of scales, with enough aggregate margin to produce a twin pair. -/
namespace REAL1B

/-- Combine the per-scale H2 lower bound with the dyadic infinitude criterion. -/
theorem infinite_of_h2_bounds (h₀ ρ e : ℝ) (N E₁ E₂ : ℝ → ℝ)
    (bounds : ∀ B : ℕ, ∃ X : ℝ, (B : ℝ) < X ∧
      (h₀ - e) * N X - E₁ X ≤
        mass X (fun n => mu n ^ 2 * roughMask n) - 2 * mass X (classMask 3) ∧
      mass X (fun n => mu n * roughMask n) + ρ * N X ≤ N X / 8 + E₂ X ∧
      0 < (h₀ + ρ - e - 1 / 8) * N X - E₁ X - E₂ X) :
    Set.Infinite {p : ℕ | p.Prime ∧ (p + 2).Prime} := by
  apply infinite_of_unbounded_mass
  intro B
  obtain ⟨X, hX, hu, hs, hm⟩ := bounds B
  refine ⟨X, hX, ?_⟩
  have lower := h2_lower X h₀ ρ e (N X) (E₁ X) (E₂ X) hu hs
  linarith

end REAL1B

#print axioms REAL1B.infinite_of_h2_bounds
