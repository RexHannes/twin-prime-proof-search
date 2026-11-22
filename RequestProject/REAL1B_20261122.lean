import RequestProject.REAL1B_20261122.QuarterRough
import RequestProject.REAL1B_20261122.FMResidual
import RequestProject.REAL1B_20261122.WeightedDecomposition
import RequestProject.REAL1B_20261122.SourceBridge
import RequestProject.REAL1B_20261122.SieveInputs
import RequestProject.REAL1B_20261122.FMClosing

/-! Aggregate entry point for the finite REAL 1B proof bank of 22 November 2026.
The fully specified endpoints are H2.infinite_of_paper_inputs and
FM.Source.infinite_of_source_residual. The earlier scalar H2 route below needs the two source estimates on the same unbounded
sequence of scales, with aggregate error small enough to leave a positive margin.
The Ford–Maynard and historical decomposition results are independent modules. -/

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
