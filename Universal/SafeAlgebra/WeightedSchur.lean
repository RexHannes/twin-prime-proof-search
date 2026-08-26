/-
# Universal safe algebra — Schur congestion criteria (re-export)

Proved in `UniversalV8/Synthesis.lean`: the unweighted Schur bound, the weighted Schur
bound (symmetric kernel; the symmetry/column condition is load-bearing, see
`weightedSchur_needs_symmetry`), and the operator corollary via a scalar majorant
(`UniversalV8.normalizedSynthesisBound`).
-/
import UniversalV8.BlockGram

namespace Universal.SafeAlgebra

export UniversalV8 (unweightedSchur weightedSchur weightedSchur_needs_symmetry)

/-- Operator-block corollary under an explicit scalar majorant `‖B_i* B_j‖ ≤ k i j`:
this is exactly `UniversalV8.normalizedSynthesisBound`. -/
theorem weightedBlockSchur {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    {Γ : Type*} [Fintype Γ] (B : Γ → (H →L[ℂ] K)) (f : Γ → H) (k : Γ → Γ → ℝ) (η : ℝ)
    (hk : ∀ γ γ', ‖ContinuousLinearMap.adjoint (B γ) ∘L B γ'‖ ≤ k γ γ')
    (hknn : ∀ γ γ', 0 ≤ k γ γ') (hsymm : ∀ γ γ', k γ γ' = k γ' γ)
    (hrow : ∀ γ, ∑ γ', k γ γ' ≤ η) :
    ‖UniversalV8.synthesis B f‖ ^ 2 ≤ η * ∑ γ, ‖f γ‖ ^ 2 :=
  UniversalV8.normalizedSynthesisBound B f k η hk hknn hsymm hrow

end Universal.SafeAlgebra
