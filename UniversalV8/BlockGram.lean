/-
# UniversalV8 Module D — synthesis operator and block Gram algebra

The synthesis map of a finite family of bounded operators, its exact block Gram
identity through genuine operator adjoints, and the honest normalized synthesis
bound: *local packet bounds alone give nothing*; a synthesis congestion bound
(here: a Schur row bound on a scalar majorant of the cross terms) is what converts
local control into a global bound.

The retracted "Hilbert–Schmidt" identity
`‖∑ b_γ T_γ‖² = ∑ b_γ conj(b_γ') ⟪T_γ, T_γ'⟫` for arbitrary bounded operators is NOT
used and NOT stated; see `Countermodels.lean` for the guard against it.
-/
import UniversalV8.DiagonalBaseline
import UniversalV8.Synthesis

open Finset ContinuousLinearMap

namespace UniversalV8

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Synthesis of a finite family of packets: `S f = ∑_γ B_γ f_γ`. -/
def synthesis {Γ : Type*} [Fintype Γ] (B : Γ → (H →L[ℂ] K)) (f : Γ → H) : K :=
  ∑ γ, B γ (f γ)

/-- **(BLOCK-GRAM).**  The exact block form of `S* S`: the Gram inner product of two
synthesis vectors is the sum of the block entries `B_γ* B_γ'` evaluated on the data. -/
theorem blockGramIdentity {Γ : Type*} [Fintype Γ] (B : Γ → (H →L[ℂ] K)) (f g : Γ → H) :
    (inner ℂ (synthesis B f) (synthesis B g) : ℂ)
      = ∑ γ, ∑ γ', (inner ℂ (f γ) ((adjoint (B γ) ∘L B γ') (g γ')) : ℂ) := by
  unfold synthesis
  rw [sum_inner]
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [inner_sum]
  refine Finset.sum_congr rfl fun γ' _ => ?_
  simp [ContinuousLinearMap.adjoint_inner_right]

omit [CompleteSpace H] [CompleteSpace K] in
/-- The quadratic form of the synthesis map, in the literally type-correct real form. -/
theorem synthesis_norm_sq {Γ : Type*} [Fintype Γ] (B : Γ → (H →L[ℂ] K)) (f : Γ → H) :
    ‖synthesis B f‖ ^ 2 = ∑ γ, ∑ γ', (inner ℂ (B γ (f γ)) (B γ' (f γ')) : ℂ).re :=
  gram_expand _

omit [CompleteSpace H] [CompleteSpace K] in
/-- Crude triangle bound for the synthesis map. -/
theorem synthesis_norm_le_sum {Γ : Type*} [Fintype Γ] (B : Γ → (H →L[ℂ] K)) (f : Γ → H) :
    ‖synthesis B f‖ ≤ ∑ γ, ‖B γ‖ * ‖f γ‖ :=
  le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun γ _ => (B γ).le_opNorm (f γ))

/-- **Normalized synthesis bound.**  Local packet control (`‖B_γ* B_γ'‖ ≤ k γ γ'`) TOGETHER
WITH synthesis congestion control (symmetric nonnegative `k` with row sums `≤ η`) gives the
global bound `‖S f‖² ≤ η ∑_γ ‖f_γ‖²`.

The congestion hypothesis is not removable: see
`identical_packets_have_family_congestion` in `Countermodels.lean`. -/
theorem normalizedSynthesisBound {Γ : Type*} [Fintype Γ] (B : Γ → (H →L[ℂ] K))
    (f : Γ → H) (k : Γ → Γ → ℝ) (η : ℝ)
    (hk : ∀ γ γ', ‖adjoint (B γ) ∘L B γ'‖ ≤ k γ γ')
    (hknn : ∀ γ γ', 0 ≤ k γ γ') (hsymm : ∀ γ γ', k γ γ' = k γ' γ)
    (hrow : ∀ γ, ∑ γ', k γ γ' ≤ η) :
    ‖synthesis B f‖ ^ 2 ≤ η * ∑ γ, ‖f γ‖ ^ 2 := by
  have hterm : ∀ γ γ' : Γ, (inner ℂ (B γ (f γ)) (B γ' (f γ')) : ℂ).re
      ≤ k γ γ' * ‖f γ‖ * ‖f γ'‖ := by
    intro γ γ'
    have hadj : (inner ℂ (B γ (f γ)) (B γ' (f γ')) : ℂ)
        = inner ℂ (f γ) ((adjoint (B γ) ∘L B γ') (f γ')) := by
      simp [ContinuousLinearMap.adjoint_inner_right]
    calc (inner ℂ (B γ (f γ)) (B γ' (f γ')) : ℂ).re
        ≤ ‖(inner ℂ (f γ) ((adjoint (B γ) ∘L B γ') (f γ')) : ℂ)‖ := by
          rw [hadj]; exact Complex.re_le_norm _
      _ ≤ ‖f γ‖ * ‖(adjoint (B γ) ∘L B γ') (f γ')‖ := norm_inner_le_norm _ _
      _ ≤ ‖f γ‖ * (‖adjoint (B γ) ∘L B γ'‖ * ‖f γ'‖) :=
          mul_le_mul_of_nonneg_left ((adjoint (B γ) ∘L B γ').le_opNorm (f γ')) (norm_nonneg _)
      _ ≤ ‖f γ‖ * (k γ γ' * ‖f γ'‖) := by
          have := mul_le_mul_of_nonneg_right (hk γ γ') (norm_nonneg (f γ'))
          exact mul_le_mul_of_nonneg_left this (norm_nonneg _)
      _ = k γ γ' * ‖f γ‖ * ‖f γ'‖ := by ring
  calc ‖synthesis B f‖ ^ 2
      = ∑ γ, ∑ γ', (inner ℂ (B γ (f γ)) (B γ' (f γ')) : ℂ).re := synthesis_norm_sq B f
    _ ≤ ∑ γ, ∑ γ', k γ γ' * ‖f γ‖ * ‖f γ'‖ :=
        Finset.sum_le_sum fun γ _ => Finset.sum_le_sum fun γ' _ => hterm γ γ'
    _ ≤ η * ∑ γ, ‖f γ‖ ^ 2 := unweightedSchur k (fun γ => ‖f γ‖) η hknn hsymm hrow

end UniversalV8
