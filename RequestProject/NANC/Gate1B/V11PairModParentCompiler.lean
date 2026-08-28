import RequestProject.NANC.Gate1B.V11FMPerronPairModInterface

/-!
# V11 · Gate 1B — pair-modulus ⟶ analytic parents

The repository contains **no** predicate named `ShiftedQuotientParentBound` or
`QK56FullCovarianceBound` (searched: absent).  They are therefore introduced
here as **new project-local v11 predicates**, with the honest content
"the parent quantity beats the scale by the stated fixed-power saving".

The two implications below are deterministic: they consume the (uninhabited)
pair-modulus analytic package and produce the parent bounds.  Nothing claims
that the analytic input exists.
-/

namespace TwinPrimeProject
namespace Gate1BV11

open Finset

/-- **v11 project-local predicate.**  The shifted-quotient parent beats the
scale `X` by the fixed-power saving `s`. -/
def ShiftedQuotientParentBound (Vp : ℂ) (X : ℝ) (s : ℚ) : Prop :=
  ‖Vp‖ ≤ X ^ (1 - (s : ℝ))

/-- **v11 project-local predicate.**  The full QK5/6 covariance family — both
parents — beats the scale `X` by the fixed-power saving `s`. -/
def QK56FullCovarianceBound (Vp : Fin 2 → ℂ) (X : ℝ) (s : ℚ) : Prop :=
  ∀ k, ‖Vp k‖ ≤ X ^ (1 - (s : ℝ))

variable {c : ℕ} [NeZero c] {Θ U V Γ₁ Γ₂ : Type} [Fintype Θ] [Fintype U] [Fintype V]
  [Fintype Γ₁] [Fintype Γ₂] {X : ℝ}

/-- **PAIRMOD ⟶ SHIFTED QUOTIENT PARENT.**  Conditional compiler. -/
theorem pairMod_to_shiftedQuotientParent
    (H : FMPerronPairModSourceMultiplierInput c Θ U V Γ₁ Γ₂ X) :
    ShiftedQuotientParentBound (H.parentValue 0) X shiftedFixedMultiplierSaving :=
  le_trans (H.norm_parentValue_le 0) H.shiftedBudget

/-- **PAIRMOD ⟶ QK5/6 FULL COVARIANCE PARENT.**  Conditional compiler. -/
theorem pairMod_to_qk56FullCovariance
    (H : FMPerronPairModSourceMultiplierInput c Θ U V Γ₁ Γ₂ X) :
    QK56FullCovarianceBound H.parentValue X qkLowerEndpointSaving :=
  fun k => le_trans (H.norm_parentValue_le k) H.qkBudget

/-! ### Guards -/

/-- **Guard.**  The parent predicates are not vacuous. -/
theorem shiftedQuotientParentBound_not_automatic :
    ¬ ShiftedQuotientParentBound 2 1 shiftedFixedMultiplierSaving := by
  unfold ShiftedQuotientParentBound
  simp

/-- **Guard.**  Nor is the covariance predicate. -/
theorem qk56FullCovarianceBound_not_automatic :
    ¬ QK56FullCovarianceBound (fun _ => 2) 1 qkLowerEndpointSaving := by
  unfold QK56FullCovarianceBound
  intro h
  have := h 0
  simp at this

end Gate1BV11
end TwinPrimeProject
