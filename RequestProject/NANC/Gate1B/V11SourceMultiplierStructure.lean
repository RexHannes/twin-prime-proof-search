import RequestProject.NANC.Gate1B.V11MultiplierCounterguards
import Gate1B.SafeAlgebra.D12ResidueFactor

/-!
# V11 · Gate 1B — source rank-one multiplier structure

The banked rank-one residue pushforward

    A(Θ) = R₁(u₁(Θ)) · conj (R₂(u₂(Θ)))

is abstracted here.  The **exact finite ℓ¹ / ℓ² factorisations are reused** from
the existing v8.2 module `Gate1B.SafeAlgebra.D12ResidueFactor`
(`d12Pushforward_l1_factor`, `d12Pushforward_l2_factor`); they are not
re-proved.

**No analytic moving-multiplier saving is inferred.**  The closing theorem of
this file shows the opposite: a rank-one multiplier family can lose the full
`√K` factor of the moving-family firewall, so rank-one structure is *not* a
substitute for family coherence.
-/

namespace TwinPrimeProject
namespace Gate1BV11

open Finset Gate1B.SafeAlgebra

/-- **The rank-one source multiplier hypothesis**, along a supplied bijective
pushforward `e : Θ ≃ Γ₁ × Γ₂`. -/
structure SourceRankOne (Θ Γ₁ Γ₂ : Type*) [Fintype Θ] [Fintype Γ₁] [Fintype Γ₂]
    (A : Θ → ℂ) where
  /-- The pushforward bijection. -/
  push : Θ ≃ Γ₁ × Γ₂
  /-- The first residue factor. -/
  R₁ : Γ₁ → ℂ
  /-- The second residue factor. -/
  R₂ : Γ₂ → ℂ
  /-- The rank-one identity. -/
  factor : ∀ t, A t = R₁ (push t).1 * (starRingEnd ℂ) (R₂ (push t).2)

/-- **ℓ¹ factorisation of a rank-one source multiplier** — reuses the banked
D₁₂ pushforward identity. -/
theorem SourceRankOne.l1_factor {Θ Γ₁ Γ₂ : Type*} [Fintype Θ] [Fintype Γ₁] [Fintype Γ₂]
    {A : Θ → ℂ} (h : SourceRankOne Θ Γ₁ Γ₂ A) :
    ∑ t, ‖A t‖ = (∑ x, ‖h.R₁ x‖) * ∑ y, ‖h.R₂ y‖ :=
  d12Pushforward_l1_factor h.push h.R₁ h.R₂ A h.factor

/-- **ℓ² factorisation of a rank-one source multiplier** — reuses the banked
D₁₂ pushforward identity. -/
theorem SourceRankOne.l2_factor {Θ Γ₁ Γ₂ : Type*} [Fintype Θ] [Fintype Γ₁] [Fintype Γ₂]
    {A : Θ → ℂ} (h : SourceRankOne Θ Γ₁ Γ₂ A) :
    ∑ t, ‖A t‖ ^ 2 = (∑ x, ‖h.R₁ x‖ ^ 2) * ∑ y, ‖h.R₂ y‖ ^ 2 :=
  d12Pushforward_l2_factor h.push h.R₁ h.R₂ A h.factor

/-- The constant multiplier of the aligned family is rank-one, with the trivial
one-point second factor. -/
noncomputable def alignedRankOne (K : ℕ) :
    SourceRankOne (Fin K) (Fin K) (Fin 1) (alignedFamily K).A where
  push := (Equiv.prodUnique (Fin K) (Fin 1)).symm
  R₁ := fun t => ((Real.sqrt K)⁻¹ : ℝ)
  R₂ := fun _ => 1
  factor := by intro t; simp [alignedFamily]

/-- **NO ANALYTIC SAVING FROM RANK-ONE STRUCTURE.**  The aligned family is
rank-one, has fixed-multiplier bound `1` and ℓ² multiplier energy `≤ 1`, and
still loses the full `√K`.  Rank-one algebra is bookkeeping, not cancellation. -/
theorem rankOne_does_not_give_movingFamily_saving (K : ℕ) (hK : 0 < K) :
    (∀ t, ‖(alignedFamily K).pairing t‖ ≤ 1) ∧
    (∑ t, ‖(alignedFamily K).A t‖ ^ 2 ≤ 1) ∧
    Nonempty (SourceRankOne (Fin K) (Fin K) (Fin 1) (alignedFamily K).A) ∧
    ‖(alignedFamily K).value‖ = Real.sqrt K :=
  ⟨alignedFamily_fixed_bound K, alignedFamily_l2_energy K hK, ⟨alignedRankOne K⟩,
    alignedFamily_value_norm K hK⟩

end Gate1BV11
end TwinPrimeProject
