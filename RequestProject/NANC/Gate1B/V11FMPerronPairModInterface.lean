import RequestProject.NANC.Gate1B.V11SourceMultiplierStructure
import RequestProject.NANC.Gate1B.V11S2GeneratedTwist
import RequestProject.NANC.Gate1B.V11PairModCapacity

/-!
# V11 · Gate 1B — the generated-grammar pair-modulus analytic interface

`FMPerronPairModSourceMultiplierInput` is the **uninhabited** structure holding
everything a pair-modulus analytic package would have to supply.

The key field is `movingFamilyCoherence`: the genuine analytic
source-multiplier estimate for the *moving* family.  It is **not** derived from
`fixedBackend`, and it is **not** derived from ℓ² source energy; the firewall
`fixedMultiplierBounds_do_not_control_movingFamily` and
`rankOne_does_not_give_movingFamily_saving` show that no such derivation exists.

There is **no global inhabitant**: the structure requires a
`PrimeExtremaRealisation` (absent from the repository) together with
`S2PerronGeneratedCancellation` relative to it.

Non-circularity: no field of this structure is the target proposition.  The
targets are `ShiftedQuotientParentBound` / `QK56FullCovarianceBound`, defined in
`V11PairModParentCompiler.lean`; the budget fields below constrain the *bounds*,
never the parent values.
-/

namespace TwinPrimeProject
namespace Gate1BV11

open Finset Gate1B.SafeAlgebra

/-- **The pair-modulus analytic package.**  Uninhabited in this project. -/
structure FMPerronPairModSourceMultiplierInput
    (c : ℕ) [NeZero c] (Θ U V Γ₁ Γ₂ : Type) [Fintype Θ] [Fintype U] [Fintype V]
    [Fintype Γ₁] [Fintype Γ₂] (X : ℝ) where
  /-- **actual source multiplier data.** -/
  source : PairModSourceData c Θ U V
  /-- The `u`-side index dictionary into the coefficient grammar. -/
  uIndex : U → ℕ
  /-- The `v`-side index dictionary into the coefficient grammar. -/
  vIndex : V → ℕ
  /-- The coefficient slots seen by the grammar: `inl t` is the `α(t,·)` slot,
  `inr t` the `β(t,·)` slot. -/
  coeffSlot : Θ ⊕ Θ → ℕ → ℂ
  /-- **generated certificate for all coefficient slots.** -/
  grammar : FMPerronGrammarCertificate coeffSlot
  /-- Pair-modulus dictionary, `α`-side. -/
  alphaDictionary : ∀ t i, source.alpha t i = coeffSlot (.inl t) (uIndex i)
  /-- Pair-modulus dictionary, `β`-side. -/
  betaDictionary : ∀ t j, source.beta t j = coeffSlot (.inr t) (vIndex j)
  /-- **source-rank-one / pushforward certificate.** -/
  rankOne : SourceRankOne Θ Γ₁ Γ₂ source.A
  /-- The realisation of the prime-extrema coordinates.  ABSENT from this
  repository — this is what makes the package uninhabited here. -/
  primeExtrema : PrimeExtremaRealisation
  /-- The source window on which the generated twists are tested. -/
  sourceWindow : Finset ℕ
  /-- The source defect. -/
  sourceDefect : ℕ → ℂ
  /-- The uniform divisor bound used by the grammar cost. -/
  divisorBound : ℝ
  /-- The generated-twist cancellation bound. -/
  twistBound : ℝ
  /-- **S2 generated-twist cancellation**, including the `P±` coordinates. -/
  generatedTwistCancellation :
    S2PerronGeneratedCancellation primeExtrema sourceWindow sourceDefect divisorBound twistBound
  /-- The fixed-multiplier backend bound. -/
  fixedBackendBound : ℝ
  /-- **fixed-backend bound** — the fixed-`Θ` estimate.  Not sufficient on its
  own; see the moving-family firewall. -/
  fixedBackend : ∀ t, ‖source.fixedMultiplierValue t‖ ≤ fixedBackendBound
  /-- The moving-family bound. -/
  movingFamilyBound : ℝ
  /-- **moving-family coherence** — THE genuine analytic source-multiplier
  estimate.  Supplied, never derived from `fixedBackend` or from ℓ² energy. -/
  movingFamilyCoherence : ‖source.pairModFamilyValue‖ ≤ movingFamilyBound
  /-- The two parent values: `0` = shifted quotient parent, `1` = QK5/6
  covariance parent. -/
  parentValue : Fin 2 → ℂ
  /-- **diagonal router** — the diagonal remainder of each parent. -/
  diagonalPart : Fin 2 → ℂ
  /-- **shared-`g` router** — the shared-`g` remainder of each parent. -/
  sharedGPart : Fin 2 → ℂ
  /-- **packet cost.** -/
  packetCost : ℝ
  /-- The packet cost is a cost. -/
  packetCost_nonneg : 0 ≤ packetCost
  /-- The exact routing identity for each parent. -/
  router : ∀ k, parentValue k
    = (packetCost : ℂ) * source.pairModFamilyValue + diagonalPart k + sharedGPart k
  /-- The diagonal budget. -/
  diagonalBound : ℝ
  /-- The diagonal router respects its budget. -/
  diagonalRouterBound : ∀ k, ‖diagonalPart k‖ ≤ diagonalBound
  /-- The shared-`g` budget. -/
  sharedGBound : ℝ
  /-- The shared-`g` router respects its budget. -/
  sharedGRouterBound : ∀ k, ‖sharedGPart k‖ ≤ sharedGBound
  /-- The assembled budget clears the shifted fixed-multiplier saving `1/32`. -/
  shiftedBudget : packetCost * movingFamilyBound + diagonalBound + sharedGBound
    ≤ X ^ (1 - (shiftedFixedMultiplierSaving : ℝ))
  /-- The assembled budget clears the QK lower-endpoint saving `1/108`. -/
  qkBudget : packetCost * movingFamilyBound + diagonalBound + sharedGBound
    ≤ X ^ (1 - (qkLowerEndpointSaving : ℝ))

namespace FMPerronPairModSourceMultiplierInput

variable {c : ℕ} [NeZero c] {Θ U V Γ₁ Γ₂ : Type} [Fintype Θ] [Fintype U] [Fintype V]
  [Fintype Γ₁] [Fintype Γ₂] {X : ℝ}

/-- Every coefficient slot certified by the package is generated. -/
theorem coeffSlot_generated (H : FMPerronPairModSourceMultiplierInput c Θ U V Γ₁ Γ₂ X)
    (s : Θ ⊕ Θ) : FMPerronGenerated (H.coeffSlot s) :=
  H.grammar.generated s

/-- The assembled bound on each parent value, before any budget is spent. -/
theorem norm_parentValue_le (H : FMPerronPairModSourceMultiplierInput c Θ U V Γ₁ Γ₂ X)
    (k : Fin 2) :
    ‖H.parentValue k‖
      ≤ H.packetCost * H.movingFamilyBound + H.diagonalBound + H.sharedGBound := by
  have hcoh : H.packetCost * ‖H.source.pairModFamilyValue‖
      ≤ H.packetCost * H.movingFamilyBound :=
    mul_le_mul_of_nonneg_left H.movingFamilyCoherence H.packetCost_nonneg
  have hmul : ‖(H.packetCost : ℂ) * H.source.pairModFamilyValue‖
      = H.packetCost * ‖H.source.pairModFamilyValue‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg H.packetCost_nonneg]
  calc ‖H.parentValue k‖
      = ‖(H.packetCost : ℂ) * H.source.pairModFamilyValue + H.diagonalPart k
          + H.sharedGPart k‖ := by rw [H.router k]
    _ ≤ ‖(H.packetCost : ℂ) * H.source.pairModFamilyValue + H.diagonalPart k‖
          + ‖H.sharedGPart k‖ := norm_add_le _ _
    _ ≤ (‖(H.packetCost : ℂ) * H.source.pairModFamilyValue‖ + ‖H.diagonalPart k‖)
          + ‖H.sharedGPart k‖ := by
        exact add_le_add (norm_add_le _ _) (le_refl ‖H.sharedGPart k‖)
    _ ≤ (H.packetCost * H.movingFamilyBound + H.diagonalBound) + H.sharedGBound := by
        refine add_le_add (add_le_add ?_ (H.diagonalRouterBound k)) (H.sharedGRouterBound k)
        rw [hmul]; exact hcoh

end FMPerronPairModSourceMultiplierInput

end Gate1BV11
end TwinPrimeProject
