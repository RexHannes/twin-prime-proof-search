/-
# NANC Gate 1A v9.4 — machine-visible retraction of the direct `R^{-1}`
# weighted-family promotion

The v9.2/v9.3 route contained a step of the shape

    "the family rows have small pairwise codegree, therefore the coherent
     family energy is at most `(#family)^{-1}` times the natural energy".

That step is **RETRACTED as a closure step**.  Small pairwise codegree — even
in its strongest possible form, exact pairwise orthogonality — does *not*
produce a `(#family)^{-1}` saving; it produces no saving at all.  A saving of
that shape needs a genuine cancellation input (a participation/normalization
certificate), never a codegree count alone.

This file banks the retraction as a finite countermodel, so that nothing
downstream can quietly re-use the promotion.

Nothing analytic is asserted here.
-/
import Mathlib

namespace TwinPrimeProject.NANC.Gate1A.V94

open Finset

/-! ## 1. Status of the retracted step -/

/-- Bank status of a formerly-proposed closure step. -/
inductive StepStatus
  /-- Retained as a proved finite statement. -/
  | Proved
  /-- Retracted as a closure step: refuted by a finite countermodel. -/
  | RetractedAsClosureStep
  /-- Still an open analytic interface. -/
  | AnalyticInterfaceOpen
  deriving DecidableEq, Repr

/-- The direct `R^{-1}` weighted-family promotion is retracted. -/
def directR1WeightedFamilyPromotion : StepStatus := .RetractedAsClosureStep

theorem directR1WeightedFamilyPromotion_retracted :
    directR1WeightedFamilyPromotion = StepStatus.RetractedAsClosureStep := rfl

theorem directR1WeightedFamilyPromotion_not_proved :
    directR1WeightedFamilyPromotion ≠ StepStatus.Proved := by decide

/-! ## 2. The finite countermodel

Two rows in a two-dimensional real coordinate space, exactly orthogonal (the
strongest conceivable "small pairwise codegree"), with equal weights.  The
coherent energy equals the natural energy, so the claimed `(#family)^{-1}`
factor is false already for a family of size two. -/

/-- The countermodel family: `famRow i` is the `i`-th standard basis row. -/
def famRow : Fin 2 → Fin 2 → ℝ := fun i j => if i = j then 1 else 0

/-- The rows are pairwise exactly orthogonal: codegree is as small as possible. -/
theorem famRow_pairwise_orthogonal (i j : Fin 2) (hij : i ≠ j) :
    ∑ k, famRow i k * famRow j k = 0 := by
  fin_cases i <;> fin_cases j <;> simp_all [famRow]

/-- Coherent (family-summed) energy of the countermodel. -/
theorem famRow_coherent_energy : ∑ k, (∑ i, famRow i k) ^ 2 = 2 := by
  simp [famRow]

/-- Natural (row-by-row) energy of the countermodel. -/
theorem famRow_natural_energy : ∑ i, ∑ k, (famRow i k) ^ 2 = 2 := by
  simp [famRow]

/-- **Retraction countermodel.**  Exact pairwise orthogonality of the family
rows does *not* imply the `(#family)^{-1}` family-energy promotion. -/
theorem directR1_promotion_countermodel :
    ¬ (∑ k, (∑ i, famRow i k) ^ 2 ≤
        (1 / (Fintype.card (Fin 2) : ℝ)) * ∑ i, ∑ k, (famRow i k) ^ 2) := by
  rw [famRow_coherent_energy, famRow_natural_energy]
  norm_num

/-- The same countermodel, phrased as: no constant strictly below `1` can be
inserted in front of the natural energy on the strength of orthogonality
alone. -/
theorem directR1_promotion_countermodel_general (c : ℝ) (hc : c < 1) :
    ¬ (∑ k, (∑ i, famRow i k) ^ 2 ≤ c * ∑ i, ∑ k, (famRow i k) ^ 2) := by
  rw [famRow_coherent_energy, famRow_natural_energy]
  intro h
  nlinarith

/-! ## 3. Firewall note

`directR1_promotion_countermodel` is the reason the v9.4 route replaces the
family promotion by a *participation* certificate: the saving must come from a
proved lower bound on the mass carried by the participating rows
(`PrimeParticipationCertificate`), not from a codegree count.  The weights in
the actual source additionally vary with the family index, which only makes the
situation strictly worse than this equal-weight countermodel. -/

end TwinPrimeProject.NANC.Gate1A.V94
