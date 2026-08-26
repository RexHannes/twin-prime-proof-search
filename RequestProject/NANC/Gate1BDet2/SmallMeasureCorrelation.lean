import Mathlib

/-!
# Gate 1B / determinant-2 bank, Module 7 (Phase B): small-measure correlation

A purely measure-theoretic deterministic lemma, with no number theory in it:
a correlation integral of two essentially bounded functions over a set `E` of
finite measure is bounded by `μ(E) · ‖A‖_∞ · ‖B‖_∞`.

This is the only deterministic implication used by the major-arc argument; the
major-arc theorem itself is **not** formalised.
-/

namespace TwinPrimeProject
namespace Gate1BDet2

open MeasureTheory Complex

variable {X : Type*} [MeasurableSpace X]

/-- **Small-measure correlation lemma.**  If `‖A x‖ ≤ MA` and `‖B x‖ ≤ MB` on a
set `E` of finite measure, then

  `‖∫_E A · conj B‖ ≤ μ(E) · MA · MB`. -/
theorem norm_setIntegral_mul_conj_le {mu : Measure X} {A B : X → ℂ} {E : Set X}
    {MA MB : ℝ} (hE : mu E < ⊤)
    (hA : ∀ x ∈ E, ‖A x‖ ≤ MA) (hB : ∀ x ∈ E, ‖B x‖ ≤ MB) :
    ‖∫ x in E, A x * (starRingEnd ℂ) (B x) ∂mu‖ ≤ mu.real E * (MA * MB) := by
  have hpt : ∀ x ∈ E, ‖A x * (starRingEnd ℂ) (B x)‖ ≤ MA * MB := by
    intro x hx
    have hA' := hA x hx
    have hB' := hB x hx
    have hMA : 0 ≤ MA := le_trans (norm_nonneg _) hA'
    calc ‖A x * (starRingEnd ℂ) (B x)‖ = ‖A x‖ * ‖B x‖ := by
          rw [norm_mul, RCLike.norm_conj]
      _ ≤ MA * MB := by
          exact mul_le_mul hA' hB' (norm_nonneg _) hMA
  have := MeasureTheory.norm_setIntegral_le_of_norm_le_const hE hpt
  linarith [this]

/-- The same bound, with the measure written as an `ENNReal.toReal`. -/
theorem norm_setIntegral_mul_conj_le' {mu : Measure X} {A B : X → ℂ} {E : Set X}
    {MA MB : ℝ} (hE : mu E < ⊤)
    (hA : ∀ x ∈ E, ‖A x‖ ≤ MA) (hB : ∀ x ∈ E, ‖B x‖ ≤ MB) :
    ‖∫ x in E, A x * (starRingEnd ℂ) (B x) ∂mu‖ ≤ (mu E).toReal * (MA * MB) :=
  norm_setIntegral_mul_conj_le hE hA hB

end Gate1BDet2
end TwinPrimeProject
