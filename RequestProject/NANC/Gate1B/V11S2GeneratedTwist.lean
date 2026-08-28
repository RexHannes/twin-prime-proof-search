import RequestProject.NANC.Gate1B.V11GeneratedExpression
import Universal.SafeAlgebra.FiniteAbel

/-!
# V11 · Gate 1B — the S2 generated-twist interface

The source-side finite transform

    defectTransform s δ w = ∑_{n ∈ s} δ(n) · w(n)

is a finite sum: it is defined, and finite partial-summation is *reused* from
the existing bank (`UniversalV8.DiscreteAbel`, re-exported by
`Universal.SafeAlgebra.FiniteAbel`) rather than re-proved.

The **cancellation interfaces are uninhabited**.  They are the genuine analytic
inputs.  In particular:

* `S2PureMellinCancellation` — cancellation against the pure Mellin twists;
* `S2PrimeExtremaTwistCancellation` — cancellation against the `P±` twists,
  relative to a `PrimeExtremaRealisation` this project does not supply;
* `S2PerronGeneratedCancellation` — cancellation against *every* generated
  weight, which is what the grammar certificate would actually need.

The second is **not** inferred from the first: see
`V11PrimeExtremaTwistFirewall.lean`, and the transform-level separation theorem
`pureMellin_transform_does_not_control_extremaTransform` below.

No Siegel–Walfisz, and no quantitative source estimate, is assumed or named as
an axiom anywhere.  Mathlib's Dirichlet-prime-AP infrastructure is qualitative
and does not supply the arbitrary-log source estimate required here.
-/

namespace TwinPrimeProject
namespace Gate1BV11

open Finset

/-- **The source-side finite defect transform.** -/
noncomputable def defectTransform (s : Finset ℕ) (delta weight : ℕ → ℂ) : ℂ :=
  ∑ n ∈ s, delta n * weight n

/-- The transform is linear in the weight. -/
theorem defectTransform_add_weight (s : Finset ℕ) (delta w₁ w₂ : ℕ → ℂ) :
    defectTransform s delta (fun n => w₁ n + w₂ n)
      = defectTransform s delta w₁ + defectTransform s delta w₂ := by
  simp [defectTransform, mul_add, Finset.sum_add_distrib]

/-- The transform is linear in the defect. -/
theorem defectTransform_smul_defect (s : Finset ℕ) (c : ℂ) (delta w : ℕ → ℂ) :
    defectTransform s (fun n => c * delta n) w = c * defectTransform s delta w := by
  simp [defectTransform, Finset.mul_sum, mul_assoc]

/-- Trivial ℓ¹ bound (no cancellation used). -/
theorem norm_defectTransform_le (s : Finset ℕ) (delta w : ℕ → ℂ) (C : ℝ)
    (hw : ∀ n ∈ s, ‖w n‖ ≤ C) :
    ‖defectTransform s delta w‖ ≤ (∑ n ∈ s, ‖delta n‖) * C :=
  norm_finiteSum_le_l1Cost s delta w C hw

/-- **Finite summation by parts for the defect transform**, obtained by reusing
the existing finite Abel bank — nothing is re-proved. -/
theorem defectTransform_backendDualNorm (m n : ℕ) (hmn : m < n) (delta w : ℕ → ℂ) (Δ : ℝ)
    (hP : ∀ t, m ≤ t → t < n → ‖UniversalV8.partialSum m delta t‖ ≤ Δ) :
    ‖defectTransform (Finset.Ico m n) delta w‖
      ≤ Δ * (‖w (n - 1)‖ + UniversalV8.variation m (n - 1) w) :=
  Universal.SafeAlgebra.backendDualNorm_discreteBV m n hmn delta w Δ hP

/-! ## The uninhabited cancellation interfaces -/

/-- **S2 pure-Mellin cancellation** — an external analytic input.  No
inhabitant. -/
structure S2PureMellinCancellation (s : Finset ℕ) (delta : ℕ → ℂ) (bound : ℝ) where
  /-- Cancellation against every pure Mellin twist. -/
  mellinCancellation :
    ∀ t : ℝ, ‖defectTransform s delta (semAtom (.mellinTwist t))‖ ≤ bound

/-- **S2 prime-extrema twist cancellation** — a *strictly separate* external
analytic input, relative to a `PrimeExtremaRealisation` that this project does
not supply.  No inhabitant. -/
structure S2PrimeExtremaTwistCancellation (E : PrimeExtremaRealisation)
    (s : Finset ℕ) (delta : ℕ → ℂ) (bound : ℝ) where
  /-- Cancellation against the two-parameter `P±` twist family. -/
  extremaCancellation :
    ∀ a b : PrimeExtremaAtom,
      ‖defectTransform s delta
        (fun n => semPrimeExtremaAtom E a n * semPrimeExtremaAtom E b n)‖ ≤ bound

/-- **S2 generated-twist cancellation** — the full analytic input the grammar
certificate would need: cancellation against *every* admissible generated
weight of bounded cost, including the prime-coordinate ones.  No inhabitant. -/
structure S2PerronGeneratedCancellation (E : PrimeExtremaRealisation)
    (s : Finset ℕ) (delta : ℕ → ℂ) (D bound : ℝ) where
  /-- The pure-Mellin subinterface. -/
  pureMellin : S2PureMellinCancellation s delta bound
  /-- The prime-extrema subinterface — supplied separately, never inferred. -/
  primeExtrema : S2PrimeExtremaTwistCancellation E s delta bound
  /-- Cancellation against every admissible generated weight of cost ≤ 1. -/
  generatedCancellation :
    ∀ e : GenExpr, e.Admissible → cost D e ≤ 1 →
      ‖defectTransform s delta (semExpr e)‖ ≤ bound

/-- The full interface does contain the pure-Mellin one — the safe direction. -/
theorem s2Generated_gives_pureMellin {E : PrimeExtremaRealisation} {s : Finset ℕ}
    {delta : ℕ → ℂ} {D bound : ℝ} (H : S2PerronGeneratedCancellation E s delta D bound) :
    S2PureMellinCancellation s delta bound := H.pureMellin

/-- …and the prime-extrema one, again only because it is a supplied field. -/
theorem s2Generated_gives_primeExtrema {E : PrimeExtremaRealisation} {s : Finset ℕ}
    {delta : ℕ → ℂ} {D bound : ℝ} (H : S2PerronGeneratedCancellation E s delta D bound) :
    S2PrimeExtremaTwistCancellation E s delta bound := H.primeExtrema

/-! ## Transform-level separation -/

/-- **The two transforms are genuinely different functionals.**

There is a finite defect and a pair of unimodular weight families such that the
transform against the first vanishes identically while the transform against the
second has full ℓ¹ mass.  Hence a bound for one family carries no information
about the other, at the level of the transform itself. -/
theorem pureMellin_transform_does_not_control_extremaTransform :
    ∃ (s : Finset ℕ) (delta w₁ w₂ : ℕ → ℂ),
      (∀ n ∈ s, ‖w₁ n‖ = 1) ∧ (∀ n ∈ s, ‖w₂ n‖ = 1) ∧
      defectTransform s delta w₁ = 0 ∧
      ‖defectTransform s delta w₂‖ = 2 := by
  refine ⟨{0, 1}, fun _ => 1, fun n => if n = 0 then 1 else -1, fun _ => 1,
    ?_, ?_, ?_, ?_⟩
  · intro n _; by_cases h : n = 0 <;> simp [h]
  · intro n _; simp
  · simp [defectTransform]
  · norm_num [defectTransform]

end Gate1BV11
end TwinPrimeProject
