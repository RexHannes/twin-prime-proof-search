/-
# Gate 1B v13 — QK5/6 conditional closure from the v13 same-`q` / cross-`q` leaves

**Status: CONDITIONAL.  Implications only; every analytic leaf stays
UNINHABITED.**

The v13 bank splits the QK5/6 parent into three deterministic pieces:

    parent = sameQGramDiag + sameQGramOff + crossQ,

using the proved decomposition `sameQGram_split`.  Each piece is then routed to
an interface:

* the diagonal piece to `SameQDiagonalResidueEnergyInput` (UNINHABITED) plus a
  principal-kernel pin;
* the off-diagonal piece to `ModularHyperbolaDiscrepancyInput` (UNINHABITED)
  plus an `ℓ¹` pin on the coefficient sequence;
* the cross-`q` piece to `CrossQThetaSourceMassCertificate` (UNINHABITED) plus
  the routing hypothesis that the cross-`q` value is dominated by the `ℓ²` mass
  of its Θ-source.

The resulting theorem `qk56_full_covariance_of_v13_inputs` produces the
project-local predicate `TwinPrimeProject.Gate1BV11.QK56FullCovarianceBound`,
and `v13_to_v10AnalyticLeaves` produces the four V10 analytic leaves.  Nothing
here inhabits any analytic interface, so **no closure is claimed**; V10/V11 are
untouched.
-/
import Gate1B.SafeExtensions.SameQDiagonalRouter
import Gate1B.SafeExtensions.ModularHyperbolaDiscrepancy
import Gate1B.SafeExtensions.CrossQThetaSpread
import RequestProject.NANC.Gate1B.V11PairModToV10Leaves

namespace Gate1B.SafeExtensions

open Finset Gate1B.SafeAlgebra TwinPrimeProject.Gate1BV11

variable {G : Type*} [Fintype G] [DecidableEq G] [CommGroup G]
variable {Ch : Type*} [Fintype Ch] [DecidableEq Ch] [CommGroup Ch]
variable {Θ : Type*} [Fintype Θ]

/-- **Literal QK5/6 source dictionary (routing data, not an analytic input).**

It records that the character system has principal character `1`, that each
parent value is the same-`q` Gram of its own coefficient sequence plus a
cross-`q` remainder, and that the cross-`q` remainder is dominated by the `ℓ²`
mass of its Θ-source.  These are *dictionary* hypotheses: they carry no
estimate. -/
structure QK56V13SourceDictionary (S : MulCharSystem G Ch) (Vp Vcross : Fin 2 → ℂ)
    (c : Fin 2 → Ch → ℂ) (u v : Fin 2 → G → ℂ) (A : Fin 2 → Θ → ℂ) : Prop where
  /-- The principal character is trivial on `G`. -/
  principal : ∀ g : G, S.chi (1 : Ch) g = 1
  /-- The parent value splits into its same-`q` Gram and a cross-`q` remainder. -/
  parent_split : ∀ k, Vp k = sameQGram (c k) (S.productKernel (u k) (v k)) + Vcross k
  /-- The cross-`q` remainder is dominated by the `ℓ²` mass of its Θ-source. -/
  cross_le : ∀ k, ‖Vcross k‖ ≤ crossL2 (A k)

/-- **QK5/6 CONDITIONAL CLOSURE.**

From the literal source dictionary, the two UNINHABITED same-`q` analytic
inputs, the UNINHABITED cross-`q` spread certificate, the deterministic
principal-kernel and `ℓ¹` pins and the final budget pin, the project-local
QK5/6 parent bound follows.  No analytic input is constructed. -/
theorem qk56_full_covariance_of_v13_inputs (S : MulCharSystem G Ch)
    (Vp Vcross : Fin 2 → ℂ) (c : Fin 2 → Ch → ℂ) (u v : Fin 2 → G → ℂ) (A : Fin 2 → Θ → ℂ)
    (E Delta B L1sq rho L1cross X : ℝ) (s : ℚ)
    (hdictionary : QK56V13SourceDictionary S Vp Vcross c u v A)
    (hdiag : ∀ k, SameQDiagonalResidueEnergyInput (c k) E)
    (hker : ∀ k, ‖S.productKernel (u k) (v k) 1‖ ≤ B) (hB0 : 0 ≤ B)
    (hhyp : ∀ k, ModularHyperbolaDiscrepancyInput (u k) (v k) Delta) (hDelta : 0 ≤ Delta)
    (hl1 : ∀ k, (∑ x : Ch, ‖c k x‖) ^ 2 ≤ L1sq)
    (hspread : ∀ k, CrossQThetaSourceMassCertificate (A k) rho) (hrho : 0 ≤ rho)
    (hcrossL1 : ∀ k, crossL1 (A k) ≤ L1cross)
    (hpin : (1 / (Fintype.card Ch : ℝ) ^ 2) * (B * E)
              + (1 / (Fintype.card Ch : ℝ) ^ 2) * (((Fintype.card G : ℝ) * Delta) * L1sq)
              + rho * L1cross ≤ X ^ (1 - (s : ℝ))) :
    QK56FullCovarianceBound Vp X s := by
  intro k
  have hsplit : Vp k
      = sameQGramDiag (c k) (S.productKernel (u k) (v k))
        + sameQGramOff (c k) (S.productKernel (u k) (v k)) + Vcross k := by
    rw [hdictionary.parent_split k, sameQGram_split]
  have hD : ‖sameQGramDiag (c k) (S.productKernel (u k) (v k))‖
      ≤ (1 / (Fintype.card Ch : ℝ) ^ 2) * (B * E) :=
    sameQGramDiag_bound_of_input (c k) (S.productKernel (u k) (v k)) E B (hker k) hB0 (hdiag k)
  have hO : ‖sameQGramOff (c k) (S.productKernel (u k) (v k))‖
      ≤ (1 / (Fintype.card Ch : ℝ) ^ 2)
          * (((Fintype.card G : ℝ) * Delta) * (∑ x : Ch, ‖c k x‖) ^ 2) :=
    sameQGramOff_bound_of_discrepancy S hdictionary.principal (u k) (v k) Delta hDelta
      (hhyp k) (c k)
  have hOmono : (1 / (Fintype.card Ch : ℝ) ^ 2)
        * (((Fintype.card G : ℝ) * Delta) * (∑ x : Ch, ‖c k x‖) ^ 2)
      ≤ (1 / (Fintype.card Ch : ℝ) ^ 2) * (((Fintype.card G : ℝ) * Delta) * L1sq) := by
    have hgd : (0 : ℝ) ≤ (Fintype.card G : ℝ) * Delta := by positivity
    have := mul_le_mul_of_nonneg_left (hl1 k) hgd
    exact mul_le_mul_of_nonneg_left this (by positivity)
  have hC : ‖Vcross k‖ ≤ rho * L1cross := by
    refine le_trans (hdictionary.cross_le k) (le_trans (hspread k).spread ?_)
    exact mul_le_mul_of_nonneg_left (hcrossL1 k) hrho
  calc ‖Vp k‖
      ≤ ‖sameQGramDiag (c k) (S.productKernel (u k) (v k))
          + sameQGramOff (c k) (S.productKernel (u k) (v k))‖ + ‖Vcross k‖ := by
        rw [hsplit]; exact norm_add_le _ _
    _ ≤ (‖sameQGramDiag (c k) (S.productKernel (u k) (v k))‖
          + ‖sameQGramOff (c k) (S.productKernel (u k) (v k))‖) + ‖Vcross k‖ := by
        have := norm_add_le (sameQGramDiag (c k) (S.productKernel (u k) (v k)))
          (sameQGramOff (c k) (S.productKernel (u k) (v k)))
        linarith
    _ ≤ ((1 / (Fintype.card Ch : ℝ) ^ 2) * (B * E)
          + (1 / (Fintype.card Ch : ℝ) ^ 2) * (((Fintype.card G : ℝ) * Delta) * L1sq))
          + rho * L1cross := by
        exact add_le_add (add_le_add hD (le_trans hO hOmono)) hC
    _ ≤ X ^ (1 - (s : ℝ)) := hpin

/-- **V13 ⟹ V10 FOUR ANALYTIC LEAVES.**  Each V10 leaf value is identified with
the real part of a v13-routed parent; the four V10 leaf fields follow with their
exact V10 types.  V10 is untouched and no leaf is fabricated. -/
theorem v13_to_v10AnalyticLeaves
    (parent : TwinPrimeProject.Gate1BV10.Gate1BLeaf → ℂ)
    (leafValue leafBudget : TwinPrimeProject.Gate1BV10.Gate1BLeaf → ℝ) (X : ℝ) (s : ℚ)
    (hb : ∀ l, ‖parent l‖ ≤ X ^ (1 - (s : ℝ)))
    (hdict : ∀ l, leafValue l = (parent l).re)
    (hbudget : ∀ l, X ^ (1 - (s : ℝ)) ≤ leafBudget l) :
    V11AnalyticLeafBundle leafValue leafBudget :=
  v10AnalyticLeaves_of_parentBounds leafValue leafBudget X s parent hb hdict hbudget

/-! ### Guards -/

/-- **Guard.**  The QK5/6 conclusion is not automatic. -/
theorem qk56_v13_conclusion_not_automatic :
    ¬ QK56FullCovarianceBound (fun _ => 2) 1 qkLowerEndpointSaving :=
  qk56FullCovarianceBound_not_automatic

/-- **Guard.**  The V10 leaf bundle is not automatic. -/
theorem v13LeafBundle_not_automatic :
    ¬ Nonempty (V11AnalyticLeafBundle (fun _ => 2) (fun _ => 1)) :=
  leafBundle_not_automatic

end Gate1B.SafeExtensions
