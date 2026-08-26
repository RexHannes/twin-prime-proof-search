/-
# NANC Gate 1A v9.5 — common vs edge-dependent weight firewall

The repository already distinguishes `CommonD2Data` from `EdgeDependentD2Data`
(`RequestProject/CenteredCRTRootNormalForm.lean`).  This file makes the
distinction *usable by the closure compiler*:

* a common packet may always be viewed as an edge-dependent one
  (`ofCommon`), and its coefficient is then literally constant in the edge;
* the converse coercion is **false**: there is an edge-dependent packet whose
  edge sums are reproduced by no common coefficient vector at all
  (`edgeDependent_not_common`);
* the only safe route for an edge-dependent packet is a **finite template
  decomposition** with an explicit nuclear cost
  (`finiteTemplate_norm_le`, `finiteTemplate_nuclear_cost`).

Consequently `EdgeDependentD2Data` may never be silently coerced into
`CommonD2Data`, and the `edgeDependentD2` census packet stays unrouted until a
finite-template certificate is supplied.
-/
import Mathlib
import RequestProject.CenteredCRTRootNormalForm

namespace TwinPrimeProject.NANC.Gate1A.V95

open Finset
open TwinPrimeProject.CenteredCRTRoot

/-! ## 1. Common data are edge-dependent data with constant coefficient -/

/-- Every common-coefficient packet is an edge-dependent packet. -/
def ofCommon (d : CommonD2Data) : EdgeDependentD2Data where
  Edge := d.Edge
  Pair := d.Pair
  Harm := d.Harm
  edgeFintype := d.edgeFintype
  pairFintype := d.pairFintype
  harmFintype := d.harmFintype
  coeff := fun _ a h => d.coeff a h
  phase := d.phase

/-- The coefficient of `ofCommon d` is literally independent of the edge. -/
theorem ofCommon_coeff_const (d : CommonD2Data) (e e' : d.Edge) (a : d.Pair) (h : d.Harm) :
    (ofCommon d).coeff e a h = (ofCommon d).coeff e' a h := rfl

/-! ## 2. The converse is false -/

/-- **Edge-dependent weight firewall.**  There is an edge-dependent packet
whose edge sums are reproduced by *no* common coefficient vector.  Hence
`EdgeDependentD2Data` must never be coerced into `CommonD2Data`. -/
theorem edgeDependent_not_common :
    ∃ coeff phase : Fin 2 → Fin 1 → Fin 1 → ℂ,
      ¬ ∃ c : Fin 1 → Fin 1 → ℂ, ∀ e : Fin 2,
        (∑ a, ∑ h, coeff e a h * phase e a h) = ∑ a, ∑ h, c a h * phase e a h := by
  refine ⟨fun e _ _ => (e : ℕ), fun _ _ _ => 1, ?_⟩
  rintro ⟨c, hc⟩
  have h0 := hc 0
  have h1 := hc 1
  simp at h0 h1
  rw [← h0] at h1
  norm_num at h1

/-! ## 3. The only safe route: finite templates with a nuclear cost -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- **Finite template decomposition.**  If an edge weight decomposes over a
finite template family, its norm is controlled by the template norms weighted
by the decomposition coefficients. -/
theorem finiteTemplate_norm_le {n : ℕ} (W : Fin n → E) (a : Fin n → ℂ) :
    ‖∑ j, a j • W j‖ ≤ ∑ j, ‖a j‖ * ‖W j‖ := by
  refine (norm_sum_le _ _).trans ?_
  exact Finset.sum_le_sum fun j _ => le_of_eq (norm_smul (a j) (W j))

/-- **Nuclear cost of a finite template decomposition.** -/
theorem finiteTemplate_nuclear_cost {n : ℕ} (W : Fin n → E) (a : Fin n → ℂ) (C : ℝ)
    (hC : ∀ j, ‖W j‖ ≤ C) :
    ‖∑ j, a j • W j‖ ≤ (∑ j, ‖a j‖) * C := by
  refine (finiteTemplate_norm_le W a).trans ?_
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hC j) (norm_nonneg _)

/-- A finite-template weight certificate for one packet. -/
structure FiniteTemplateCertificate (Edge : Type*) (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℂ E] where
  /-- Number of templates. -/
  n : ℕ
  /-- The templates. -/
  template : Fin n → E
  /-- The decomposition coefficients. -/
  coeff : Edge → Fin n → ℂ
  /-- The edge weights. -/
  weight : Edge → E
  /-- The decomposition identity. -/
  decomposition : ∀ e, weight e = ∑ j, coeff e j • template j
  /-- Uniform template bound. -/
  templateBound : ℝ
  templateBound_ok : ∀ j, ‖template j‖ ≤ templateBound
  /-- Nuclear cost. -/
  nuclearCost : ℝ
  nuclearCost_ok : ∀ e, (∑ j, ‖coeff e j‖) ≤ nuclearCost

namespace FiniteTemplateCertificate

variable {Edge : Type*} (T : FiniteTemplateCertificate Edge E)

/-- A finite-template certificate bounds every edge weight uniformly. -/
theorem weight_norm_le (e : Edge) (hC : 0 ≤ T.templateBound) :
    ‖T.weight e‖ ≤ T.nuclearCost * T.templateBound := by
  rw [T.decomposition e]
  refine (finiteTemplate_nuclear_cost T.template (T.coeff e) T.templateBound
    T.templateBound_ok).trans ?_
  exact mul_le_mul_of_nonneg_right (T.nuclearCost_ok e) hC

end FiniteTemplateCertificate

end TwinPrimeProject.NANC.Gate1A.V95
