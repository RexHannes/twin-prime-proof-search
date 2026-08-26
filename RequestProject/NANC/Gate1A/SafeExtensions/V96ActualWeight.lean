/-
# NANC Gate 1A v9.6 — the actual `W_D` / `W_{D,e}` determination

This file answers the first concrete all-`m` obstruction **from the actual
source definitions**, not from a reconstructed narrative.

The authoritative source object is

    TwinPrimeProject.CenteredCRTRoot.EdgeDependentD2Data
    (RequestProject/CenteredCRTRootNormalForm.lean, `structure EdgeDependentD2Data`)

whose coefficient field has the literal type

    coeff : Edge → Pair → Harm → ℂ

with **no** further field constraining the edge dependence: no common-weight
equation, no finite-template equation, no smooth parameter `Φ(t/D, θ_e)`, and
no compactness or smoothness hypothesis of any kind.  The source therefore
supplies an *arbitrary* edge-dependent weight, and this is recorded here as

    actualWeightVerdict = ActualWeightVerdict.arbitraryEdgeDependent

The determination is backed by three machine-checked facts.

* `edgeData_coeff` — every function `Edge → Pair → Harm → ℂ` whatsoever is the
  coefficient field of an actual `EdgeDependentD2Data`; the source constrains
  nothing.
* `template_count_ge_of_linearIndependent` — if the edge weights are linearly
  independent then any finite common-template decomposition needs at least as
  many templates as there are edges.
* `deltaEdgeData_no_small_template` — an actual `EdgeDependentD2Data` whose edge
  weights are the orthogonal delta directions: any
  `FiniteTemplateCertificate` for its weights has at least `#Edge` templates.

Consequently the common-template / `E♯` route is **not** available for
arbitrary edge-dependent `W_{D,e}` on functional-analytic grounds alone:

    EDGEDEPENDENT_D2_NOT_ESharp_ADMISSIBLE.

Nothing here weakens or reopens the v9–v9.5 bank; `ofCommon` and
`edgeDependent_not_common` of `V95WeightFirewall` are reused, not restated.
-/
import Mathlib
import RequestProject.CenteredCRTRootNormalForm
import RequestProject.NANC.Gate1A.SafeExtensions.V95WeightFirewall

namespace TwinPrimeProject.NANC.Gate1A.V96

open Finset
open TwinPrimeProject.CenteredCRTRoot
open TwinPrimeProject.NANC.Gate1A.V95

/-! ## 1. The verdict -/

/-- The five admissible answers to the `W_D` / `W_{D,e}` question. -/
inductive ActualWeightVerdict
  /-- The source proves `W_{D,e} = W_D`. -/
  | common
  /-- The source proves an exact finite-template formula. -/
  | finiteTemplate
  /-- The source gives a smooth fixed-dimensional parametric family. -/
  | structuredEdgeDependent
  /-- The source allows an arbitrary independent weight for each edge. -/
  | arbitraryEdgeDependent
  /-- The source defines no weight at all. -/
  | notDefinedInSource
  deriving DecidableEq, Repr

/-- **The v9.6 determination.**  Read off from
`TwinPrimeProject.CenteredCRTRoot.EdgeDependentD2Data`. -/
def actualWeightVerdict : ActualWeightVerdict := .arbitraryEdgeDependent

/-- The exact source path of the weight determination. -/
def actualWeightSourcePath : String :=
  "RequestProject/CenteredCRTRootNormalForm.lean :: " ++
    "TwinPrimeProject.CenteredCRTRoot.EdgeDependentD2Data.coeff"

/-- The verdict is not the common-weight one; the common branch of the
instructions is therefore not taken. -/
theorem actualWeightVerdict_ne_common : actualWeightVerdict ≠ .common := by decide

/-! ## 2. The source constrains nothing -/

/-- Any prescribed coefficient and phase family gives an actual
`EdgeDependentD2Data`. -/
abbrev edgeData (Edge Pair Harm : Type) [Fintype Edge] [Fintype Pair] [Fintype Harm]
    (c ph : Edge → Pair → Harm → ℂ) : EdgeDependentD2Data where
  Edge := Edge
  Pair := Pair
  Harm := Harm
  coeff := c
  phase := ph

/-- **The source imposes no relation between the edges.**  Every function
whatsoever occurs as the coefficient field of an actual source datum, so no
common-weight or finite-template equation can be derived from the source. -/
theorem edgeData_coeff (Edge Pair Harm : Type) [Fintype Edge] [Fintype Pair] [Fintype Harm]
    (c ph : Edge → Pair → Harm → ℂ) : (edgeData Edge Pair Harm c ph).coeff = c := rfl

/-- The weight vector carried by one edge of an actual source datum. -/
def edgeWeight (d : EdgeDependentD2Data) (e : d.Edge) : d.Pair × d.Harm → ℂ :=
  fun p => d.coeff e p.1 p.2

/-! ## 3. Rank obstruction to a finite common-template reduction -/

/-- **Template count is bounded below by the rank of the weight family.**  If
the edge weights are linearly independent and each decomposes over `n` common
templates, then there are at least as many templates as edges. -/
theorem template_count_ge_of_linearIndependent {M : Type*} [AddCommGroup M] [Module ℂ M]
    {Edge : Type*} [Fintype Edge] {n : ℕ} (W : Edge → M) (hW : LinearIndependent ℂ W)
    (T : Fin n → M) (a : Edge → Fin n → ℂ) (hdec : ∀ e, W e = ∑ j, a e j • T j) :
    Fintype.card Edge ≤ n := by
  classical
  set S : Submodule ℂ M := Submodule.span ℂ (Set.range T) with hS
  have hmem : ∀ e, W e ∈ S := by
    intro e
    rw [hdec e]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  haveI : Module.Finite ℂ S := Module.Finite.span_of_finite ℂ (Set.finite_range T)
  have hfin : Module.finrank ℂ S ≤ n := by
    refine (finrank_span_le_card (R := ℂ) (Set.range T)).trans ?_
    rw [Set.toFinset_range]
    exact Finset.card_image_le.trans (by simp)
  have hindep : LinearIndependent ℂ (fun e => (⟨W e, hmem e⟩ : S)) :=
    LinearIndependent.of_comp S.subtype hW
  exact hindep.fintype_card_le_finrank.trans hfin

/-! ## 4. An actual edge-dependent datum with orthogonal edge directions -/

/-- An actual `EdgeDependentD2Data` whose `N` edges carry the `N` orthogonal
delta weight directions. -/
abbrev deltaEdgeData (N : ℕ) : EdgeDependentD2Data :=
  edgeData (Fin N) (Fin N) (Fin 1) (fun e a _ => if e = a then 1 else 0) (fun _ _ _ => 1)

/-- The edge weights of `deltaEdgeData N` are linearly independent. -/
theorem deltaEdgeData_linearIndependent (N : ℕ) :
    LinearIndependent ℂ (fun e : (deltaEdgeData N).Edge => edgeWeight (deltaEdgeData N) e) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have h := congrFun hg (i, 0)
  simp only [edgeWeight, deltaEdgeData, edgeData, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, Pi.zero_apply, mul_ite, mul_one, mul_zero] at h
  simpa using h

/-- **`EDGEDEPENDENT_D2_NOT_ESharp_ADMISSIBLE`.**  For the actual source datum
`deltaEdgeData N`, every finite common-template decomposition of the edge
weights uses at least `N` templates.  No `X^{o(1)}` common-template reduction
therefore follows from functional analysis alone. -/
theorem deltaEdgeData_no_small_template (N n : ℕ)
    (T : Fin n → ((deltaEdgeData N).Pair × (deltaEdgeData N).Harm → ℂ))
    (a : (deltaEdgeData N).Edge → Fin n → ℂ)
    (hdec : ∀ e, edgeWeight (deltaEdgeData N) e = ∑ j, a e j • T j) :
    N ≤ n := by
  have h := template_count_ge_of_linearIndependent
    (fun e : (deltaEdgeData N).Edge => edgeWeight (deltaEdgeData N) e)
    (deltaEdgeData_linearIndependent N) T a hdec
  simpa using h

/-- The same statement phrased through the **existing**
`FiniteTemplateCertificate` type: a certificate for the delta weights has at
least `N` templates. -/
theorem finiteTemplateCertificate_delta_card
    (N : ℕ)
    (C : FiniteTemplateCertificate (Fin N) ((deltaEdgeData N).Pair × (deltaEdgeData N).Harm → ℂ))
    (hC : ∀ e : Fin N, C.weight e = edgeWeight (deltaEdgeData N) e) :
    N ≤ C.n := by
  refine deltaEdgeData_no_small_template N C.n C.template C.coeff ?_
  intro e
  rw [← hC e]
  exact C.decomposition e

/-! ## 5. The permitted positive direction -/

/-- A **common** weight always has a one-template certificate: the
common-weight branch of the instructions is inhabited, and it is the only
branch that is. -/
def commonFiniteTemplate {Edge E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (W : E) (B : ℝ) (hB : ‖W‖ ≤ B) : FiniteTemplateCertificate Edge E where
  n := 1
  template := fun _ => W
  coeff := fun _ _ => 1
  weight := fun _ => W
  decomposition := by intro e; simp
  templateBound := B
  templateBound_ok := fun _ => hB
  nuclearCost := 1
  nuclearCost_ok := by intro e; simp

/-- The common-weight certificate really has a single template and unit nuclear
cost. -/
theorem commonFiniteTemplate_cost {Edge E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (W : E) (B : ℝ) (hB : ‖W‖ ≤ B) :
    (commonFiniteTemplate (Edge := Edge) W B hB).n = 1 ∧
      (commonFiniteTemplate (Edge := Edge) W B hB).nuclearCost = 1 :=
  ⟨rfl, rfl⟩

end TwinPrimeProject.NANC.Gate1A.V96
