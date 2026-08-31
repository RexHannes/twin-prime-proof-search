import Gate1B.Gate1BLeaf4RowLocalStatus

/-!
# Gate 1B · physical row-local dictionary interface (append-only)

The current first residual of the research bank is the **physical row-local
dictionary**

```
ORIGINAL-E(q) / Z_E(q) PHYSICAL-ROWLOCAL-DICTIONARY45.
```

This module exposes that residual as an explicit *interface*.  Nothing here is
guessed:

* `E`, `ZE` and `kappa4` are **data fields** of the dictionary; no primitive
  definition and no numerical value is invented for them
  (`dictionary_data_not_pinned`, `kappa4_not_pinned`);
* the six named obligations `E_q_normalization_condition`,
  `ZE_q_normalization_condition`, `q1_physical_match`, `q2_physical_match`,
  `oddPrime_local_match`, `twoAdic_local_match`, together with
  `kappa4NormalizationHypothesis`, are `Prop`-valued fields, never axioms;
* `PhysicalRowLocalDictionaryValid` is **not proved**; it is refutable for an
  explicit non-physical witness (`physicalRowLocalDictionaryValid_not_unconditional`).

The two compilers at the end are **purely logical**.  They record the
dependency structure of the Leaf-4 and `h = 0` high-high research claims; every
analytic and source antecedent is an explicit hypothesis and none of them is
supplied anywhere in this repository.  Their conclusions are bookkeeping
packages, carrying no analytic content and, in particular, no Gate 1B closure
(`hZeroHighHigh_does_not_close_gate1B`).
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace Gate1BRowLocal

/-! ## 1. The dictionary as data -/

/-- The still-open physical row-local dictionary.  All fields are **data**: the
module never assigns them values. -/
structure PhysicalRowLocalDictionary where
  /-- The physical local factor `E(q)`.  Source data; not defined here. -/
  E : ℕ → ℂ
  /-- The physical normalising factor `Z_E(q)`.  Source data; not defined here. -/
  ZE : ℕ → ℂ
  /-- The combinatorial constant `kappa_4`.  Source data; not defined here. -/
  kappa4 : ℂ
  /-- The principal-character convention of the source. -/
  principalConvention : Prop
  /-- The non-principal-character convention of the source. -/
  nonprincipalConvention : Prop
  /-- The exceptional-character convention of the source. -/
  exceptionalConvention : Prop
  /-- The non-unit-residue convention of the source. -/
  nonunitConvention : Prop
  /-- Which projector owns the local packet. -/
  projectorOwnership : Prop

/-- The named source obligations attached to a dictionary.  Each is a
`Prop`-valued field: an obligation, never an axiom. -/
structure RowLocalObligations (D : PhysicalRowLocalDictionary) where
  /-- Normalisation condition on `E(q)`. -/
  E_q_normalization_condition : Prop
  /-- Normalisation condition on `Z_E(q)`. -/
  ZE_q_normalization_condition : Prop
  /-- The `q = 1` physical match. -/
  q1_physical_match : Prop
  /-- The `q = 2` physical match. -/
  q2_physical_match : Prop
  /-- The odd-prime local match. -/
  oddPrime_local_match : Prop
  /-- The `2`-adic local match. -/
  twoAdic_local_match : Prop
  /-- The `kappa_4` normalisation hypothesis (imported if a combinatorial
  convention is already banked elsewhere; otherwise an explicit hypothesis). -/
  kappa4NormalizationHypothesis : Prop

/-- **The dictionary source pin.**  Schematically: the formal `j = 4` local tree
packet, after the finite `2+2` / leaf reindexing, with dictionary `D`, equals
the historical physical TOPBAND local packet.

This proposition is the current first residual.  It is **never proved** in this
repository, and no field of `D` is assigned a value. -/
def PhysicalRowLocalDictionaryValid (D : PhysicalRowLocalDictionary)
    (O : RowLocalObligations D) : Prop :=
  O.E_q_normalization_condition ∧ O.ZE_q_normalization_condition ∧
    O.q1_physical_match ∧ O.q2_physical_match ∧
    O.oddPrime_local_match ∧ O.twoAdic_local_match ∧
    O.kappa4NormalizationHypothesis ∧
    D.principalConvention ∧ D.nonprincipalConvention ∧ D.exceptionalConvention ∧
    D.nonunitConvention ∧ D.projectorOwnership

/-- A deliberately **non-physical** witness dictionary, used only to show that
the validity proposition has content (it is refutable).  Its fields are zero /
`False` placeholders and carry no physical meaning whatsoever. -/
noncomputable def placeholderDictionary : PhysicalRowLocalDictionary where
  E := fun _ => 0
  ZE := fun _ => 0
  kappa4 := 0
  principalConvention := False
  nonprincipalConvention := False
  exceptionalConvention := False
  nonunitConvention := False
  projectorOwnership := False

/-- The matching placeholder obligations, all `False`. -/
def placeholderObligations : RowLocalObligations placeholderDictionary where
  E_q_normalization_condition := False
  ZE_q_normalization_condition := False
  q1_physical_match := False
  q2_physical_match := False
  oddPrime_local_match := False
  twoAdic_local_match := False
  kappa4NormalizationHypothesis := False

/-- **Firewall.**  `PhysicalRowLocalDictionaryValid` is *not* unconditionally
true: it fails for the placeholder witness.  Hence it can only ever be obtained
from genuine source data, which this repository does not contain. -/
theorem physicalRowLocalDictionaryValid_not_unconditional :
    ¬ PhysicalRowLocalDictionaryValid placeholderDictionary placeholderObligations := by
  rintro ⟨h, -⟩
  exact h

/-- **Firewall.**  `E` and `Z_E` are not pinned by this interface: two
dictionaries may carry different data. -/
theorem dictionary_data_not_pinned :
    ∃ D₁ D₂ : PhysicalRowLocalDictionary, D₁.E ≠ D₂.E ∧ D₁.ZE ≠ D₂.ZE := by
  refine ⟨placeholderDictionary,
    { placeholderDictionary with E := fun _ => 1, ZE := fun _ => 1 }, ?_, ?_⟩
  · intro h
    have := congrFun h 1
    simp [placeholderDictionary] at this
  · intro h
    have := congrFun h 1
    simp [placeholderDictionary] at this

/-- **Firewall.**  `kappa_4` is not pinned by this interface either. -/
theorem kappa4_not_pinned :
    ∃ D₁ D₂ : PhysicalRowLocalDictionary, D₁.kappa4 ≠ D₂.kappa4 := by
  refine ⟨placeholderDictionary, { placeholderDictionary with kappa4 := 1 }, ?_⟩
  simp [placeholderDictionary]

/-! ## 2. Conditional Leaf-4 compiler

Every analytic antecedent is an explicit hypothesis.  No hidden assumption. -/

/-- The explicit analytic antecedents of the Leaf-4 research claim.  Each is a
`Prop` field; none is inhabited here. -/
structure Leaf4AnalyticHypotheses where
  /-- `HZERO-J4-ALPHA4-BEZOUTROW-CENTREDGRAM45`. -/
  centredGram : Prop
  /-- `HZERO-J4-ALPHA4-BEZOUTROW-NONRESONANT45`. -/
  nonresonant : Prop
  /-- `HZERO-J4-ALPHA4-PRODUCTDIFF45` in its analytic reading (the arithmetic
  kernel alone is `gate1B_leaf4_productDifference`). -/
  productDifference : Prop
  /-- `HZERO-J4-ALPHA4-NONCOMMUTATIVE-MAJORTREE45`. -/
  noncommutativeMajorTree : Prop
  /-- The `j = 4` component of the full recursive broad-major tree owns the
  local packet (bare Leaf 5 does not). -/
  localTreeOwner : Prop

/-- The Leaf-4 closure conclusion, as a **logical/status package**: the
conjunction of the source pin with the four analytic antecedents and the owner
statement.  It contains no analytic object and asserts no new estimate. -/
def Leaf4ClosureConclusion (D : PhysicalRowLocalDictionary) (O : RowLocalObligations D)
    (H : Leaf4AnalyticHypotheses) : Prop :=
  PhysicalRowLocalDictionaryValid D O ∧ H.centredGram ∧ H.nonresonant ∧
    H.productDifference ∧ H.noncommutativeMajorTree ∧ H.localTreeOwner

/-- **Conditional Leaf-4 compiler.**  Purely logical: it records that the Leaf-4
package follows exactly from the physical dictionary together with the four
named analytic antecedents and the owner statement.  None of the hypotheses is
supplied anywhere. -/
theorem leaf4_closed_of_physical_dictionary
    {D : PhysicalRowLocalDictionary} {O : RowLocalObligations D}
    {H : Leaf4AnalyticHypotheses}
    (hDict : PhysicalRowLocalDictionaryValid D O)
    (hCentred : H.centredGram)
    (hNonresonant : H.nonresonant)
    (hProductDiff : H.productDifference)
    (hMajorTree : H.noncommutativeMajorTree)
    (hOwner : H.localTreeOwner) :
    Leaf4ClosureConclusion D O H :=
  ⟨hDict, hCentred, hNonresonant, hProductDiff, hMajorTree, hOwner⟩

/-- **Firewall.**  The Leaf-4 package genuinely requires the dictionary: it
implies the source pin. -/
theorem leaf4_closure_requires_dictionary
    {D : PhysicalRowLocalDictionary} {O : RowLocalObligations D}
    {H : Leaf4AnalyticHypotheses} (h : Leaf4ClosureConclusion D O H) :
    PhysicalRowLocalDictionaryValid D O := h.1

/-- **Firewall.**  The Leaf-4 package is not unconditionally available. -/
theorem leaf4_closure_not_unconditional :
    ∃ (D : PhysicalRowLocalDictionary) (O : RowLocalObligations D)
      (H : Leaf4AnalyticHypotheses), ¬ Leaf4ClosureConclusion D O H := by
  refine ⟨placeholderDictionary, placeholderObligations,
    ⟨False, False, False, False, False⟩, ?_⟩
  intro h
  exact physicalRowLocalDictionaryValid_not_unconditional h.1

/-! ## 3. Conditional `h = 0` high-high compiler -/

/-- The five explicit leaf antecedents of the `h = 0` high-high research claim.
None is supplied here; Leaves 1-3 in particular remain open. -/
structure HZeroLeafHypotheses where
  /-- Leaf 1 closure. OPEN. -/
  leaf1 : Prop
  /-- Leaf 2 closure. OPEN. -/
  leaf2 : Prop
  /-- Leaf 3 closure. OPEN. -/
  leaf3 : Prop
  /-- Leaf 4 closure (conditional on the physical dictionary). -/
  leaf4 : Prop
  /-- The Leaf-5 *local* model statement. -/
  leaf5Local : Prop

/-- The `h = 0` high-high conclusion, as a logical/status package. -/
def HZeroHighHighConclusion (L : HZeroLeafHypotheses) : Prop :=
  L.leaf1 ∧ L.leaf2 ∧ L.leaf3 ∧ L.leaf4 ∧ L.leaf5Local

/-- **Conditional `h = 0` compiler.**  Dependency structure only: all five leaf
hypotheses are explicit and none is supplied. -/
theorem hZeroHighHigh_closed_of_local_dictionary
    {L : HZeroLeafHypotheses}
    (hLeaf1 : L.leaf1) (hLeaf2 : L.leaf2) (hLeaf3 : L.leaf3)
    (hLeaf4 : L.leaf4) (hLeaf5Local : L.leaf5Local) :
    HZeroHighHighConclusion L :=
  ⟨hLeaf1, hLeaf2, hLeaf3, hLeaf4, hLeaf5Local⟩

/-- **Firewall.**  The `h = 0` high-high package does not imply Gate 1B closure:
there are instances where the package holds and an arbitrary further claim
(here `False`) fails. -/
theorem hZeroHighHigh_does_not_close_gate1B :
    ∃ (L : HZeroLeafHypotheses) (Gate1BClosure : Prop),
      HZeroHighHighConclusion L ∧ ¬ Gate1BClosure := by
  refine ⟨⟨True, True, True, True, True⟩, False, ⟨trivial, trivial, trivial, trivial, trivial⟩,
    not_false⟩

/-- **Firewall.**  The `h = 0` package does not promote Leaves 1-3: they are
inputs to it, not outputs of Leaf 4. -/
theorem hZeroHighHigh_requires_leaves123
    {L : HZeroLeafHypotheses} (h : HZeroHighHighConclusion L) :
    L.leaf1 ∧ L.leaf2 ∧ L.leaf3 :=
  ⟨h.1, h.2.1, h.2.2.1⟩

/-! ## 4. `q = 1` / `q = 2` research status (metadata only)

* `q = 1`: the formal zero-mode is present; the centred-defect analytic
  coefficient is negligible in the current research bank; the physical
  `E(1) / Z_E(1)` normalisation is a **source pin**.
* `q = 2`: the formal alternating major packet is present; the physical
  `E(2) / Z_E(2)` normalisation is a **source pin**.

No analytic asymptotic is formalised here. -/

/-- Status of the `q = 1` physical normalisation. -/
def q1NormalisationStatus : RowLocalStatus := RowLocalStatus.sourcePin

/-- Status of the `q = 2` physical normalisation. -/
def q2NormalisationStatus : RowLocalStatus := RowLocalStatus.sourcePin

/-- **Firewall.**  Both small-`q` normalisations are source pins, not proofs. -/
theorem smallQ_normalisations_are_source_pins :
    q1NormalisationStatus = RowLocalStatus.sourcePin ∧
      q2NormalisationStatus = RowLocalStatus.sourcePin ∧
      q1NormalisationStatus.isKernelProved = false ∧
      q2NormalisationStatus.isKernelProved = false := by decide

end Gate1BRowLocal
end CurrentProgramme
end TwinPrimeProject
