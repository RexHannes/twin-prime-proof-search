/-
NANC V5.1 — EDGE-BY-EDGE DEPENDENCY PROVENANCE.

The parent V5 controlling bank records a Ford–Maynard dependency table as a
single object.  V5.1 refines it: every *edge* carries its own provenance, and
no edge is upgraded as a side effect of another edge.

    KEY RULE (CG-15):
        one verified dependency edge  ≠  entire dependency table verified.

Since no readable Ford–Maynard source is present in this repository (see
`fordMaynardSourceTextPresent`), the strongest label any edge gets in this run is
`assumedSourceReading`, and the edge

    Lemma 7.20  ←  comparison condition (b.2)

is additionally flagged as the one the inherited audit claims to be
source-supported.  The remaining edges

    Proposition 7.19  ←  (w), Type I, Type II
    Lemma 7.21        ←  Type I
    Theorem 8.2 final N₂ step  ←  bounded-class pointwise estimate

are recorded as uninspected / inherited claims and are NOT upgraded.
-/
import Mathlib
import RequestProject.NANC.V5_1.FordMaynardSourceAudit

namespace NANC.V5_1

/-- How well supported a single dependency edge is. -/
inductive EdgeProvenance where
  /-- The edge was read verbatim in a source available to the auditor. -/
  | sourceVerified
  /-- The edge is asserted by the source but its passage was not inspected. -/
  | uninspectedSourceDependency
  /-- The edge is inherited from an earlier audit's metadata only. -/
  | inheritedAuditClaim
  deriving DecidableEq, Repr

/-- One edge of the Ford–Maynard dependency table. -/
structure DependencyEdge where
  /-- The dependent statement. -/
  target : String
  /-- The statement it depends on. -/
  premise : String
  /-- What the inherited audit claims about this edge. -/
  claimedProvenance : EdgeProvenance
  /-- What *this* bank is willing to assert about the edge. -/
  bankProvenance : V51Provenance
  /-- Whether the passage was inspected in this repository. -/
  inspection : SourceInspection

namespace DependencyEdge

/-- No dependency edge is ever Lean evidence. -/
def IsLeanEvidence (e : DependencyEdge) : Bool :=
  V51Provenance.IsLeanEvidence e.bankProvenance

/-- Upgrade exactly one named edge to `sourceInspectedNotProved`.  Used to show
that upgrading one edge leaves the others untouched. -/
def upgrade (name : String) (e : DependencyEdge) : DependencyEdge :=
  if e.target = name then
    { e with bankProvenance := V51Provenance.sourceInspectedNotProved,
             inspection := SourceInspection.inspectedVerbatim }
  else e

/-- Upgrading the edge named `name` does not touch any edge with another target. -/
theorem upgrade_other {name : String} {e : DependencyEdge} (h : e.target ≠ name) :
    upgrade name e = e := by
  simp [upgrade, h]

/-- Upgrading an edge never makes it Lean evidence. -/
theorem upgrade_not_leanEvidence {name : String} {e : DependencyEdge}
    (h : IsLeanEvidence e = false) : IsLeanEvidence (upgrade name e) = false := by
  unfold upgrade
  split
  · rfl
  · exact h

end DependencyEdge

/-! ### The refined table -/

/-- The inspected/source-supported edge claimed by the inherited audit. -/
def edgeLemma720 : DependencyEdge where
  target := "Lemma 7.20"
  premise := "comparison condition (b.2)"
  claimedProvenance := EdgeProvenance.sourceVerified
  bankProvenance := V51Provenance.assumedSourceReading
  inspection := SourceInspection.notInspected

def edgeProposition719 : DependencyEdge where
  target := "Proposition 7.19"
  premise := "(w), Type I, Type II"
  claimedProvenance := EdgeProvenance.uninspectedSourceDependency
  bankProvenance := V51Provenance.assumedSourceReading
  inspection := SourceInspection.notInspected

def edgeLemma721 : DependencyEdge where
  target := "Lemma 7.21"
  premise := "Type I"
  claimedProvenance := EdgeProvenance.uninspectedSourceDependency
  bankProvenance := V51Provenance.assumedSourceReading
  inspection := SourceInspection.notInspected

def edgeTheorem82N2 : DependencyEdge where
  target := "Theorem 8.2 final N2 step"
  premise := "bounded-class pointwise estimate"
  claimedProvenance := EdgeProvenance.inheritedAuditClaim
  bankProvenance := V51Provenance.assumedSourceReading
  inspection := SourceInspection.notInspected

/-- The V5.1 dependency table, edge by edge. -/
def fmDependencyTable : List DependencyEdge :=
  [edgeLemma720, edgeProposition719, edgeLemma721, edgeTheorem82N2]

/-- No edge of the table is Lean evidence. -/
theorem fmDependencyTable_no_leanEvidence :
    fmDependencyTable.all (fun e => ! DependencyEdge.IsLeanEvidence e) = true := by decide

/-- No edge of the table was inspected in this repository. -/
theorem fmDependencyTable_none_inspected :
    fmDependencyTable.all
      (fun e => decide (e.inspection = SourceInspection.notInspected)) = true := by decide

/-- The table is **not** fully source-verified: at least one edge is only an
uninspected or inherited claim. -/
theorem fmDependencyTable_not_fully_sourceVerified :
    fmDependencyTable.any
      (fun e => decide (e.claimedProvenance ≠ EdgeProvenance.sourceVerified)) = true := by
  decide

/-- Exactly one edge is claimed source-verified by the inherited audit. -/
theorem fmDependencyTable_one_claimed_verified :
    (fmDependencyTable.filter
      (fun e => decide (e.claimedProvenance = EdgeProvenance.sourceVerified))).length = 1 := by
  decide

/-- **CG-15.**  One source-verified dependency edge does not make the whole
dependency table source-verified. -/
theorem one_edge_verified_not_table_verified :
    (∃ e ∈ fmDependencyTable, e.claimedProvenance = EdgeProvenance.sourceVerified) ∧
      ¬ (∀ e ∈ fmDependencyTable, e.claimedProvenance = EdgeProvenance.sourceVerified) := by
  constructor
  · exact ⟨edgeLemma720, by simp [fmDependencyTable], rfl⟩
  · intro h
    have := h edgeLemma721 (by simp [fmDependencyTable])
    simp [edgeLemma721] at this

/-- Upgrading the `Lemma 7.20` edge leaves the other three edges unchanged: no
edge is promoted as a side effect of another. -/
theorem upgrade_lemma720_leaves_others :
    fmDependencyTable.map (DependencyEdge.upgrade "Lemma 7.20") =
      [DependencyEdge.upgrade "Lemma 7.20" edgeLemma720,
       edgeProposition719, edgeLemma721, edgeTheorem82N2] := by
  simp [fmDependencyTable, DependencyEdge.upgrade, edgeProposition719, edgeLemma721,
    edgeTheorem82N2]

/-- Even after upgrading every edge, nothing in the table becomes Lean evidence. -/
theorem upgraded_table_no_leanEvidence (name : String) :
    (fmDependencyTable.map (DependencyEdge.upgrade name)).all
      (fun e => ! DependencyEdge.IsLeanEvidence e) = true := by
  simp only [List.all_map, List.all_eq_true, Function.comp_apply]
  intro e he
  have h : DependencyEdge.IsLeanEvidence e = false := by
    revert he
    revert e
    decide
  simp [DependencyEdge.upgrade_not_leanEvidence h]

/-- Summary entry for the dependency table. -/
def dependencyTableEntry : V51Entry where
  name := "FM dependency table (edge-by-edge)"
  provenance := V51Provenance.assumedSourceReading
  inspection := SourceInspection.notInspected
  notes :=
    "Lemma 7.20 ← (b.2) is the single edge the inherited audit claims to be " ++
    "source-supported; Proposition 7.19, Lemma 7.21 and the Theorem-8.2 final N2 " ++
    "step are recorded as uninspected / inherited.  PARTIALLY SOURCE-VERIFIED at best."

theorem dependencyTableEntry_not_leanEvidence :
    V51Entry.IsLeanEvidence dependencyTableEntry = false := rfl

end NANC.V5_1
