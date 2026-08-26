/-
NANC V5.1 — CONSERVATIVE PROVENANCE PATCH.

APPEND-ONLY extension of the V5 controlling layer
(`RequestProject/NANC/V5/Controlling/`), which is not modified by this layer.

The single new *concept* introduced here is the provenance class

    assumedSourceReading

meaning: a mathematical statement attributed to a source, but whose exact
relevant source passage has **not** been independently inspected in the material
available to this bank.

It is deliberately NOT identified with any pre-existing status: the parent
`ControlStatus` embeds into the new `V51Provenance` type, and the embedding is
proved injective and proved to miss `assumedSourceReading`.  In particular

    assumedSourceReading ≠ leanProved
    assumedSourceReading ≠ externallyPublished
    assumedSourceReading ≠ opusAuditedAnalyticPass
    assumedSourceReading ≠ sourceSpecificAnalyticPass.

Nothing here is a mathematical assertion; creating a provenance record never
creates a proof.
-/
import Mathlib
import RequestProject.NANC.V5.Controlling

namespace NANC.V5_1

open NANC.V5.Controlling

/-! ### The V5.1 provenance universe -/

/-- V5.1 provenance labels.  The first block reproduces the parent
`ControlStatus` labels (see `ofControl` below); the last three are new to V5.1. -/
inductive V51Provenance where
  /-- Formalized *and* proved in Lean inside this repository. -/
  | leanProved
  /-- A deterministic Lean implication whose analytic inputs remain hypotheses. -/
  | conditionalCompiler
  /-- An external (non-Lean) audit verdict of "analytic pass" on a research claim. -/
  | opusAuditedAnalyticPass
  /-- A published theorem cited from the literature; not formalized here. -/
  | externallyPublished
  /-- A Prop that is defined but deliberately **not** inhabited. -/
  | uninhabitedInterface
  /-- The source material required for the entry is missing. -/
  | sourceMissing
  /-- A required input that is neither proved here nor available externally. -/
  | openStatus
  /-- A route that has been ruled out. -/
  | failedRoute
  /-- An analytic pass established only for the source-specific architecture,
  not for arbitrary sequences.  (New in V5.1: the parent universe has no such
  label, so it must not be simulated by one of the labels above.) -/
  | sourceSpecificAnalyticPass
  /-- **New in V5.1.**  A statement attributed to a source whose exact relevant
  passage has not been inspected in the material available to this bank. -/
  | assumedSourceReading
  /-- **New in V5.1.**  The relevant source passage *was* inspected verbatim in
  this repository — still not a Lean proof. -/
  | sourceInspectedNotProved
  deriving DecidableEq, Repr

namespace V51Provenance

/-- The embedding of the parent controlling-status universe.  It is injective
(`ofControl_injective`) and misses the new labels
(`ofControl_ne_assumedSourceReading`, `ofControl_ne_sourceInspectedNotProved`),
so no two distinct statuses are identified. -/
def ofControl : ControlStatus → V51Provenance
  | ControlStatus.leanProved => leanProved
  | ControlStatus.conditionalCompiler => conditionalCompiler
  | ControlStatus.opusAuditedAnalyticPass => opusAuditedAnalyticPass
  | ControlStatus.externallyPublished => externallyPublished
  | ControlStatus.uninhabitedInterface => uninhabitedInterface
  | ControlStatus.sourceMissing => sourceMissing
  | ControlStatus.openStatus => openStatus
  | ControlStatus.failedRoute => failedRoute

theorem ofControl_injective : Function.Injective ofControl := by
  intro a b h
  cases a <;> cases b <;> simp_all [ofControl]

/-- The new class is genuinely new: it is not the image of any parent status. -/
theorem ofControl_ne_assumedSourceReading (s : ControlStatus) :
    ofControl s ≠ assumedSourceReading := by
  cases s <;> simp [ofControl]

theorem ofControl_ne_sourceInspectedNotProved (s : ControlStatus) :
    ofControl s ≠ sourceInspectedNotProved := by
  cases s <;> simp [ofControl]

theorem ofControl_ne_sourceSpecificAnalyticPass (s : ControlStatus) :
    ofControl s ≠ sourceSpecificAnalyticPass := by
  cases s <;> simp [ofControl]

/-! ### The mandatory status inequalities -/

theorem assumedSourceReading_ne_leanProved : assumedSourceReading ≠ leanProved := by decide

theorem assumedSourceReading_ne_externallyPublished :
    assumedSourceReading ≠ externallyPublished := by decide

theorem assumedSourceReading_ne_opusAuditedAnalyticPass :
    assumedSourceReading ≠ opusAuditedAnalyticPass := by decide

theorem assumedSourceReading_ne_sourceSpecificAnalyticPass :
    assumedSourceReading ≠ sourceSpecificAnalyticPass := by decide

theorem assumedSourceReading_ne_sourceInspectedNotProved :
    assumedSourceReading ≠ sourceInspectedNotProved := by decide

theorem assumedSourceReading_ne_uninhabitedInterface :
    assumedSourceReading ≠ uninhabitedInterface := by decide

/-- Even a verbatim source inspection is not a Lean proof. -/
theorem sourceInspectedNotProved_ne_leanProved :
    sourceInspectedNotProved ≠ leanProved := by decide

/-! ### Evidence predicates -/

/-- The statuses asserting "there is an unconditional Lean proof in this repo". -/
def IsLeanEvidence : V51Provenance → Bool
  | leanProved => true
  | _ => false

/-- The statuses asserting "no unconditional Lean inhabitant is claimed". -/
def IsNonLeanEvidence : V51Provenance → Bool
  | leanProved => false
  | _ => true

theorem not_leanEvidence_and_nonLeanEvidence (s : V51Provenance) :
    ¬ (IsLeanEvidence s = true ∧ IsNonLeanEvidence s = true) := by
  cases s <;> simp [IsLeanEvidence, IsNonLeanEvidence]

theorem nonLeanEvidence_not_leanEvidence {s : V51Provenance}
    (h : IsNonLeanEvidence s = true) : IsLeanEvidence s = false := by
  cases s <;> simp_all [IsLeanEvidence, IsNonLeanEvidence]

theorem assumedSourceReading_not_leanEvidence :
    IsLeanEvidence assumedSourceReading = false := rfl

theorem sourceInspectedNotProved_not_leanEvidence :
    IsLeanEvidence sourceInspectedNotProved = false := rfl

theorem sourceSpecificAnalyticPass_not_leanEvidence :
    IsLeanEvidence sourceSpecificAnalyticPass = false := rfl

/-- The embedding preserves the evidence predicate: importing the parent
statuses cannot upgrade or downgrade any of them. -/
theorem ofControl_isLeanEvidence (s : ControlStatus) :
    IsLeanEvidence (ofControl s) = ControlStatus.IsLeanEvidence s := by
  cases s <;> rfl

end V51Provenance

/-! ### Source-inspection state -/

/-- Whether the relevant source passage was actually read in this repository. -/
inductive SourceInspection where
  /-- No readable copy of the passage is present in this repository. -/
  | notInspected
  /-- The passage was read verbatim from material present in this repository. -/
  | inspectedVerbatim
  deriving DecidableEq, Repr

/-- A V5.1 bank entry: a name, a provenance label, an inspection state and notes. -/
structure V51Entry where
  /-- The name of the entry. -/
  name : String
  /-- The provenance label. -/
  provenance : V51Provenance
  /-- Whether the source passage was inspected in this repository. -/
  inspection : SourceInspection
  /-- Free-form notes. -/
  notes : String

namespace V51Entry

/-- An entry is Lean evidence only when its provenance label is. -/
def IsLeanEvidence (E : V51Entry) : Bool := V51Provenance.IsLeanEvidence E.provenance

theorem not_leanEvidence_of_nonLean {E : V51Entry}
    (h : V51Provenance.IsNonLeanEvidence E.provenance = true) : IsLeanEvidence E = false :=
  V51Provenance.nonLeanEvidence_not_leanEvidence h

/-- **Source-verification promotion firewall.**  Changing the inspection state of
an entry — even to `inspectedVerbatim` — never turns it into Lean evidence. -/
theorem inspection_does_not_promote (E : V51Entry) (i : SourceInspection) :
    IsLeanEvidence { E with inspection := i } = IsLeanEvidence E := rfl

/-- Reading the source can at best move an entry from `assumedSourceReading` to
`sourceInspectedNotProved`; neither is Lean evidence. -/
def promoteByInspection (E : V51Entry) : V51Entry :=
  if E.provenance = V51Provenance.assumedSourceReading then
    { E with provenance := V51Provenance.sourceInspectedNotProved,
             inspection := SourceInspection.inspectedVerbatim }
  else E

theorem promoteByInspection_not_leanEvidence {E : V51Entry}
    (h : IsLeanEvidence E = false) : IsLeanEvidence (promoteByInspection E) = false := by
  unfold promoteByInspection
  split
  · rfl
  · exact h

end V51Entry

end NANC.V5_1
