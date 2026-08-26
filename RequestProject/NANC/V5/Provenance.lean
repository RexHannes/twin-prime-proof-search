/-
NANC V5 — PROVENANCE RECORDS.

A `Provenance` record attaches an audit status, a named source, a version, a
scope and free-form notes to a bank entry.  Records are *data*: creating a
record never creates a proof of anything.
-/
import Mathlib
import RequestProject.NANC.V5.AuditStatus

namespace NANC.V5

/-- Provenance metadata for a bank entry. -/
structure Provenance where
  /-- The audit status of the entry. -/
  status : AuditStatus
  /-- The name of the source (paper, repository module, audit report, …). -/
  sourceName : String
  /-- The version / revision / arXiv version of that source. -/
  sourceVersion : String
  /-- The scope in which the entry is asserted. -/
  scope : String
  /-- Free-form notes. -/
  notes : String

namespace Provenance

/-- A provenance record counts as Lean evidence only when its status does. -/
def IsLeanEvidence (P : Provenance) : Bool := AuditStatus.IsLeanEvidence P.status

/-- Recording a provenance entry with a non-Lean status never yields Lean evidence,
whatever the source name, version, scope or notes say. -/
theorem not_leanEvidence_of_nonLean {P : Provenance}
    (h : AuditStatus.IsNonLeanEvidence P.status = true) : IsLeanEvidence P = false := by
  simpa [IsLeanEvidence] using AuditStatus.nonLeanEvidence_not_leanEvidence h

/-- No provenance record is simultaneously Lean evidence and non-Lean evidence. -/
theorem not_both (P : Provenance) :
    ¬ (IsLeanEvidence P = true ∧ AuditStatus.IsNonLeanEvidence P.status = true) := by
  simpa [IsLeanEvidence] using AuditStatus.not_leanEvidence_and_nonLeanEvidence P.status

end Provenance

/-- Provenance of an external audit verdict: never Lean evidence. -/
def provenanceOpusVerdict (name : String) : Provenance where
  status := AuditStatus.opusAudited
  sourceName := name
  sourceVersion := "external audit report"
  scope := "research-claim audit; no Lean inhabitant"
  notes := "An external audit PASS is not a Lean proof and never inhabits an interface."

/-- An external audit verdict is never Lean evidence — the formal version of
"external audit PASS ≠ Lean proof". -/
theorem provenanceOpusVerdict_not_leanEvidence (name : String) :
    Provenance.IsLeanEvidence (provenanceOpusVerdict name) = false := rfl

/-- Provenance of a published analytic theorem that is *not* formalized here. -/
def provenanceExternalTheorem (name version scope : String) : Provenance where
  status := AuditStatus.externallyPublished
  sourceName := name
  sourceVersion := version
  scope := scope
  notes := "Cited, not formalized: the corresponding Lean Prop is left uninhabited."

theorem provenanceExternalTheorem_not_leanEvidence (name version scope : String) :
    Provenance.IsLeanEvidence (provenanceExternalTheorem name version scope) = false := rfl

end NANC.V5
