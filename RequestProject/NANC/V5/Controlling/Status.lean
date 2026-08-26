/-
NANC V5 CONTROLLING LAYER — STATUS / PROVENANCE SYSTEM.

This layer is an APPEND-ONLY extension of the existing V4 and V5 banks: no V4 or
V5 file is modified by it.  It adds the *controlling-interface* vocabulary that
the Gate-0 / Gate-2 audit needs and that the earlier status systems do not carry,
namely the three extra labels

    conditionalCompiler   (a deterministic Lean implication, no analytic content)
    openStatus            (a required input that is neither proved nor cited)
    failedRoute           (a route that has been ruled out)

together with the permanent firewalls

    opusAuditedAnalyticPass  ≠  leanProved
    externallyPublished      ≠  leanProved
    uninhabitedInterface     ≠  leanProved
    sourceMissing            ≠  failedRoute.

Everything here is bookkeeping: no mathematical statement is inhabited.
-/
import Mathlib
import RequestProject.NANC.V5

namespace NANC.V5.Controlling

/-- Controlling-layer status labels. -/
inductive ControlStatus where
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
  deriving DecidableEq, Repr

namespace ControlStatus

/-- The statuses that assert "there is an unconditional Lean proof in this repo". -/
def IsLeanEvidence : ControlStatus → Bool
  | leanProved => true
  | _ => false

/-- The statuses that assert "no unconditional Lean inhabitant is claimed". -/
def IsNonLeanEvidence : ControlStatus → Bool
  | leanProved => false
  | _ => true

/-- An external audited analytic pass is not a Lean proof. -/
theorem opusAuditedAnalyticPass_ne_leanProved :
    opusAuditedAnalyticPass ≠ leanProved := by decide

/-- A published external theorem is not a Lean proof in this repository. -/
theorem externallyPublished_ne_leanProved : externallyPublished ≠ leanProved := by decide

/-- An uninhabited interface is not a Lean proof. -/
theorem uninhabitedInterface_ne_leanProved : uninhabitedInterface ≠ leanProved := by decide

/-- A missing source is not a failed route. -/
theorem sourceMissing_ne_failedRoute : sourceMissing ≠ failedRoute := by decide

/-- A conditional compiler is not an unconditional Lean proof of its conclusion. -/
theorem conditionalCompiler_ne_leanProved : conditionalCompiler ≠ leanProved := by decide

/-- An open input is not a failed route either. -/
theorem openStatus_ne_failedRoute : openStatus ≠ failedRoute := by decide

/-- Permanent promotion firewall: no status is simultaneously Lean evidence and
non-Lean evidence. -/
theorem not_leanEvidence_and_nonLeanEvidence (s : ControlStatus) :
    ¬ (IsLeanEvidence s = true ∧ IsNonLeanEvidence s = true) := by
  cases s <;> simp [IsLeanEvidence, IsNonLeanEvidence]

/-- Non-Lean evidence is never Lean evidence. -/
theorem nonLeanEvidence_not_leanEvidence {s : ControlStatus}
    (h : IsNonLeanEvidence s = true) : IsLeanEvidence s = false := by
  cases s <;> simp_all [IsLeanEvidence, IsNonLeanEvidence]

/-- Translation into the V5 audit-status system. -/
def toAuditStatus : ControlStatus → NANC.V5.AuditStatus
  | leanProved => NANC.V5.AuditStatus.leanProved
  | conditionalCompiler => NANC.V5.AuditStatus.leanProved
  | opusAuditedAnalyticPass => NANC.V5.AuditStatus.opusAudited
  | externallyPublished => NANC.V5.AuditStatus.externallyPublished
  | uninhabitedInterface => NANC.V5.AuditStatus.uninhabited
  | sourceMissing => NANC.V5.AuditStatus.sourceMissing
  | openStatus => NANC.V5.AuditStatus.uninhabited
  | failedRoute => NANC.V5.AuditStatus.refuted

/-- Translation into the V4 bank-status system. -/
def toV4 (s : ControlStatus) : NANC.V4.BankStatus :=
  NANC.V5.AuditStatus.toV4 (toAuditStatus s)

/-- The translation never promotes a status that is not Lean evidence in the V5
system to a proof-bearing V4 status. -/
theorem toV4_not_proofBearing {s : ControlStatus}
    (h : NANC.V5.AuditStatus.IsNonLeanEvidence (toAuditStatus s) = true) :
    NANC.V4.BankStatus.IsProofBearing (toV4 s) = false :=
  NANC.V5.AuditStatus.toV4_not_proofBearing h

/-- An audited analytic pass translates to a non-proof-bearing V4 status. -/
theorem opusAuditedAnalyticPass_toV4_not_proofBearing :
    NANC.V4.BankStatus.IsProofBearing (toV4 opusAuditedAnalyticPass) = false := by decide

/-- An uninhabited interface translates to a non-proof-bearing V4 status. -/
theorem uninhabitedInterface_toV4_not_proofBearing :
    NANC.V4.BankStatus.IsProofBearing (toV4 uninhabitedInterface) = false := by decide

end ControlStatus

/-- A controlling-layer bank entry: a name, a status and free-form notes.
Creating an entry never creates a proof. -/
structure ControlEntry where
  /-- The name of the entry. -/
  name : String
  /-- The status of the entry. -/
  status : ControlStatus
  /-- Free-form notes. -/
  notes : String

namespace ControlEntry

/-- An entry counts as Lean evidence only when its status does. -/
def IsLeanEvidence (E : ControlEntry) : Bool := ControlStatus.IsLeanEvidence E.status

/-- An entry whose status is not Lean evidence is never Lean evidence, whatever
its name and notes say. -/
theorem not_leanEvidence_of_nonLean {E : ControlEntry}
    (h : ControlStatus.IsNonLeanEvidence E.status = true) : IsLeanEvidence E = false :=
  ControlStatus.nonLeanEvidence_not_leanEvidence h

end ControlEntry

end NANC.V5.Controlling
