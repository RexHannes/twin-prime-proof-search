/-
NANC V5 — AUDIT STATUS SYSTEM.

Bookkeeping only.  The point of this file is to make the repository permanently
distinguish five different kinds of assertion:

  1. finite/algebraic facts proved in Lean            (`leanProved`)
  2. externally cited analytic theorems               (`externallyPublished`)
  3. external-audit verdicts on research claims       (`opusAudited`)
  4. current research claims                          (`researchClaim`)
  5. defined-but-uninhabited interfaces               (`uninhabited`)

together with `refuted` and `sourceMissing`.

PERMANENT FIREWALLS (proved below):

    opusAudited      ≠ leanProved
    researchClaim    ≠ externallyPublished
    uninhabited      ≠ leanProved
-/
import Mathlib
import RequestProject.NANC.V4

namespace NANC.V5

/-- Audit-level status labels for entries of the NANC V5 bank. -/
inductive AuditStatus where
  /-- Formalized *and* proved in Lean inside this repository. -/
  | leanProved
  /-- A published theorem cited from the literature; not formalized here. -/
  | externallyPublished
  /-- A verdict produced by an external (non-Lean) audit of a research claim. -/
  | opusAudited
  /-- An unpublished current research claim. -/
  | researchClaim
  /-- A Prop that is defined but deliberately **not** inhabited. -/
  | uninhabited
  /-- A claim that has been shown to be false. -/
  | refuted
  /-- The source material required for the entry is missing. -/
  | sourceMissing
  deriving DecidableEq, Repr

namespace AuditStatus

/-- The statuses that legitimately assert "there is a Lean proof in this repo". -/
def IsLeanEvidence : AuditStatus → Bool
  | leanProved => true
  | _ => false

/-- The statuses that assert "no Lean inhabitant is claimed". -/
def IsNonLeanEvidence : AuditStatus → Bool
  | externallyPublished => true
  | opusAudited => true
  | researchClaim => true
  | uninhabited => true
  | sourceMissing => true
  | _ => false

/-- An external (non-Lean) audit verdict is not a Lean proof. -/
theorem opusAudited_ne_leanProved : opusAudited ≠ leanProved := by decide

/-- A current research claim is not a published theorem. -/
theorem researchClaim_ne_externallyPublished : researchClaim ≠ externallyPublished := by decide

/-- An uninhabited interface is not a Lean proof. -/
theorem uninhabited_ne_leanProved : uninhabited ≠ leanProved := by decide

/-- A published external theorem is not, by itself, a Lean proof in this repository. -/
theorem externallyPublished_ne_leanProved : externallyPublished ≠ leanProved := by decide

/-- The permanent promotion firewall: no status is simultaneously Lean evidence and
non-Lean evidence. -/
theorem not_leanEvidence_and_nonLeanEvidence (s : AuditStatus) :
    ¬ (IsLeanEvidence s = true ∧ IsNonLeanEvidence s = true) := by
  cases s <;> simp [IsLeanEvidence, IsNonLeanEvidence]

/-- Non-Lean evidence is never Lean evidence. -/
theorem nonLeanEvidence_not_leanEvidence {s : AuditStatus} (h : IsNonLeanEvidence s = true) :
    IsLeanEvidence s = false := by
  cases s <;> simp_all [IsLeanEvidence, IsNonLeanEvidence]

/-- Compatibility with the V4 status system. -/
def toV4 : AuditStatus → NANC.V4.BankStatus
  | leanProved => NANC.V4.BankStatus.leanBanked
  | externallyPublished => NANC.V4.BankStatus.externalAnalyticInput
  | opusAudited => NANC.V4.BankStatus.externalAnalyticInput
  | researchClaim => NANC.V4.BankStatus.externalAnalyticInput
  | uninhabited => NANC.V4.BankStatus.uninhabitedInterface
  | refuted => NANC.V4.BankStatus.failedRoute
  | sourceMissing => NANC.V4.BankStatus.sourceFieldMissing

/-- The translation to V4 preserves the firewall: a status that is not Lean
evidence never becomes a V4 proof-bearing status. -/
theorem toV4_not_proofBearing {s : AuditStatus} (h : IsNonLeanEvidence s = true) :
    NANC.V4.BankStatus.IsProofBearing (toV4 s) = false := by
  cases s <;> simp_all [IsNonLeanEvidence, toV4, NANC.V4.BankStatus.IsProofBearing]

end AuditStatus

end NANC.V5
