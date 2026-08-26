/-
NANC V4 — GATE 0/2 FORD–MAYNARD ENDGAME SAFE BANK
Status system.

This file contains *bookkeeping* only: a datatype of bank statuses together with
the "no-promotion" guards that make it impossible to silently record an
uninhabited analytic interface as a Lean-banked proof.
-/
import Mathlib

namespace NANC.V4

/-- Status labels for entries of the NANC bank. -/
inductive BankStatus where
  /-- Statement copied verbatim from a source text. -/
  | sourceExact
  /-- Statement formalized *and* proved in Lean inside this repository. -/
  | leanBanked
  /-- A deep analytic result taken from outside; not formalized here. -/
  | externalAnalyticInput
  /-- A Prop/interface that is defined but deliberately **not** inhabited. -/
  | uninhabitedInterface
  /-- A theorem proved only under explicit hypotheses. -/
  | conditionalTheorem
  /-- A finite/decidable statement proved in Lean. -/
  | provedFinite
  /-- The source material required for the entry is missing. -/
  | sourceFieldMissing
  /-- A route that was attempted and shown to fail. -/
  | failedRoute
  /-- A certificate recording a pivot in the proof strategy. -/
  | pivotCertificate
  /-- An entry that has been withdrawn. -/
  | retracted
  /-- An entry whose dependencies have moved on. -/
  | staleDependent
  deriving DecidableEq, Repr

namespace BankStatus

/-- The statuses that legitimately assert "there is a Lean proof". -/
def IsProofBearing : BankStatus → Bool
  | leanBanked => true
  | provedFinite => true
  | _ => false

/-- The statuses that assert "no inhabitant is claimed". -/
def IsInterfaceOnly : BankStatus → Bool
  | externalAnalyticInput => true
  | uninhabitedInterface => true
  | sourceFieldMissing => true
  | _ => false

/-- Missing source material is *not* the same as a failed route. -/
theorem sourceMissing_ne_failedRoute : sourceFieldMissing ≠ failedRoute := by decide

/-- An uninhabited interface is *not* a Lean-banked proof. -/
theorem uninhabited_ne_proved : uninhabitedInterface ≠ leanBanked := by decide

/-- A conditional theorem is *not* an unconditional one. -/
theorem conditional_ne_unconditional : conditionalTheorem ≠ leanBanked := by decide

/-- An external analytic input is *not* a Lean-banked proof. -/
theorem external_ne_proved : externalAnalyticInput ≠ leanBanked := by decide

/-- No status is simultaneously proof-bearing and interface-only:
this is the permanent promotion firewall. -/
theorem not_proofBearing_and_interfaceOnly (s : BankStatus) :
    ¬ (IsProofBearing s = true ∧ IsInterfaceOnly s = true) := by
  cases s <;> simp [IsProofBearing, IsInterfaceOnly]

/-- Interface-only statuses are never proof-bearing. -/
theorem interfaceOnly_not_proofBearing {s : BankStatus} (h : IsInterfaceOnly s = true) :
    IsProofBearing s = false := by
  cases s <;> simp_all [IsProofBearing, IsInterfaceOnly]

end BankStatus

end NANC.V4
