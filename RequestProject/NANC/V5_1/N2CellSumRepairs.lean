/-
NANC V5.1 — THE FOUR STRUCTURAL REPAIRS OF THE N₂ CELLSUM ARGUMENT.

The controlling interface `FM-N2-CELLSUM-UPPER45` and its deterministic compiler
chain already live in the parent bank
(`RequestProject/NANC/V5/Controlling/N2CellSumInterface.lean`) and are NOT
replaced here.  This file records, as typed metadata, the four structural repairs
used in the latest analytic cellsum argument:

  A. the largest active prime variable is isolated as the final two-linear-form
     sieve variable;
  B. a coarse mesh `1 ≪ N ≪ log x` is used, not a microscopic pointwise cell
     decomposition;
  C. the aggregate remainder scale is `REM ≪ P^(1−2δ) (log x)^2`, with aggregate
     contribution of schematic size `x^(1−2δσ) / (2δ)`;
  D. the comparison `b`-side contribution in this N₂ cellsum step does not
     require condition (b.2).

None of these is a Lean proof of an analytic inequality: the asymptotic content
is recorded as external analytic metadata, deliberately not as exact arithmetic.

PERMANENT COUNTERGUARD (CG-16):

    b.2 required for Lemma 7.20   ≠   b.2 required by the N₂ comparison b-side.
-/
import Mathlib
import RequestProject.NANC.V5_1.DependencyAuditPatch

namespace NANC.V5_1

/-- What kind of object a recorded repair is. -/
inductive RepairKind where
  /-- A choice in the analytic architecture of the argument. -/
  | analyticArchitecture
  /-- An asymptotic estimate belonging to the external analytic layer. -/
  | externalAnalyticEstimate
  /-- A statement about which hypotheses a step does or does not use. -/
  | hypothesisUsageClaim
  deriving DecidableEq, Repr

/-- One recorded structural repair of the N₂ cellsum argument. -/
structure RepairRecord where
  /-- Short identifier, `"A"`–`"D"`. -/
  id : String
  /-- The schematic content of the repair. -/
  statement : String
  /-- The kind of the repair. -/
  kind : RepairKind
  /-- What this bank is willing to assert about it. -/
  provenance : V51Provenance

namespace RepairRecord

/-- A repair record is never Lean evidence. -/
def IsLeanEvidence (R : RepairRecord) : Bool := V51Provenance.IsLeanEvidence R.provenance

end RepairRecord

/-- **Repair A.**  Largest active prime is the final sieve variable. -/
def repairA : RepairRecord where
  id := "A"
  statement :=
    "the largest active prime variable is isolated as the final two-linear-form sieve variable"
  kind := RepairKind.analyticArchitecture
  provenance := V51Provenance.sourceSpecificAnalyticPass

/-- **Repair B.**  Coarse mesh regime `1 ≪ N ≪ log x` (schematic, not exact
arithmetic). -/
def repairB : RepairRecord where
  id := "B"
  statement := "coarse partition regime 1 << N << log x, not a pointwise microscopic cell mesh"
  kind := RepairKind.analyticArchitecture
  provenance := V51Provenance.sourceSpecificAnalyticPass

/-- **Repair C.**  Aggregate remainder `REM ≪ P^(1−2δ)(log x)^2`, aggregate
contribution `x^(1−2δσ)/(2δ)`.  External analytic metadata: no inequality is
proved in Lean. -/
def repairC : RepairRecord where
  id := "C"
  statement :=
    "aggregate remainder REM << P^(1-2delta) (log x)^2, aggregate contribution " ++
    "x^(1-2 delta sigma)/(2 delta) under the parameter dictionary"
  kind := RepairKind.externalAnalyticEstimate
  provenance := V51Provenance.assumedSourceReading

/-- **Repair D.**  The comparison `b`-side of this N₂ cellsum step does not need
condition (b.2). -/
def repairD : RepairRecord where
  id := "D"
  statement := "the comparison b_n contribution in this N2 cellsum step does not require (b.2)"
  kind := RepairKind.hypothesisUsageClaim
  provenance := V51Provenance.sourceSpecificAnalyticPass

/-- The four recorded repairs. -/
def n2CellSumRepairs : List RepairRecord := [repairA, repairB, repairC, repairD]

theorem n2CellSumRepairs_all_recorded :
    n2CellSumRepairs.map RepairRecord.id = ["A", "B", "C", "D"] := rfl

/-- No recorded repair is Lean evidence. -/
theorem n2CellSumRepairs_no_leanEvidence :
    n2CellSumRepairs.all (fun R => ! RepairRecord.IsLeanEvidence R) = true := by decide

/-! ### Where (b.2) is and is not used -/

/-- Which steps the comparison condition (b.2) is recorded as being needed for. -/
structure B2Usage where
  /-- (b.2) is required for Lemma 7.20. -/
  requiredForLemma720 : Bool
  /-- (b.2) is required by the N₂ comparison `b`-side cellsum. -/
  requiredForN2BSide : Bool
  deriving DecidableEq, Repr

/-- The usage this bank records: needed for Lemma 7.20, not needed for the N₂
`b`-side (Repair D). -/
def recordedB2Usage : B2Usage where
  requiredForLemma720 := true
  requiredForN2BSide := false

/-- **CG-16.**  The two usages are distinct: (b.2) being required elsewhere is not
a requirement of the N₂ comparison `b`-side. -/
theorem b2_lemma720_ne_b2_n2BSide :
    recordedB2Usage.requiredForLemma720 ≠ recordedB2Usage.requiredForN2BSide := by decide

/-- The logical shape of CG-16: the two requirement flags are independent, so no
implication between them may be assumed in either direction. -/
theorem b2_usage_independent :
    ∃ u : B2Usage, u.requiredForLemma720 = true ∧ u.requiredForN2BSide = false :=
  ⟨recordedB2Usage, rfl, rfl⟩

/-! ### Status of the cellsum research pass -/

/-- The V5.1 status of `FM-N2-CELLSUM-UPPER45`: a research pass *conditional on*
`FMLemma718RoughBound` as stated, and Lean-uninhabited. -/
def n2CellSumEntry : V51Entry where
  name := "FM-N2-CELLSUM-UPPER45"
  provenance := V51Provenance.uninhabitedInterface
  inspection := SourceInspection.notInspected
  notes :=
    "RESEARCH PASS CONDITIONAL ON FMLemma718RoughBound AS STATED; LEAN: UNINHABITED. " ++
    "Not labelled sourceSpecificAnalyticPass while the Lemma-7.18 reading is only assumed."

theorem n2CellSumEntry_not_leanEvidence : V51Entry.IsLeanEvidence n2CellSumEntry = false := rfl

/-- The cellsum status is deliberately *not* an unconditional source-specific
analytic pass. -/
theorem n2CellSumEntry_not_sourceSpecificAnalyticPass :
    n2CellSumEntry.provenance ≠ V51Provenance.sourceSpecificAnalyticPass := by decide

/-- The V5.1 status of the N₂ ε-uniformity claim. -/
def n2EpsilonUniformityEntry : V51Entry where
  name := "N2 epsilon uniformity"
  provenance := V51Provenance.uninhabitedInterface
  inspection := SourceInspection.notInspected
  notes :=
    "RESEARCH PASS CONDITIONAL ON FMLemma718RoughBound AS STATED; LEAN: UNINHABITED. " ++
    "Elementary ingredients (sigma >= 49 nu/50, sigma >= 49/300, Omega(n) <= 6) are " ++
    "Lean-proved; the analytic H-uniformity is not."

theorem n2EpsilonUniformityEntry_not_leanEvidence :
    V51Entry.IsLeanEvidence n2EpsilonUniformityEntry = false := rfl

end NANC.V5_1
