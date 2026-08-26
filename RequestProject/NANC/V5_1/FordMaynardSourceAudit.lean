/-
NANC V5.1 — SOURCE AUDIT: AVAILABILITY OF THE FORD–MAYNARD TEXT AND THE
APPEND-ONLY THRESHOLD-CONVENTION RECORD.

Two things are recorded here.

1. SOURCE AVAILABILITY.  No readable copy of the Ford–Maynard manuscript is
   present in this repository, so no passage of it has been inspected verbatim
   during this run.  Every statement attributed to that manuscript and not
   already carried by the parent banks therefore gets provenance
   `assumedSourceReading`.

   FIREWALL: even `sourceInspectedNotProved` (a verbatim reading) is not a Lean
   proof — `V51Provenance.sourceInspectedNotProved_ne_leanProved`.

2. THE THRESHOLD-CONVENTION DISAGREEMENT (append-only).  The parent V5 bank
   records the published Theorem-2.7(b) convention as the strict inequality
   `ν > 0.1663`; a later audit reading reports `ν ≥ 0.1663`.  The old record is
   NOT erased: both readings are stored side by side, the later one with
   provenance `assumedSourceReading`.

   FIREWALL: the disagreement is irrelevant to the only downstream arithmetic
   fact actually used, `1/6 > 1663/10000` with margin `11/30000`, which holds
   under either convention.  The Lean proofs of those two facts are the existing
   V4/V5 ones, re-exported, not re-proved.
-/
import Mathlib
import RequestProject.NANC.V5_1.N2RoughBoundInterface

namespace NANC.V5_1

open NANC.V4 NANC.V5 NANC.V5.Controlling

/-! ### 1. Source availability in this repository -/

/-- Whether a readable copy of the Ford–Maynard manuscript is present in this
repository.  It is not: this run inspected no passage of it. -/
def fordMaynardSourceTextPresent : Bool := false

/-- Consequently the inspection state of every Ford–Maynard passage is
`notInspected`. -/
def fordMaynardInspection : SourceInspection := SourceInspection.notInspected

theorem fordMaynardInspection_notInspected :
    fordMaynardInspection = SourceInspection.notInspected := rfl

/-- The default provenance this bank may assign to a Ford–Maynard statement that
is not already carried by the parent banks. -/
def fordMaynardDefaultProvenance : V51Provenance :=
  V51Provenance.assumedSourceReading

theorem fordMaynardDefaultProvenance_not_leanEvidence :
    V51Provenance.IsLeanEvidence fordMaynardDefaultProvenance = false := rfl

/-- **Source-verification promotion firewall.**  Even if a verbatim source
reading became available, the resulting label is `sourceInspectedNotProved`,
which is still not Lean evidence. -/
theorem source_inspection_never_lean_evidence (E : V51Entry) :
    V51Entry.IsLeanEvidence
        { E with provenance := V51Provenance.sourceInspectedNotProved,
                 inspection := SourceInspection.inspectedVerbatim } = false := rfl

/-! ### 2. The threshold-convention audit (append-only) -/

/-- Which inequality convention a reading of Theorem 2.7(b) reports. -/
inductive ThresholdConvention where
  /-- The strict convention `ν > 0.1663`. -/
  | strict
  /-- The non-strict convention `ν ≥ 0.1663`. -/
  | nonStrict
  deriving DecidableEq, Repr

theorem strict_ne_nonStrict : ThresholdConvention.strict ≠ ThresholdConvention.nonStrict := by
  decide

/-- The hypothesis a convention imposes on `ν`, at the exact rational threshold
`1663/10000`. -/
def ThresholdConvention.hyp : ThresholdConvention → ℚ → Prop
  | strict => fun nu => fmThresholdQ < nu
  | nonStrict => fun nu => fmThresholdQ ≤ nu

/-- **Append-only audit object** for the disagreement about the published
convention.  The parent V5 metadata is kept verbatim; the later reading is
stored alongside it with its own provenance. -/
structure PublishedThresholdConventionAudit where
  /-- What the parent V5 controlling bank recorded. -/
  parentV5Metadata : ThresholdConvention
  /-- What the later audit reports. -/
  laterAuditReading : ThresholdConvention
  /-- The provenance of that later reading. -/
  laterAuditProvenance : V51Provenance
  /-- The only arithmetic fact downstream of the threshold that this bank uses. -/
  controllingArithmeticFact : Prop

/-- The concrete audit record of this run. -/
def thresholdAudit : PublishedThresholdConventionAudit where
  parentV5Metadata := ThresholdConvention.strict
  laterAuditReading := ThresholdConvention.nonStrict
  laterAuditProvenance := V51Provenance.assumedSourceReading
  controllingArithmeticFact := fmThresholdQ < nu0

theorem thresholdAudit_parent_strict :
    thresholdAudit.parentV5Metadata = ThresholdConvention.strict := rfl

theorem thresholdAudit_later_nonStrict :
    thresholdAudit.laterAuditReading = ThresholdConvention.nonStrict := rfl

theorem thresholdAudit_readings_disagree :
    thresholdAudit.parentV5Metadata ≠ thresholdAudit.laterAuditReading := by decide

theorem thresholdAudit_later_provenance_not_leanEvidence :
    V51Provenance.IsLeanEvidence thresholdAudit.laterAuditProvenance = false := rfl

theorem thresholdAudit_later_provenance_ne_externallyPublished :
    thresholdAudit.laterAuditProvenance ≠ V51Provenance.externallyPublished := by decide

/-- The controlling arithmetic fact of the audit record holds: `1/6 > 1663/10000`
(the existing V4/V5 proof, re-exported). -/
theorem thresholdAudit_controllingArithmeticFact :
    thresholdAudit.controllingArithmeticFact :=
  control_one_sixth_gt_threshold

/-- The exact margin, re-exported from the parent bank. -/
theorem thresholdAudit_margin : nu0 - fmThresholdQ = 11 / 30000 :=
  control_threshold_margin

/-- **Firewall (CG-18 arithmetic half).**  `ν = 1/6` satisfies *both* conventions,
so the metadata disagreement cannot affect the `1/6` margin. -/
theorem one_sixth_satisfies_both_conventions :
    ThresholdConvention.strict.hyp nu0 ∧ ThresholdConvention.nonStrict.hyp nu0 :=
  ⟨control_one_sixth_gt_threshold, le_of_lt control_one_sixth_gt_threshold⟩

/-- **CG-18.**  Recording the historical strict convention is not evidence that
strict is the current published convention: the audit stores a later, conflicting
reading whose provenance is only `assumedSourceReading`, and neither reading is
Lean evidence. -/
theorem historical_strict_not_current_convention_proof :
    thresholdAudit.parentV5Metadata ≠ thresholdAudit.laterAuditReading ∧
      V51Provenance.IsLeanEvidence thresholdAudit.laterAuditProvenance = false := by
  exact ⟨by decide, rfl⟩

/-- Bank entry for the threshold-convention question. -/
def thresholdConventionEntry : V51Entry where
  name := "PublishedThresholdConventionAudit"
  provenance := V51Provenance.assumedSourceReading
  inspection := SourceInspection.notInspected
  notes :=
    "Parent V5 metadata: strict ν > 0.1663.  Later audit reading: non-strict " ++
    "ν ≥ 0.1663.  Neither inspected in this repository.  Only downstream fact " ++
    "used: 1/6 > 1663/10000 with margin 11/30000, valid under both conventions."

theorem thresholdConventionEntry_not_leanEvidence :
    V51Entry.IsLeanEvidence thresholdConventionEntry = false := rfl

end NANC.V5_1
