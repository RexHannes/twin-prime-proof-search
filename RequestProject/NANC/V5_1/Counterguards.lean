/-
NANC V5.1 — PERMANENT COUNTERGUARDS CG-9 … CG-18.

All inherited V4 / V5 / V5-controlling counterguards remain in force and are
re-exported here as `inheritedCounterguards`.  This file adds the ten guards the
V5.1 audit requires.

    CG-9   assumedSourceReading ≠ externallyPublished
    CG-10  assumedSourceReading ≠ leanProved
    CG-11  FullFMTypeII_OneSixth alone ≠ the current Gate-2 antecedent package
    CG-12  Gate-2 conditional research closure ≠ the Twin Prime theorem
    CG-13  N₂ cellsum research pass conditional on Lemma 7.18
             ≠ a Lean proof of FM-N2-CELLSUM-UPPER45
    CG-14  uniform rough factor-count bound ≠ uniform analytic H bound
    CG-15  one source-verified dependency edge
             ≠ the entire Theorem-8.2 dependency table source-verified
    CG-16  (b.2) required for Lemma 7.20 ≠ (b.2) required for the N₂ b-side
    CG-17  Gate1AOutput + Gate1BOutput ≠ FullFMTypeII_OneSixth without reassembly
    CG-18  historical strict threshold metadata
             ≠ proof that strict is the current published convention
-/
import Mathlib
import RequestProject.NANC.V5_1.ConditionalEndgamePatch

namespace NANC.V5_1

open NANC.V4 NANC.V5 NANC.V5.Controlling

/-! ### CG-9 / CG-10 — the new provenance class -/

/-- **CG-9.**  An assumed source reading is not a published external theorem. -/
theorem cg9_assumedSourceReading_ne_externallyPublished :
    V51Provenance.assumedSourceReading ≠ V51Provenance.externallyPublished :=
  V51Provenance.assumedSourceReading_ne_externallyPublished

/-- **CG-10.**  An assumed source reading is not a Lean proof, and carries no
Lean evidence. -/
theorem cg10_assumedSourceReading_ne_leanProved :
    V51Provenance.assumedSourceReading ≠ V51Provenance.leanProved ∧
      V51Provenance.IsLeanEvidence V51Provenance.assumedSourceReading = false :=
  ⟨V51Provenance.assumedSourceReading_ne_leanProved, rfl⟩

/-! ### CG-11 — the Gate-2 antecedent package -/

/-- **CG-11.**  The full Type-II hypothesis alone is not the Gate-2 antecedent
package: the package has a second, distinct antecedent. -/
theorem cg11_fullTypeII_alone_not_gate2_package :
    gate2Dependencies.fullTypeII ≠ gate2Dependencies.lemma718RoughBound ∧
      gate2Dependencies ≠
        { gate2Dependencies with lemma718RoughBound := gate2Dependencies.fullTypeII } :=
  ⟨gate2Dependencies_two_distinct_antecedents, fullTypeII_alone_ne_gate2_antecedents⟩

/-! ### CG-12 — conditional closure is not a twin-prime theorem -/

/-- **CG-12.**  Gate-2 conditional research closure is not the Twin Prime
theorem: the banked Gate-2 status is not `closed`, twin primes are recorded as
not proved, and the twin conclusion genuinely requires the positivity input
(which fails, for instance, on an empty window). -/
theorem cg12_gate2_conditional_not_twin_theorem :
    gate2Status51 ≠ Gate2Status51.closed ∧
      programmeDag ProgrammeNode.twinPrimes = ProgrammeStatus.notProved ∧
      ∃ S : Finset ℕ, ¬ (0 < weightedTwinMass S) :=
  ⟨gate2Status51_not_closed, rfl, twinMassPositive_not_automatic⟩

/-! ### CG-13 — a conditional research pass is not a Lean proof -/

/-- **CG-13.**  The N₂ cellsum research pass, conditional on the Lemma-7.18
reading, is not a Lean proof of `FM-N2-CELLSUM-UPPER45`: the banked status is
`uninhabitedInterface`, and the interface is not vacuous — there is cell data on
which it fails (inherited witness). -/
theorem cg13_cellsum_research_pass_not_lean_proof :
    V51Entry.IsLeanEvidence n2CellSumEntry = false ∧
      ¬ FMN2CellSumUpperAtScale unitCellData 1 1 0 :=
  ⟨rfl, unitCellData_not_cellSum⟩

/-! ### CG-14 — factor-count bound is not analytic H-uniformity -/

/-- **CG-14.**  A uniform rough factor-count bound (`Ω(n) ≤ 6` on the exceptional
region) is not the uniform analytic bound `|H| ≤ C_{g,ν}`. -/
theorem cg14_factor_bound_not_H_uniformity :
    ∃ F : N2Family,
      (∀ eps : ℝ, ∀ n ∈ (F.data eps).region,
          RoughAt (F.data eps).sigma n ∧ ArithmeticFunction.cardFactors n ≤ 6) ∧
      ¬ N2HUniformity F :=
  uniform_factor_bound_not_H_uniformity

/-! ### CG-15 — one edge is not the table -/

/-- **CG-15.**  One source-verified dependency edge does not make the whole
Theorem-8.2 dependency table source-verified. -/
theorem cg15_one_edge_not_table :
    (∃ e ∈ fmDependencyTable, e.claimedProvenance = EdgeProvenance.sourceVerified) ∧
      ¬ (∀ e ∈ fmDependencyTable, e.claimedProvenance = EdgeProvenance.sourceVerified) :=
  one_edge_verified_not_table_verified

/-! ### CG-16 — where (b.2) is needed -/

/-- **CG-16.**  (b.2) being required for Lemma 7.20 is not the claim that it is
required by the N₂ comparison `b`-side cellsum. -/
theorem cg16_b2_usages_distinct :
    recordedB2Usage.requiredForLemma720 ≠ recordedB2Usage.requiredForN2BSide :=
  b2_lemma720_ne_b2_n2BSide

/-! ### CG-17 — the preserved Type-II reassembly firewall -/

/-- **CG-17.**  Gate-1A and Gate-1B outputs do not give the full
arbitrary-coefficient Type-II hypothesis without a reassembly certificate
(inherited controlling-layer counterexample, re-exported unchanged). -/
theorem cg17_gate1AB_not_fullTypeII :
    ∃ (A : Gate1AOutput) (B : Gate1BOutput) (mRangeOf nRangeOf : ℚ → Finset ℕ)
      (dwM dwN : ℕ → ℝ) (eps : ℚ),
      A.X = B.X ∧ A.w = B.w ∧ A.target = B.target ∧
      ¬ FullFMTypeIIAtOneSixth A.X mRangeOf nRangeOf dwM dwN A.w eps A.target :=
  fullTypeII_not_gate1AB

/-! ### CG-18 — the threshold-convention record -/

/-- **CG-18.**  The historical strict-threshold metadata is not a proof that the
strict convention is the current published one; and the disagreement does not
touch the `1/6` margin, which holds under both conventions. -/
theorem cg18_historical_metadata_not_current_convention :
    thresholdAudit.parentV5Metadata ≠ thresholdAudit.laterAuditReading ∧
      V51Provenance.IsLeanEvidence thresholdAudit.laterAuditProvenance = false ∧
      ThresholdConvention.strict.hyp nu0 ∧ ThresholdConvention.nonStrict.hyp nu0 := by
  refine ⟨by decide, rfl, ?_, ?_⟩
  · exact control_one_sixth_gt_threshold
  · exact le_of_lt control_one_sixth_gt_threshold

/-! ### The counterguard ledger -/

/-- The names of the ten V5.1 counterguards, banked as data. -/
def v51Counterguards : List String :=
  ["CG-9  assumedSourceReading ≠ externallyPublished",
   "CG-10 assumedSourceReading ≠ leanProved",
   "CG-11 FullFMTypeII_OneSixth alone ≠ Gate-2 antecedent package",
   "CG-12 Gate-2 conditional closure ≠ Twin Prime theorem",
   "CG-13 conditional N2 cellsum research pass ≠ Lean proof of FM-N2-CELLSUM-UPPER45",
   "CG-14 uniform rough factor-count bound ≠ uniform analytic H bound",
   "CG-15 one verified dependency edge ≠ whole dependency table verified",
   "CG-16 (b.2) for Lemma 7.20 ≠ (b.2) for the N2 b-side",
   "CG-17 Gate1A + Gate1B ≠ FullFMTypeII_OneSixth without reassembly",
   "CG-18 historical strict threshold metadata ≠ current published convention"]

theorem v51Counterguards_count : v51Counterguards.length = 10 := rfl

/-- The inherited guards that V5.1 explicitly keeps in force. -/
def inheritedCounterguards : List String :=
  ["V5C-1 width arithmetic ≠ twin primes",
   "V5C-2 Gate-0 audited analytic pass ≠ Lean proof",
   "V5C-3 Gate-0 + Gate-2 material ≠ full Type II",
   "V5C-4 Gate-1A + Gate-1B ≠ full Type II",
   "V5C-5 pointwise cell bound ≠ aggregate cell-sum target",
   "V5C-6 fixed-ε N2 bound ≠ ε-uniform N2 bound",
   "V5C-7 ordinary sequence class ≠ bounded sequence class",
   "V5C-8 source-specific repair ≠ general repair"]

theorem inheritedCounterguards_count : inheritedCounterguards.length = 8 := rfl

end NANC.V5_1
