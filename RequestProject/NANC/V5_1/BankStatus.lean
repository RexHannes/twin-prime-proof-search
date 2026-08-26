/-
NANC V5.1 — BANK STATUS AND AXIOM AUDIT.

Three layers, kept strictly apart:

LEAN-PROVED (this file runs `#print axioms` on every one of them below):
  provenance/status inequalities, the `assumedSourceReading` firewalls, the sigma
  arithmetic (`σ ≥ 49ν/50`, `σ ≥ 49/300` at `ν = 1/6`), the safe factor-count
  consequence `Ω(n) ≤ 6`, the typed dependency/status structures, the logical
  projections, the programme DAG as data, the threshold-history data, the ten
  counterguards, and the re-use of the inherited finite twin-pair theorem.

EXTERNAL / UNINHABITED:
  `FMLemma718RoughBound`, `N2HUniformity`, `FM-N2-CELLSUM-UPPER45`, the ε-uniform
  N₂ splice, `FMShiftedPrimeT82Splice`, the two-linear-form Selberg upper sieve,
  the Mertens/PNT prefix-volume input, the Ford–Maynard analytic theorems,
  Bombieri–Vinogradov, Brun–Titchmarsh, the comparison progression mean,
  FM (b.1)/(b.2)/(w), `FullFMTypeII_OneSixth`, full Type-II reassembly, and
  twin-prime infinitude.

RESEARCH STATUS:
  Gate 0 permanent analytic pass; `FMLemma718RoughBound` an assumed source
  reading; the N₂ cellsum and its ε-uniformity research passes conditional on
  that reading; the Theorem-8.2 splice conditional and only partially
  source-verified; Gate 2 closed **only** conditional on `FullFMTypeII_OneSixth`
  and `FMLemma718RoughBound` as stated; full Type II and its reassembly open;
  twin primes NOT proved and infinitude NOT declared.
-/
import Mathlib
import RequestProject.NANC.V5_1.Counterguards

namespace NANC.V5_1

/-! ### The V5.1 status table -/

/-- The V5.1 status table, as data.  Listing an entry never creates a proof. -/
def v51StatusTable : List V51Entry :=
  [ lemma718Entry, n2HUniformityEntry, n2CellSumEntry, n2EpsilonUniformityEntry,
    t82SpliceEntry51, gate2Entry51, thresholdConventionEntry, dependencyTableEntry,
    v51EndgameEntry ]

/-- No entry of the V5.1 status table is Lean evidence. -/
theorem v51StatusTable_no_leanEvidence :
    v51StatusTable.all (fun E => ! V51Entry.IsLeanEvidence E) = true := by decide

/-- Neither is any entry of the external analytic inventory. -/
theorem v51_full_inventory_no_leanEvidence :
    (v51StatusTable ++ externalAnalyticInventory).all
      (fun E => ! V51Entry.IsLeanEvidence E) = true := by decide

/-- Twin-prime infinitude is not declared anywhere in V5.1: the programme DAG
records it as not proved. -/
theorem v51_twin_primes_not_proved :
    programmeDag ProgrammeNode.twinPrimes = ProgrammeStatus.notProved := rfl

/-! ### `#print axioms` audit of every inhabited V5.1 theorem -/

section AxiomAudit

-- ProvenancePatch
#print axioms V51Provenance.ofControl_injective
#print axioms V51Provenance.ofControl_ne_assumedSourceReading
#print axioms V51Provenance.ofControl_ne_sourceInspectedNotProved
#print axioms V51Provenance.ofControl_ne_sourceSpecificAnalyticPass
#print axioms V51Provenance.assumedSourceReading_ne_leanProved
#print axioms V51Provenance.assumedSourceReading_ne_externallyPublished
#print axioms V51Provenance.assumedSourceReading_ne_opusAuditedAnalyticPass
#print axioms V51Provenance.assumedSourceReading_ne_sourceSpecificAnalyticPass
#print axioms V51Provenance.assumedSourceReading_ne_sourceInspectedNotProved
#print axioms V51Provenance.assumedSourceReading_ne_uninhabitedInterface
#print axioms V51Provenance.sourceInspectedNotProved_ne_leanProved
#print axioms V51Provenance.not_leanEvidence_and_nonLeanEvidence
#print axioms V51Provenance.nonLeanEvidence_not_leanEvidence
#print axioms V51Provenance.assumedSourceReading_not_leanEvidence
#print axioms V51Provenance.sourceInspectedNotProved_not_leanEvidence
#print axioms V51Provenance.sourceSpecificAnalyticPass_not_leanEvidence
#print axioms V51Provenance.ofControl_isLeanEvidence
#print axioms V51Entry.not_leanEvidence_of_nonLean
#print axioms V51Entry.inspection_does_not_promote
#print axioms V51Entry.promoteByInspection_not_leanEvidence

-- N2RoughBoundInterface
#print axioms sigma_ge_of_eps_le_nu_div_hundred
#print axioms sigma_ge_49_300_of_nu_one_sixth
#print axioms real_sigma_ge_49_300_of_nu_one_sixth
#print axioms pow_length_le_prod
#print axioms rough_length_primeFactorsList_le_six
#print axioms rough_cardFactors_le_six
#print axioms PEpsilon_rough_cardFactors_le_six
#print axioms roughIndicator_eq_one
#print axioms roughIndicator_eq_zero
#print axioms lemma718Entry_not_leanEvidence
#print axioms lemma718Entry_provenance_ne_leanProved
#print axioms lemma718Entry_provenance_ne_externallyPublished
#print axioms lemma718Entry_provenance_ne_sourceSpecificAnalyticPass
#print axioms lemma718_projects_to_N2HUniformity
#print axioms n2HUniformityEntry_not_leanEvidence
#print axioms roughAt_five
#print axioms uniform_factor_bound_not_H_uniformity

-- FordMaynardSourceAudit
#print axioms fordMaynardInspection_notInspected
#print axioms fordMaynardDefaultProvenance_not_leanEvidence
#print axioms source_inspection_never_lean_evidence
#print axioms strict_ne_nonStrict
#print axioms thresholdAudit_parent_strict
#print axioms thresholdAudit_later_nonStrict
#print axioms thresholdAudit_readings_disagree
#print axioms thresholdAudit_later_provenance_not_leanEvidence
#print axioms thresholdAudit_later_provenance_ne_externallyPublished
#print axioms thresholdAudit_controllingArithmeticFact
#print axioms thresholdAudit_margin
#print axioms one_sixth_satisfies_both_conventions
#print axioms historical_strict_not_current_convention_proof
#print axioms thresholdConventionEntry_not_leanEvidence

-- DependencyAuditPatch
#print axioms DependencyEdge.upgrade_other
#print axioms DependencyEdge.upgrade_not_leanEvidence
#print axioms fmDependencyTable_no_leanEvidence
#print axioms fmDependencyTable_none_inspected
#print axioms fmDependencyTable_not_fully_sourceVerified
#print axioms fmDependencyTable_one_claimed_verified
#print axioms one_edge_verified_not_table_verified
#print axioms upgrade_lemma720_leaves_others
#print axioms upgraded_table_no_leanEvidence
#print axioms dependencyTableEntry_not_leanEvidence

-- N2CellSumRepairs
#print axioms n2CellSumRepairs_all_recorded
#print axioms n2CellSumRepairs_no_leanEvidence
#print axioms b2_lemma720_ne_b2_n2BSide
#print axioms b2_usage_independent
#print axioms n2CellSumEntry_not_leanEvidence
#print axioms n2CellSumEntry_not_sourceSpecificAnalyticPass
#print axioms n2EpsilonUniformityEntry_not_leanEvidence

-- Gate02StatusPatch
#print axioms externalAnalyticInventory_no_leanEvidence
#print axioms externalAnalyticInventory_has_new_items
#print axioms gate0ResearchStatus_matches_parent
#print axioms gate0ResearchStatus_ne_leanProved
#print axioms gate0LeanAnalyticStatus_ne_leanProved
#print axioms gate0ResearchStatus_ne_leanAnalyticStatus
#print axioms gate2Dependencies_fullTypeII_open
#print axioms gate2Dependencies_lemma718_assumedSourceReading
#print axioms gate2Dependencies_none_inhabited
#print axioms gate2Dependencies_two_distinct_antecedents
#print axioms fullTypeII_alone_ne_gate2_antecedents
#print axioms gate2Status51_not_closed
#print axioms gate2LeanAnalyticStatus_ne_leanProved
#print axioms gate2Entry51_not_leanEvidence
#print axioms t82SpliceEntry51_not_leanEvidence
#print axioms programmeDag_twinPrimes_notProved
#print axioms programmeDag_fullTypeII_open
#print axioms programmeDag_gate2_conditional
#print axioms programmeDag_no_promotion
#print axioms programmeDag_gate0_research_not_leanProved

-- ConditionalEndgamePatch
#print axioms V51ShiftedPrimeEndgamePackage.proj_fullFMTypeII
#print axioms V51ShiftedPrimeEndgamePackage.proj_lemma718
#print axioms V51ShiftedPrimeEndgamePackage.proj_gate0TypeI
#print axioms V51ShiftedPrimeEndgamePackage.proj_n2CellSumUpper
#print axioms V51ShiftedPrimeEndgamePackage.proj_twinMassPositive
#print axioms v51EndgamePackage_gives_twin_pair
#print axioms no_v51Package_without_lemma718
#print axioms no_v51Package_from_nothing
#print axioms twinMassPositive_not_automatic
#print axioms v51EndgameEntry_not_leanEvidence

-- Counterguards
#print axioms cg9_assumedSourceReading_ne_externallyPublished
#print axioms cg10_assumedSourceReading_ne_leanProved
#print axioms cg11_fullTypeII_alone_not_gate2_package
#print axioms cg12_gate2_conditional_not_twin_theorem
#print axioms cg13_cellsum_research_pass_not_lean_proof
#print axioms cg14_factor_bound_not_H_uniformity
#print axioms cg15_one_edge_not_table
#print axioms cg16_b2_usages_distinct
#print axioms cg17_gate1AB_not_fullTypeII
#print axioms cg18_historical_metadata_not_current_convention
#print axioms v51Counterguards_count
#print axioms inheritedCounterguards_count

-- BankStatus
#print axioms v51StatusTable_no_leanEvidence
#print axioms v51_full_inventory_no_leanEvidence
#print axioms v51_twin_primes_not_proved

end AxiomAudit

end NANC.V5_1
