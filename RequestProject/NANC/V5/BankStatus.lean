/-
NANC V5 — BANK STATUS AND AXIOM AUDIT.

This file records, in Lean, the status of every V5 entry, and runs
`#print axioms` on every inhabited V5 theorem.

Only `propext`, `Classical.choice` and `Quot.sound` (or fewer) are allowed.
-/
import Mathlib
import RequestProject.NANC.V5.Counterguards

namespace NANC.V5

/-! ### Status table -/

/-- Entries proved in Lean in this bank. -/
def statusV5ProvenanceSystem : AuditStatus := AuditStatus.leanProved
/-- Finite twin local-factor algebra: proved. -/
def statusTwinLocalFactorAlgebra : AuditStatus := AuditStatus.leanProved
/-- Squarefree divisor expansion: proved. -/
def statusSquarefreeExpansion : AuditStatus := AuditStatus.leanProved
/-- Gate-0 deterministic compilers: proved (conditional on uninhabited inputs). -/
def statusGate0Compiler : AuditStatus := AuditStatus.leanProved
/-- The `N₂` sieve compiler: proved (conditional on uninhabited inputs). -/
def statusN2SieveCompiler : AuditStatus := AuditStatus.leanProved
/-- The ε-uniformity firewall: proved. -/
def statusEpsUniformityFirewall : AuditStatus := AuditStatus.leanProved
/-- The conditional twin-endgame dependency DAG: proved. -/
def statusConditionalEndgameDAG : AuditStatus := AuditStatus.leanProved

/-- The infinite Euler-product identity for the twin constant: uninhabited. -/
def statusTwinConstantEulerIdentity : AuditStatus := AuditStatus.uninhabited
/-- The comparison progression mean: uninhabited. -/
def statusComparisonProgressionMean : AuditStatus := AuditStatus.uninhabited
/-- Comparison condition (b.1): uninhabited. -/
def statusFMb1 : AuditStatus := AuditStatus.uninhabited
/-- Comparison condition (b.2): uninhabited. -/
def statusFMb2 : AuditStatus := AuditStatus.uninhabited
/-- Comparison condition (w): uninhabited. -/
def statusFMconditionW : AuditStatus := AuditStatus.uninhabited
/-- Weighted maximal Bombieri–Vinogradov: uninhabited. -/
def statusWeightedMaximalBV : AuditStatus := AuditStatus.uninhabited
/-- The reindexing bridge: uninhabited. -/
def statusShift2Bridge : AuditStatus := AuditStatus.uninhabited
/-- Ford–Maynard Theorem 2.7: externally published, not formalized. -/
def statusFMTheorem27 : AuditStatus := AuditStatus.externallyPublished
/-- Ford–Maynard Theorem 8.2: externally published, not formalized. -/
def statusFMTheorem82 : AuditStatus := AuditStatus.externallyPublished
/-- Ford–Maynard Theorem 8.3: externally published, not formalized. -/
def statusFMTheorem83 : AuditStatus := AuditStatus.externallyPublished
/-- The two-linear-forms upper sieve: uninhabited. -/
def statusTwoLinearFormsSieve : AuditStatus := AuditStatus.uninhabited
/-- The `N₂` shifted-prime upper bound: uninhabited. -/
def statusN2Upper : AuditStatus := AuditStatus.uninhabited
/-- ε-uniformity of the `N₂` constant: uninhabited. -/
def statusN2Uniform : AuditStatus := AuditStatus.uninhabited
/-- The Theorem-8.2 shifted-prime splice: uninhabited (research claim). -/
def statusT82Splice : AuditStatus := AuditStatus.uninhabited
/-- The full arbitrary-coefficient Type-II hypothesis at `1/6`: uninhabited. -/
def statusFullTypeII : AuditStatus := AuditStatus.uninhabited
/-- Twin-prime infinitude: uninhabited (never declared). -/
def statusTwinInfinitude : AuditStatus := AuditStatus.uninhabited
/-- The Theorem-8.2 boundedness-use audit: external-audit metadata only. -/
def statusTheorem82Audit : AuditStatus := AuditStatus.opusAudited

/-- Every entry above that is not `leanProved` fails the Lean-evidence test. -/
theorem statusTable_no_promotion :
    AuditStatus.IsLeanEvidence statusTwinConstantEulerIdentity = false ∧
    AuditStatus.IsLeanEvidence statusComparisonProgressionMean = false ∧
    AuditStatus.IsLeanEvidence statusFMb1 = false ∧
    AuditStatus.IsLeanEvidence statusFMb2 = false ∧
    AuditStatus.IsLeanEvidence statusFMconditionW = false ∧
    AuditStatus.IsLeanEvidence statusWeightedMaximalBV = false ∧
    AuditStatus.IsLeanEvidence statusShift2Bridge = false ∧
    AuditStatus.IsLeanEvidence statusFMTheorem27 = false ∧
    AuditStatus.IsLeanEvidence statusFMTheorem82 = false ∧
    AuditStatus.IsLeanEvidence statusFMTheorem83 = false ∧
    AuditStatus.IsLeanEvidence statusTwoLinearFormsSieve = false ∧
    AuditStatus.IsLeanEvidence statusN2Upper = false ∧
    AuditStatus.IsLeanEvidence statusN2Uniform = false ∧
    AuditStatus.IsLeanEvidence statusT82Splice = false ∧
    AuditStatus.IsLeanEvidence statusFullTypeII = false ∧
    AuditStatus.IsLeanEvidence statusTwinInfinitude = false ∧
    AuditStatus.IsLeanEvidence statusTheorem82Audit = false := by
  decide

/-! ### Axiom audit -/

section AxiomAudit

#print axioms AuditStatus.opusAudited_ne_leanProved
#print axioms AuditStatus.researchClaim_ne_externallyPublished
#print axioms AuditStatus.uninhabited_ne_leanProved
#print axioms AuditStatus.externallyPublished_ne_leanProved
#print axioms AuditStatus.not_leanEvidence_and_nonLeanEvidence
#print axioms AuditStatus.nonLeanEvidence_not_leanEvidence
#print axioms AuditStatus.toV4_not_proofBearing

#print axioms Provenance.not_leanEvidence_of_nonLean
#print axioms Provenance.not_both
#print axioms provenanceOpusVerdict_not_leanEvidence
#print axioms provenanceExternalTheorem_not_leanEvidence

#print axioms publishedThreshold_eq
#print axioms internalNumericalWitnessNote_not_leanEvidence
#print axioms v5_margin
#print axioms v5_one_sixth_gt_threshold

#print axioms twinComparisonWeight_nonneg
#print axioms twinComparisonWeight_even
#print axioms twinComparisonWeight_one
#print axioms candidateW_even
#print axioms genericCandidateModel_w

#print axioms prod_one_add_eq_powersetSum
#print axioms oddLocalRatio_eq_one_add
#print axioms oddPrimeProduct_eq_squarefreeDivisorSum
#print axioms twinLocalFactor_eq_squarefreeDivisorSum
#print axioms oddPrimeProduct_split_at
#print axioms twinComparison_mul_argument_expansion
#print axioms twinComparisonWeight_split_at
#print axioms truncatedTwinEulerProduct_pos
#print axioms truncatedTwinEulerProduct_mono
#print axioms eulerInterfaceProvenance_not_leanEvidence

#print axioms TwinComparisonRegularityPackage.proj_b1
#print axioms TwinComparisonRegularityPackage.proj_b2
#print axioms TwinComparisonRegularityPackage.proj_w
#print axioms no_regularity_package_from_nothing
#print axioms comparisonRegularityProvenance_not_leanEvidence

#print axioms shift2_residue_bridge_imp_multiplicative
#print axioms weightedBV_and_comparison_imply_gate0TypeI
#print axioms shift2_bridge_imply_gate0TypeI
#print axioms TauWeightNeedsAnalyticInput_not_leanEvidence
#print axioms tauBounded_not_weightedBV

#print axioms theorem82Audit_not_leanEvidence
#print axioms n2Use_does_not_exclude_otherUses
#print axioms n2Weighted_nonneg
#print axioms twoLinearForms_and_geometry_imply_n2Upper
#print axioms n2InterfaceProvenance_not_leanEvidence
#print axioms pointwiseSieve_not_uniformN2

#print axioms epsAdmissible_shrunk_gt_threshold
#print axioms epsAdmissible_theta_add_nu
#print axioms n2ForEachEpsilon_not_uniformInEpsilon
#print axioms epsUniformityProvenance_not_leanEvidence

#print axioms fullTypeII_at
#print axioms fullReassembly_certificate_imp_fullTypeII
#print axioms gate1AB_not_fullTypeIIAtOneSixth
#print axioms fullTypeIIProvenance_not_leanEvidence

#print axioms FMShiftedPrimeT82Splice.proj_gate0
#print axioms FMShiftedPrimeT82Splice.proj_fullTypeII
#print axioms FMShiftedPrimeT82Splice.proj_n2Upper
#print axioms FMShiftedPrimeT82Splice.proj_n2Uniform
#print axioms no_t82_splice_from_nothing
#print axioms theorem83Provenance_not_leanEvidence
#print axioms t82SpliceProvenance_not_leanEvidence
#print axioms t82Splice_researchClaim_ne_published

#print axioms ShiftedPrimeEndgamePackage.proj_splice
#print axioms ShiftedPrimeEndgamePackage.proj_mass
#print axioms ShiftedPrimeEndgamePackage.proj_twinMass
#print axioms endgamePackage_gives_twin_pair
#print axioms endgamePackagesAtAllScales_imp_infinitely_many_twins
#print axioms endgameProvenance_not_leanEvidence

#print axioms width_arithmetic_not_fullTypeII
#print axioms auditPass_not_leanProof
#print axioms n2Use_not_exclusive
#print axioms pointwiseSieve_not_uniformIntegration
#print axioms fixedEps_not_uniformEps
#print axioms gate0Compiler_not_weightedBV
#print axioms gate0_gate2_not_twins_without_typeII

#print axioms statusTable_no_promotion

end AxiomAudit

end NANC.V5
