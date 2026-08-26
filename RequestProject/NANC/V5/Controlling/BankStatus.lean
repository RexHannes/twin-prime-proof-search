/-
NANC V5 CONTROLLING LAYER — BANK STATUS AND AXIOM AUDIT.

This file contains no new mathematics.  It records the status table of the
controlling layer and runs `#print axioms` on every inhabited theorem added by
the layer.  The allowed axioms are `propext`, `Classical.choice`, `Quot.sound`
(or fewer); no custom axiom is introduced anywhere.
-/
import Mathlib
import RequestProject.NANC.V5.Controlling.Counterguards

namespace NANC.V5.Controlling

/-! ### Status table -/

/-- The status table of the controlling layer. -/
def controllingStatusTable : List ControlEntry :=
  [ { name := "control status system + firewalls", status := ControlStatus.leanProved,
      notes := "opusAuditedAnalyticPass / externallyPublished / uninhabitedInterface ≠ leanProved; sourceMissing ≠ failedRoute" },
    { name := "exact rational threshold arithmetic (1/6 > 1663/10000, margin 11/30000)",
      status := ControlStatus.leanProved, notes := "re-exported from V4, not re-proved" },
    { name := "published Theorem 2.7(b) inequality is STRICT (nu > 0.1663)",
      status := ControlStatus.externallyPublished,
      notes := "recorded as metadata; the strict/non-strict separation is Lean-proved" },
    { name := "P_ε rational geometry (θ+ν = 1/6-ε, γ > θ+ν)",
      status := ControlStatus.leanProved, notes := "exact ℚ arithmetic" },
    { name := "Ford–Maynard Theorem 4.16", status := ControlStatus.uninhabitedInterface,
      notes := "external interface; only the conditional compiler is Lean-proved" },
    { name := "exact Type-II endpoint convention (X/2)^θ < m ≤ X^(θ+ν)",
      status := ControlStatus.leanProved,
      notes := "recorded exactly; differs provably from the naive X^θ endpoint" },
    { name := "FMTypeIIExactAtScale", status := ControlStatus.uninhabitedInterface,
      notes := "arbitrary divisor-bounded ξ, κ quantified literally" },
    { name := "twin comparison parity algebra", status := ControlStatus.leanProved,
      notes := "elementary facts only" },
    { name := "GATE0 research status", status := ControlStatus.opusAuditedAnalyticPass,
      notes := "audited analytic pass; not a Lean proof" },
    { name := "GATE0 Lean status", status := ControlStatus.conditionalCompiler,
      notes := "deterministic compiler; analytic inputs external" },
    { name := "Bombieri–Vinogradov / Brun–Titchmarsh for shift +2",
      status := ControlStatus.uninhabitedInterface, notes := "external analytic inputs" },
    { name := "FM-N2-CELLSUM-UPPER45", status := ControlStatus.uninhabitedInterface,
      notes := "the Gate-2 controlling aggregate target" },
    { name := "N₂ cell-sum compiler chain", status := ControlStatus.conditionalCompiler,
      notes := "sieve → prefix cells → aggregate remainder → controlling target" },
    { name := "ε-uniform N₂ error", status := ControlStatus.uninhabitedInterface,
      notes := "strictly stronger than a bound for each fixed ε" },
    { name := "Ford–Maynard Theorem 8.3 mass", status := ControlStatus.externallyPublished,
      notes := "cited, not formalized" },
    { name := "GATE2", status := ControlStatus.openStatus,
      notes := "OPEN; first open item FM-N2-CELLSUM-UPPER45" },
    { name := "N2 PRO VERDICT", status := ControlStatus.openStatus, notes := "PENDING" },
    { name := "conditional endgame DAG", status := ControlStatus.uninhabitedInterface,
      notes := "every dependency is an explicit field" },
    { name := "twin-prime infinitude", status := ControlStatus.openStatus,
      notes := "NOT DECLARED" } ]

/-- **Status-table firewall.**  Every entry of the table that is not marked
`leanProved` fails to be Lean evidence. -/
theorem controllingStatusTable_no_promotion :
    ∀ E ∈ controllingStatusTable, E.status ≠ ControlStatus.leanProved →
      ControlEntry.IsLeanEvidence E = false := by
  intro E _ h
  cases hs : E.status <;>
    simp_all [ControlEntry.IsLeanEvidence, ControlStatus.IsLeanEvidence]

/-! ### Axiom audit -/

section AxiomAudit

#print axioms ControlStatus.opusAuditedAnalyticPass_ne_leanProved
#print axioms ControlStatus.externallyPublished_ne_leanProved
#print axioms ControlStatus.uninhabitedInterface_ne_leanProved
#print axioms ControlStatus.sourceMissing_ne_failedRoute
#print axioms ControlStatus.conditionalCompiler_ne_leanProved
#print axioms ControlStatus.openStatus_ne_failedRoute
#print axioms ControlStatus.not_leanEvidence_and_nonLeanEvidence
#print axioms ControlStatus.nonLeanEvidence_not_leanEvidence
#print axioms ControlStatus.toV4_not_proofBearing
#print axioms ControlStatus.opusAuditedAnalyticPass_toV4_not_proofBearing
#print axioms ControlStatus.uninhabitedInterface_toV4_not_proofBearing
#print axioms ControlEntry.not_leanEvidence_of_nonLean

#print axioms fmSourceEntry_not_leanEvidence
#print axioms control_one_sixth_gt_threshold
#print axioms control_threshold_margin
#print axioms strict_imp_nonStrict
#print axioms nonStrict_not_strict
#print axioms nu0_thresholdHypStrict
#print axioms PEpsilon_theta_add_nu
#print axioms PEpsilon_gamma_gt_theta_add_nu
#print axioms PEpsilon_gamma_lt_half
#print axioms PEpsilon_nu_thresholdHypStrict
#print axioms fmTheorem416_imp_ordinary_PEpsilon_zero
#print axioms theorem416Entry_not_leanEvidence
#print axioms ordinary_ne_bounded
#print axioms bounded_requires_more
#print axioms fmDependencyAudit_not_leanEvidence
#print axioms dependencyAudit_does_not_exclude_indirect_uses

#print axioms mem_exactTypeIIRange
#print axioms mem_naiveTypeIIRange
#print axioms exact_range_ne_naive_range
#print axioms FMTypeIIExact_imp_sourceSpecific
#print axioms sourceSpecific_not_FMTypeIIExact
#print axioms typeIIExactEntry_not_leanEvidence

#print axioms shiftedPrimeWeight_even_pos_eq_zero
#print axioms candidateA_mul_even
#print axioms candidateB_mul_even
#print axioms candidateW_mul_even
#print axioms candidateA_nonneg
#print axioms candidateB_nonneg
#print axioms candidateW_eq
#print axioms candidateB_one
#print axioms candidateW_sum_even_multiplier
#print axioms twinComparisonAnalyticEntry_not_leanEvidence

#print axioms gate0_bv_bridge_compiler
#print axioms gate0_multiplicative_compiler
#print axioms gate0ResearchStatus_ne_leanProved
#print axioms gate0LeanStatus_ne_leanProved
#print axioms gate0Entries_not_leanEvidence

#print axioms cellMass_nonneg
#print axioms totalN2Mass_nonneg
#print axioms pointwise_and_summation_imp_cellSum
#print axioms cellSum_does_not_give_pointwise
#print axioms twoLinearForms_chain_imp_cellSumUpper
#print axioms cellSum_and_epsUniform_imp_uniform
#print axioms cellSum_with_theorem83
#print axioms n2Entries_not_leanEvidence

#print axioms gate2_not_closed
#print axioms gate2_not_conditionalClosed
#print axioms gate2ControlStatus_ne_leanProved
#print axioms gate2Entry_not_leanEvidence
#print axioms n2ProVerdict_is_pending
#print axioms verdict_never_leanProved
#print axioms pass_gives_only_audited
#print axioms n2ProVerdictEntry_not_leanEvidence

#print axioms ShiftedPrimeFMEndgamePackage.proj_gate0TypeI
#print axioms ShiftedPrimeFMEndgamePackage.proj_comparisonRegularity
#print axioms ShiftedPrimeFMEndgamePackage.proj_fullFMTypeII
#print axioms ShiftedPrimeFMEndgamePackage.proj_n2CellSumUpper
#print axioms ShiftedPrimeFMEndgamePackage.proj_epsilonUniformity
#print axioms ShiftedPrimeFMEndgamePackage.proj_theorem83Mass
#print axioms ShiftedPrimeFMEndgamePackage.proj_twinMass
#print axioms endgamePackage_gives_twin_pair
#print axioms no_endgamePackage_from_nothing
#print axioms endgameDagEntry_not_leanEvidence
#print axioms twinInfinitudeEntry_not_leanEvidence

#print axioms emptyCellData_cellSum
#print axioms unitCellData_not_cellSum
#print axioms width_arithmetic_not_twin_primes
#print axioms gate0AuditPass_not_leanProof
#print axioms gate0_and_gate2_not_fullTypeII
#print axioms fullTypeII_not_gate1AB
#print axioms pointwise_stronger_than_cellSum
#print axioms fixedEpsilon_not_epsilonUniform
#print axioms ordinary_not_bounded_class
#print axioms sourceSpecificRepair_not_general

#print axioms controllingStatusTable_no_promotion

end AxiomAudit

end NANC.V5.Controlling
