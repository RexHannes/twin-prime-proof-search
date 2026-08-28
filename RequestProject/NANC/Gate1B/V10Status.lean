import RequestProject.NANC.Gate1B.V10CanonicalZeroMode
import RequestProject.NANC.Gate1B.V10HistoricalResidual
import RequestProject.NANC.Gate1B.V10PacketReassembly
import RequestProject.NANC.Gate1B.V10Counterguards
import RequestProject.NANC.Gate1B.V10FullTypeIICompiler

/-!
# V10 · Gate 1B — status and axiom audit

Classification of every principal V10 declaration.  The labels are **comments
only**: no theorem below asserts a status.

## LEAN_PROVED_FINITE_ALGEBRA

* `sum_echar` — additive orthogonality mod `q`, derived from Mathlib.
* `stdCharSystem` — the project's `AdditiveCharacterSystem` interface, inhabited.
* `unit_indicator_baseline_std` — the Ramanujan / unit baseline, unconditional.
* `fourier_inversion`, `fourierCoeff_zero`, `sum_ite_isUnit`.
* `canonical_discrepancy_has_zero_additive_mean` — the canonical zero mode.
* `canonical_discrepancy_eq_nonzero_frequencies` — purely nonzero frequencies.
* `zero_mean_fails_for_arbitrary_expected_term` — the test theorem.
* `discr_hist_eq_can_add_gap`, `weightedDiscrSum_hist_eq_can_sub_residual`,
  `switchedOperator_hist_eq_can_sub_residual` — historical = canonical − `R_E`.
* `weightedResidual_perturbation`, `switchedOperator_perturbation`,
  `historical_residual_not_determined_by_nonzero_packet`,
  `residual_changes_concretely` — the E-indeterminacy counterguards.
* `census_union`, `census_union'`, `hpp_disjoint_repeated`,
  `hpp_disjoint_generic`, `repeated_disjoint_generic`, `freq_disjoint`,
  `freq_union`, `unit_disjoint`, `unit_union`, `fullNine_census` — the packet
  census partitions actually present in the bank.
* `norm_sum_le_of_packet_budget`, `norm_rawSource_le_of_packet_budget` — the
  finite packet norm reassembly.
* the hostile tests `packet_budget_needs_leaf_bounds`,
  `empty_packet_family_certifies_nothing`,
  `nonzero_source_has_no_empty_decomposition`,
  `packet_compiler_not_self_certifying`, `gate1BClosed_not_automatic`,
  `fullTypeII_not_automatic`, `compiler_uses_existing_fullTypeII`,
  `gate1BClosed_does_not_give_fullTypeII`, `certificate_dataType_nonempty`.

## LEAN_PROVED_CONDITIONAL_COMPILER

* `gate1B_closed_of_exact_inputs` — `Gate1BClosureInputs → Gate1BClosed`.
* `fullTypeIIBound_of_reassemblyCertificate` —
  `FMReassemblyCertificate → Gate1BDet2.FullTypeIIBound`.
* `canonicalComparison_residual_vanishes`,
  `switchedOperator_hist_eq_can_of_realisation` — consequences of the
  (uninhabited) canonical comparison interface.

## OPEN_SOURCE_INTERFACE — MUST REMAIN UNINHABITED

* `Gate1BClosureInputs` — in particular its fields `highPrimeLeaf` (HIGHPRIME-
  MSWITCH), `sameQLeaf` (SAMEQ), `crossModLeaf` (CROSSMOD), `H9Leaf` (H9) and
  `zeroFork` (E = canonical ∨ residual bound).  No instance is constructed.
* `CanonicalComparisonRealisation` — no comparison sequence is supplied.
* `FMReassemblyCertificate` for the real programme — only a finite toy instance,
  irrelevant to the analytic problem, is constructed
  (`certificate_dataType_nonempty`), solely to show the data type is not
  definitionally the target.
* `TwinPrimeProject.Gate1BDet2.Gate1BClosed`, `FullTypeIIBound`, `TwinPrimes` —
  never inhabited anywhere.

## FIRST FORMAL BLOCKER

`FullFMTypeII_OneSixth` **does not exist** in this project (neither do
`FMTypeIIExactAtScale`, `Gate1AOutput`, `Gate1BOutput`,
`Gate1ABReassemblyCertificate`).  The exact missing declaration is

    def FullFMTypeII_OneSixth : ...      -- ABSENT from the whole repository

so no theorem in V10 concludes it, and none was created as a substitute.  The
conditional Type-II compiler is stated against the project's existing
`Gate1BDet2.FullTypeIIBound`, which is explicitly *not* the Ford–Maynard
one-sixth statement.
-/

namespace TwinPrimeProject
namespace Gate1BV10

/-! ## Structure field printouts (non-circularity, mechanical) -/

#print Gate1BClosureInputs
#print FMReassemblyCertificate
#print CanonicalComparisonRealisation

/-! ## Axiom audit -/

#print axioms sum_echar
#print axioms stdCharSystem
#print axioms card_units_ne_zero
#print axioms unit_indicator_baseline_std
#print axioms fourierCoeff_zero
#print axioms fourier_inversion
#print axioms sum_ite_isUnit
#print axioms canonical_discrepancy_has_zero_additive_mean
#print axioms canonical_discrepancy_eq_nonzero_frequencies
#print axioms zero_mean_fails_for_arbitrary_expected_term

#print axioms discr_hist_eq_can_add_gap
#print axioms weightedDiscrSum_hist_eq_can_sub_residual
#print axioms switchedOperator_eq_weightedDiscrSum
#print axioms switchedOperator_hist_eq_can_sub_residual
#print axioms weightedResidual_eq_zero_of_agree
#print axioms canonicalComparison_residual_vanishes
#print axioms switchedOperator_hist_eq_can_of_realisation

#print axioms hpp_disjoint_repeated
#print axioms hpp_disjoint_generic
#print axioms repeated_disjoint_generic
#print axioms census_union
#print axioms census_union'
#print axioms freq_disjoint
#print axioms freq_union
#print axioms unit_disjoint
#print axioms unit_union
#print axioms fullNine_census
#print axioms fullNine_census_index
#print axioms norm_sum_le_of_packet_budget
#print axioms norm_rawSource_le_of_packet_budget
#print axioms packet_budget_needs_leaf_bounds
#print axioms empty_packet_family_certifies_nothing
#print axioms nonzero_source_has_no_empty_decomposition
#print axioms packet_compiler_not_self_certifying

#print axioms perturbedExpected_self
#print axioms perturbedExpected_of_ne
#print axioms weightedResidual_perturbation
#print axioms switchedOperator_perturbation
#print axioms historical_residual_not_determined_by_nonzero_packet
#print axioms residual_changes_concretely
#print axioms zero_mean_fails_for_arbitrary_comparison

#print axioms Gate1BClosureInputs.rawSource_eq_sum_leafValue
#print axioms Gate1BClosureInputs.leaf_bound
#print axioms gate1B_closed_of_exact_inputs
#print axioms gate1BClosed_not_automatic
#print axioms empty_source_forces_zero
#print axioms FMReassemblyCertificate.sum_source_eq_sum_packet
#print axioms fullTypeIIBound_of_reassemblyCertificate
#print axioms compiler_uses_existing_fullTypeII
#print axioms fullTypeII_not_automatic
#print axioms certificate_dataType_nonempty
#print axioms gate1BClosed_does_not_give_fullTypeII

end Gate1BV10
end TwinPrimeProject
