import RequestProject.CurrentProgramme.DependencyGraph
import RequestProject.CurrentProgramme.Gate1BEndpointCompiler
import RequestProject.CurrentProgramme.FiniteLineFourier
import RequestProject.CurrentProgramme.EndpointExponentBank
import RequestProject.CurrentProgramme.NormalisationFirewall
import RequestProject.CurrentProgramme.PascadiParameterLedger
import RequestProject.CurrentProgramme.R9LeakageArithmetic
import RequestProject.CurrentProgramme.LocalEulerAlgebra
import RequestProject.CurrentProgramme.SourceStrata

/-!
# Phase N · trust / axiom audit for the current programme layer

Every principal declaration of `RequestProject/CurrentProgramme/` is passed
through `#print axioms`.  Expected output for each: exactly
`[propext, Classical.choice, Quot.sound]`, or fewer, or
"does not depend on any axioms".

No `sorry`, `admit`, user `axiom`, `opaque`, `unsafe`, `native_decide` or
`@[implemented_by]` occurs in any `CurrentProgramme` module.  Occurrences of
those words in this repository's `CurrentProgramme` files are documentation
only.
-/

namespace TwinPrimeProject
namespace CurrentProgramme

/-! ## Status taxonomy firewalls -/
#print axioms not_closed_of_conditionalCompiler
#print axioms externallyAudited_not_kernelProved
#print axioms status_dichotomy
#print axioms LedgerEntry.honest_of_not_closed

/-! ## A1 — normalisation firewall -/
#print axioms Normalisation.defect_prime
#print axioms Normalisation.two_lt_log_eleven
#print axioms Normalisation.defect_prime_ge_half
#print axioms Normalisation.prime_defect_refutes_pointwise_log_bound
#print axioms Normalisation.defect_prime_nonneg

/-! ## A3 — smooth localisation compiler -/
#print axioms SmoothLocalisation.sum_increments
#print axioms SmoothLocalisation.wDiscrepancy_abel
#print axioms SmoothLocalisation.wDiscrepancy_le
#print axioms SmoothLocalisation.wDiscrepancy_le_uniform
#print axioms SmoothLocalisation.supNorm_alone_insufficient

/-! ## A4 / A5 / A8 — rank-one line algebra (load-bearing) -/
#print axioms RankOne.lineDet2_propagates
#print axioms RankOne.lineDet2_base_iff
#print axioms RankOne.endpoint_residue_relation
#print axioms RankOne.endpoint_residue_zmod
#print axioms RankOne.negTwoInv_involutive
#print axioms RankOne.negTwoInv_bijective
#print axioms RankOne.negTwoInv_spec
#print axioms RankOne.residue_permutation_gives_no_interval_multiplicity_bound
#print axioms RankOne.offdiag_basepoint_shift
#print axioms RankOne.offdiag_line_difference
#print axioms RankOne.offdiag_line_difference_of_shift
#print axioms RankOne.offdiag_line_difference_numeric_check
#print axioms RankOne.congruentPairs_split
#print axioms RankOne.congruentPair_param
#print axioms RankOne.congruentPair_offdiag_iff

/-! ## A4 / C1 — finite line Fourier -/
#print axioms FiniteLineFourier.sum_stdAddChar_mul
#print axioms FiniteLineFourier.lineZ_apply
#print axioms FiniteLineFourier.dft_inner
#print axioms FiniteLineFourier.mixedMoment
#print axioms FiniteLineFourier.parseval_lineZ
#print axioms FiniteLineFourier.parseval_lineB
#print axioms FiniteLineFourier.separate_energy_gives_no_cancellation

/-! ## A6 / A8 — endpoint bilinear decomposition -/
#print axioms EndpointBilinear.sum_fiber_energy
#print axioms EndpointBilinear.residueEnergy_expansion
#print axioms EndpointBilinear.residueEnergy_split
#print axioms EndpointBilinear.diagEnergy_eq_sum_sq
#print axioms EndpointBilinear.unweighted_average_is_not_the_source
#print axioms EndpointBilinear.offdiag_index_set_nonempty

/-! ## A7 — endpoint exponent bank -/
#print axioms EndpointExponents.eDiag_value
#print axioms EndpointExponents.eMargin_Y
#print axioms EndpointExponents.eMargin_X
#print axioms EndpointExponents.eDiag_relative_X
#print axioms EndpointExponents.diag_scale_rpow
#print axioms EndpointExponents.diag_scale_relative_X
#print axioms EndpointExponents.margin_lt_one
#print axioms EndpointExponents.exponent_bank_is_not_an_estimate

/-! ## Interfaces (uninhabited) and their firewalls -/
#print axioms Interfaces.familyUniformity_stronger_than_pointwise
#print axioms Interfaces.beta_p_stratification
#print axioms Interfaces.residue_discrepancy_ne_physical_without_pin
#print axioms Interfaces.pure5Pin_not_automatic

/-! ## A10 — Gate-1B endpoint conditional compiler -/
#print axioms Gate1BEndpoint.endpointEstimate_of_inputs
#print axioms Gate1BEndpoint.endpointEstimate_not_automatic
#print axioms Gate1BEndpoint.compiler_is_not_circular
#print axioms Gate1BEndpoint.endpointEstimate_does_not_give_gate1BClosed

/-! ## G — Ford generated census -/
#print axioms Ford.census_is_source_open
#print axioms Ford.gate1ARequired_not_derivable_from_empty_census
#print axioms Ford.gate1ARequired_of_one_packet
#print axioms Ford.exhaustiveness_not_automatic
#print axioms Ford.q_ge_five_of_gt_four
#print axioms Ford.minus_endpoint_le
#print axioms Ford.divisor_blocker
#print axioms Ford.divisor_blocker_nontrivial
#print axioms Ford.gdn_balancedValue_determined

/-! ## G2 / G3 — R9 -/
#print axioms R9.r9_coordinate_not_tiny
#print axioms R9.r9_coordinate_not_large
#print axioms R9.r9_four_below_cut
#print axioms R9.r9_five_above_cut
#print axioms R9.r9_H_value_seventy
#print axioms R9.seventy_depends_on_cutoff
#print axioms R9.balancedR9_is_leakage
#print axioms R9.r9_death_certificate_refuted

/-! ## J — Erdős #287 factorial Euler -/
#print axioms FactorialEuler.alternating_polarization
#print axioms FactorialEuler.aOf_corner
#print axioms FactorialEuler.factorialEulerPolarization_general
#print axioms FactorialEuler.factorialEulerPolarization_seven
#print axioms FactorialEuler.no_extra_inverse_factorial_correction
#print axioms FactorialEuler.coeffExtract_linear
#print axioms FactorialEuler.coeffExtract_linear_does_not_identify_functionals

/-! ## J4 / J5 / J6 — Pascadi ledger and balanced-seven interfaces -/
#print axioms Pascadi.eta_le_of_constraint
#print axioms Pascadi.one_seventh_gt
#print axioms Pascadi.pascadi_parameter_nogo
#print axioms Pascadi.nogo_is_parameter_specific
#print axioms Pascadi.balanced7_modulusAverage_of_inputs
#print axioms Pascadi.balanced7_not_automatic
#print axioms Pascadi.blocks_sum_seven
#print axioms Pascadi.blocks_distinct

/-! ## Ledger and dependency graph -/
#print axioms Ledger.no_closed_rows
#print axioms Ledger.ledger_is_honest
#print axioms Ledger.end_of_run_nonclaims
#print axioms Graph.spine_present
#print axioms Graph.twin_branch_present
#print axioms Graph.no_cross_implication
#print axioms Graph.providers_are_parallel
#print axioms Graph.providerArrowIsConditional
#print axioms Graph.gate0_is_a_source

/-! ## Phase J2 · local Euler algebra -/
#print axioms LocalEuler.succ_mul_localF
#print axioms LocalEuler.localEuler_tsum
#print axioms LocalEuler.lambdaLocal_conv
#print axioms LocalEuler.lambdaLocal_recursion
#print axioms LocalEuler.lambdaLocal_unique
#print axioms LocalEuler.lambdaLocal_prime
#print axioms LocalEuler.lambdaLocal_prime_power
#print axioms LocalEuler.LambdaF_prime
#print axioms LocalEuler.LambdaF_prime_power
#print axioms LocalEuler.lambdaLocal_injective_in_a

/-! ## Phase A9 / D2 / E-I · source-neutral strata, order census, recursion measure -/
#print axioms Strata.sum_stratified
#print axioms Strata.strata_disjoint
#print axioms Strata.strata_cover
#print axioms Strata.offdiagEnergy_stratified
#print axioms Strata.offdiagEnergy_prime_split
#print axioms Strata.prime_split_disjoint
#print axioms Strata.allDefectOrders_complete
#print axioms Strata.no_blanket_monotonicity
#print axioms Strata.specialisation_not_automatic
#print axioms Strata.properDvd_lt
#print axioms Strata.properDvd_wf
#print axioms Strata.properDvd_irrefl
#print axioms Strata.one_properDvd

end CurrentProgramme
end TwinPrimeProject
