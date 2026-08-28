import RequestProject.CurrentProgramme.CurrentStatusMixed

/-!
# Phase N · trust / axiom audit for the mixed `2|2` / Lichtman-socket layer

Every principal declaration added by this layer is passed through
`#print axioms`.  Expected output for each: exactly
`[propext, Classical.choice, Quot.sound]`, or fewer.

No `sorry`, `admit`, user `axiom`, `opaque`, `unsafe`, `native_decide` or
`@[implemented_by]` occurs in any module of this layer; the occurrences of those
words in this repository's `CurrentProgramme` files are documentation only.

No source or analytic interface is instantiated anywhere: `LichtmanT18Dictionary`,
`LichtmanT18PhysicalPin`, `LichtmanT18CoeffNorms`, `MixedGcdMomentInput`,
`EndpointMixedLichtmanInputs` and `EndpointMixedSocketInput` have **no**
constructor application in the project, in particular none using
`Classical.choice`.
-/

namespace TwinPrimeProject
namespace CurrentProgramme

/-! ## Phase A — centering -/
#print axioms Centering.centeredKernel_symm
#print axioms Centering.centeredKernel_units
#print axioms Centering.centeredKernel_row_sum_units
#print axioms Centering.sum_mul_conj_eq_sum_centered_mul_conj
#print axioms Centering.sum_centeredCoeff
#print axioms Centering.centering_needs_zero_mean

/-! ## Phase B — exact 2|2 split -/
#print axioms TwoByTwo.sum_group_one
#print axioms TwoByTwo.conv2_eq_sum_product
#print axioms TwoByTwo.sum_conv2_weight
#print axioms TwoByTwo.conv4_eq_conv2_conv2
#print axioms TwoByTwo.conv2_conj
#print axioms TwoByTwo.sum_conv2_conj_weight
#print axioms TwoByTwo.coverage_is_load_bearing

/-! ## Phase B5 — centered rewriting -/
#print axioms CenteredRewriting.rCent_two_by_two

/-! ## Phase C — mixed additive/multiplicative index -/
#print axioms MixedAddMult.nat_sub_is_not_int_sub
#print axioms MixedAddMult.nu_eq_zero_iff
#print axioms MixedAddMult.nonzero_congruence_iff_unique_j
#print axioms MixedAddMult.mixed_regroup
#print axioms MixedAddMult.nonzeroCongruence_regroup

/-! ## Phase D — collision parametrisation and L² -/
#print axioms Collision.gcd_decomposition
#print axioms Collision.collision_param
#print axioms Collision.collision_param_converse
#print axioms Collision.norm_sq_sum_le_card_mul
#print axioms Collision.sum_sq_collision_le
#print axioms Collision.sum_sq_product_factor
#print axioms Collision.collision_fibre_card_le_interval
#print axioms Collision.bMix_eq_pair_sum
#print axioms Collision.sum_sq_bMix_le
#print axioms Collision.mixedGcdMoment_not_automatic

/-! ## Phase E — Lichtman socket schema -/
#print axioms LichtmanSocket.dictionary_phase_not_free
#print axioms LichtmanSocket.dictionary_cClass_rigid
#print axioms LichtmanSocket.physicalPin_determines_phase
#print axioms LichtmanSocket.transformed_norm_not_determined_by_l2

/-! ## Phase F — capacity arithmetic and J-ledger -/
#print axioms LichtmanCapacity.rational_signal_66_107
#print axioms LichtmanCapacity.rational_signal_pos
#print axioms LichtmanCapacity.rational_signal_is_not_a_capacity_certificate
#print axioms LichtmanCapacity.LichtmanT18JLedger.jSq_eq_total
#print axioms LichtmanCapacity.LichtmanT18JLedger.jSq_le_of_terms
#print axioms LichtmanCapacity.endpointMixedLichtmanCapacity_of_inputs
#print axioms LichtmanCapacity.capacity_not_automatic

/-! ## Phase G — small-`k` firewall -/
#print axioms LichtmanCapacity.finite_k_sum_cost
#print axioms LichtmanCapacity.finite_k_cost_is_attained

/-! ## Phase H — conditional endpoint compiler -/
#print axioms EndpointMixedCompiler.nonzeroCongruence_norm_le_of_socket
#print axioms EndpointMixedCompiler.endpoint_bound_of_socket_input
#print axioms EndpointMixedCompiler.nonzeroCongruenceContribution_nonvacuous
#print axioms EndpointMixedCompiler.zero_budget_fails
#print axioms EndpointMixedCompiler.comparison_remains_independent
#print axioms EndpointMixedCompiler.comparison_pin_is_the_existing_interface

/-! ## Phase I — status graph -/
#print axioms LedgerMixed.no_closed_rows
#print axioms LedgerMixed.ledger_is_honest
#print axioms LedgerMixed.gate1B_open
#print axioms LedgerMixed.historical_offdiag_row_preserved
#print axioms LedgerMixed.offdiag_superseded_not_false
#print axioms LedgerMixed.current_frontier
#print axioms LedgerMixed.end_of_run_nonclaims

end CurrentProgramme
end TwinPrimeProject
