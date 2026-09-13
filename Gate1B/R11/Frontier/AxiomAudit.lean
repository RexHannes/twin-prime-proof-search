/-
# Gate1B / R11 / Frontier : axiom audit

`#print axioms` for every principal theorem of the frontier layer.  Each depends only on a subset
of `{propext, Classical.choice, Quot.sound}`; there is no custom axiom, no `sorry`, no
`native_decide`, no `@[implemented_by]`, no `unsafe` and no `opaque` in the new modules.
-/
import Gate1B.R11.Frontier.Bank

namespace Gate1B.R11.Frontier

-- Matched-line two-copy algebra
#print axioms Gate1B.R11.Frontier.dLine_shift
#print axioms Gate1B.R11.Frontier.BLine_shift
#print axioms Gate1B.R11.Frontier.matched_det_line
#print axioms Gate1B.R11.Frontier.twoCopy_det
#print axioms Gate1B.R11.Frontier.vVec_shift
#print axioms Gate1B.R11.Frontier.det_Nmat
#print axioms Gate1B.R11.Frontier.Mmat_factorisation
#print axioms Gate1B.R11.Frontier.det_Mmat
#print axioms Gate1B.R11.Frontier.det_Mmat_via_factorisation

-- Gcd descent
#print axioms Gate1B.R11.Frontier.coprime_d_A
#print axioms Gate1B.R11.Frontier.coprime_B_k
#print axioms Gate1B.R11.Frontier.gcd_dLine_two_copy
#print axioms Gate1B.R11.Frontier.gcd_BLine_two_copy
#print axioms Gate1B.R11.Frontier.gcd_dLine_two_copy_of_det
#print axioms Gate1B.R11.Frontier.gcd_BLine_two_copy_of_det
#print axioms Gate1B.R11.Frontier.twoCopy_det_descent

-- Mean zero and finite Fourier
#print axioms Gate1B.R11.Frontier.sum_bPerp_interval
#print axioms Gate1B.R11.Frontier.sum_bPerp_univ
#print axioms Gate1B.R11.Frontier.fcoef_bPerp_zero
#print axioms Gate1B.R11.Frontier.bank_fourier_inversion
#print axioms Gate1B.R11.Frontier.bank_parseval
#print axioms Gate1B.R11.Frontier.meanZero_does_not_kill_high_frequencies
#print axioms Gate1B.R11.Frontier.bPerp_high_frequency_not_zero

-- Low/high projection and first-moment reassembly
#print axioms Gate1B.R11.Frontier.low_add_high
#print axioms Gate1B.R11.Frontier.fcoef_lowProj
#print axioms Gate1B.R11.Frontier.Rtotal_eq_Rlo_add_Rhi
#print axioms Gate1B.R11.Frontier.norm_sq_add
#print axioms Gate1B.R11.Frontier.mixed_term_not_deletable
#print axioms Gate1B.R11.Frontier.Rtotal_sq_ne_sum_of_squares

-- Rough-conductor finite combinatorics
#print axioms Gate1B.R11.Frontier.sum_moebius_divisors
#print axioms Gate1B.R11.Frontier.indicator_coprime_eq_sum_moebius
#print axioms Gate1B.R11.Frontier.conductor_descent
#print axioms Gate1B.R11.Frontier.changeLevel_natCast
#print axioms Gate1B.R11.Frontier.imprimitive_factorisation
#print axioms Gate1B.R11.Frontier.dirichlet_conductor_descent

-- Audit corrections
#print axioms Gate1B.R11.Frontier.subset_cost_identity
#print axioms Gate1B.R11.Frontier.literal_j_cost_insufficient
#print axioms Gate1B.R11.Frontier.fixed_j_cost_constant
#print axioms Gate1B.R11.Frontier.ledger_correction
#print axioms Gate1B.R11.Frontier.ledger_at_zero
#print axioms Gate1B.R11.Frontier.cell_cap_uniform
#print axioms Gate1B.R11.Frontier.representative_Q_unsound

-- Rough-modulus analytic-input interface (conditional; no axiom)
#print axioms Gate1B.R11.Frontier.rough_modulus_variance_of_input
#print axioms Gate1B.R11.Frontier.roughModulusVarianceTarget_of_input
#print axioms Gate1B.R11.Frontier.largeSieve_input_load_bearing

-- Status bank, graveyard and chain firewalls
#print axioms Gate1B.R11.Frontier.bank_abstract_hilbert_hmrd
#print axioms Gate1B.R11.Frontier.bank_two_copy_determinant
#print axioms Gate1B.R11.Frontier.bank_hecke_factorisation
#print axioms Gate1B.R11.Frontier.bank_gcd_descent
#print axioms Gate1B.R11.Frontier.bank_mean_zero
#print axioms Gate1B.R11.Frontier.bank_fourier_inversion_row
#print axioms Gate1B.R11.Frontier.bank_parseval_row
#print axioms Gate1B.R11.Frontier.bank_first_moment_reassembly
#print axioms Gate1B.R11.Frontier.bank_mixed_quadratic
#print axioms Gate1B.R11.Frontier.bank_imprimitive_descent
#print axioms Gate1B.R11.Frontier.bank_principal_2j
#print axioms Gate1B.R11.Frontier.bank_ledger_114
#print axioms Gate1B.R11.Frontier.bank_cell_cap
#print axioms Gate1B.R11.Frontier.highPass_reduction
#print axioms Gate1B.R11.Frontier.physical_caller_firewall
#print axioms Gate1B.R11.Frontier.no_physical_R11_owner
#print axioms Gate1B.R11.Frontier.frontier_chain_statuses
#print axioms Gate1B.R11.Frontier.oldFSHC_superseded_not_open
#print axioms Gate1B.R11.Frontier.oldSectorA_conditional
#print axioms Gate1B.R11.Frontier.roughModulus_researchBank
#print axioms Gate1B.R11.Frontier.global_rows_open
#print axioms Gate1B.R11.Frontier.no_global_claim

-- Occupied-row arithmetic kernel (unmodified-row delta)
#print axioms Gate1B.R11.Frontier.rowAverage_zero
#print axioms Gate1B.R11.Frontier.Dpre_eq_mask_mul
#print axioms Gate1B.R11.Frontier.Dpre_far
#print axioms Gate1B.R11.Frontier.Dpre_medium
#print axioms Gate1B.R11.Frontier.Dpre_odd_support
#print axioms Gate1B.R11.Frontier.Drow_mean_zero
#print axioms Gate1B.R11.Frontier.Drow_off_row
#print axioms Gate1B.R11.Frontier.Drow_on_row
#print axioms Gate1B.R11.Frontier.freqMask_univ
#print axioms Gate1B.R11.Frontier.DpreTotal_eq_double_sum
#print axioms Gate1B.R11.Frontier.DrowTotal_of_common_interval
#print axioms Gate1B.R11.Frontier.reassembly_has_no_free_cancellation

-- Product-fibre pushforward
#print axioms Gate1B.R11.Frontier.pushforward_factorisation
#print axioms Gate1B.R11.Frontier.norm_fibreWeight_le_one
#print axioms Gate1B.R11.Frontier.norm_pushforward_le_fibreCount
#print axioms Gate1B.R11.Frontier.merged_pushforward_factorisation
#print axioms Gate1B.R11.Frontier.productFibre_equality_ne_tuplewise_equality
#print axioms Gate1B.R11.Frontier.fibreWeight_does_not_determine_selector

-- Empty-site repair transfer
#print axioms Gate1B.R11.Frontier.L_decomposition
#print axioms Gate1B.R11.Frontier.Lprin_original
#print axioms Gate1B.R11.Frontier.Lphys_repair_zero
#print axioms Gate1B.R11.Frontier.Lprin_repair
#print axioms Gate1B.R11.Frontier.Lprin_repair_eq_neg_original
#print axioms Gate1B.R11.Frontier.Lnonprin_repair_eq_Lprin_original
#print axioms Gate1B.R11.Frontier.Lprin_repairedRow
#print axioms Gate1B.R11.Frontier.Lphys_repairedRow
#print axioms Gate1B.R11.Frontier.Lnonprin_repairedRow
#print axioms Gate1B.R11.Frontier.principal_cancellation_is_not_removal
#print axioms Gate1B.R11.Frontier.repair_transfers_rather_than_removes

-- Unmodified-row compiler and width scaling
#print axioms Gate1B.R11.Frontier.CardinalInterpolation.z_injective
#print axioms Gate1B.R11.Frontier.interpolant_sample
#print axioms Gate1B.R11.Frontier.interpolant_eq_sum_support
#print axioms Gate1B.R11.Frontier.interpolant_of_zero
#print axioms Gate1B.R11.Frontier.interpolant_compiledRow
#print axioms Gate1B.R11.Frontier.interpolant_transform
#print axioms Gate1B.R11.Frontier.widthOf_scale
#print axioms Gate1B.R11.Frontier.mellin_height_scale
#print axioms Gate1B.R11.Frontier.energy_height_product_invariant
#print axioms Gate1B.R11.Frontier.narrow_interpolation_no_free_saving

-- Critical mixed incidence
#print axioms Gate1B.R11.Frontier.mixedIncidence_relation
#print axioms Gate1B.R11.Frontier.mixedIncidence_relation_converse
#print axioms Gate1B.R11.Frontier.mixedIncidence_dvd
#print axioms Gate1B.R11.Frontier.mixedIncidence_witness_unique
#print axioms Gate1B.R11.Frontier.MixedIncidenceData.relation
#print axioms Gate1B.R11.Frontier.mixedIncidence_descent
#print axioms Gate1B.R11.Frontier.mixedIncidence_no_size_bound

-- Real-overlap support
#print axioms Gate1B.R11.Frontier.ratio_bounds_of_log_le
#print axioms Gate1B.R11.Frontier.abs_sub_le_of_log_le
#print axioms Gate1B.R11.Frontier.exp_sub_one_le_two_mul
#print axioms Gate1B.R11.Frontier.abs_sub_le_two_mul_of_log_le
#print axioms Gate1B.R11.Frontier.overlap_abs_sub_le
#print axioms Gate1B.R11.Frontier.overlap_bound_is_not_o_delta

-- Critical-mask firewall
#print axioms Gate1B.R11.Frontier.maskedSum_univ
#print axioms Gate1B.R11.Frontier.full_character_sum_is_indicator
#print axioms Gate1B.R11.Frontier.abstract_full_orthogonality
#print axioms Gate1B.R11.Frontier.proper_mask_not_congruence_indicator
#print axioms Gate1B.R11.Frontier.masked_frequency_sum_not_point_mass
#print axioms Gate1B.R11.Frontier.unmasked_frequency_sum_is_point_mass

-- Status bank of the unmodified-row delta
#print axioms Gate1B.R11.Frontier.newbank_original_row_reassembly
#print axioms Gate1B.R11.Frontier.newbank_row_mean_zero
#print axioms Gate1B.R11.Frontier.newbank_freqMask_univ
#print axioms Gate1B.R11.Frontier.newbank_pushforward
#print axioms Gate1B.R11.Frontier.newbank_weight_le_one
#print axioms Gate1B.R11.Frontier.newbank_productFibre_firewall
#print axioms Gate1B.R11.Frontier.newbank_repair_source_preserving
#print axioms Gate1B.R11.Frontier.newbank_repair_transfer
#print axioms Gate1B.R11.Frontier.newbank_principal_transfer_firewall
#print axioms Gate1B.R11.Frontier.newbank_critical_mask_firewall
#print axioms Gate1B.R11.Frontier.newbank_masked_fourier_firewall
#print axioms Gate1B.R11.Frontier.newbank_mixed_incidence
#print axioms Gate1B.R11.Frontier.newbank_interpolation_sample
#print axioms Gate1B.R11.Frontier.newbank_scale_identity
#print axioms Gate1B.R11.Frontier.newbank_real_overlap
#print axioms Gate1B.R11.Frontier.newbank_rhi_still_valid
#print axioms Gate1B.R11.Frontier.empty_site_repair_firewall
#print axioms Gate1B.R11.Frontier.retired_mechanisms
#print axioms Gate1B.R11.Frontier.conditional_analytic_rows
#print axioms Gate1B.R11.Frontier.rhi_superseded_as_current_coordinate
#print axioms Gate1B.R11.Frontier.newcrit_open_rows
#print axioms Gate1B.R11.Frontier.no_newcrit_owner
#print axioms Gate1B.R11.Frontier.RnewcritSource_eq_sum
#print axioms Gate1B.R11.Frontier.bound_of_criticalMixedIncidence
#print axioms Gate1B.R11.Frontier.Rnewcrit_estimate_of_hypothesis
#print axioms Gate1B.R11.Frontier.Rnewcrit_row_open
#print axioms Gate1B.R11.Frontier.newCritKernelProved_correct
#print axioms Gate1B.R11.Frontier.newCritKernelProved_excludes_open

end Gate1B.R11.Frontier

/-! ## Minimal-gap-kernel delta -/

-- Complete divisor fibre
#print axioms Gate1B.R11.Frontier.dvd_radNat_iff
#print axioms Gate1B.R11.Frontier.Hdiv_eq_sum_radNat
#print axioms Gate1B.R11.Frontier.Hdiv_of_lt_one
#print axioms Gate1B.R11.Frontier.sum_divisors_coprime_mul
#print axioms Gate1B.R11.Frontier.sum_fibre_dvd
#print axioms Gate1B.R11.Frontier.Hdiv_forced_fibre
#print axioms Gate1B.R11.Frontier.Hdiv_eq_vonMangoldt_sub_prefix
#print axioms Gate1B.R11.Frontier.TsourceTotal_eq

-- Centered source
#print axioms Gate1B.R11.Frontier.raw_eq_centered_add_principal
#print axioms Gate1B.R11.Frontier.total_raw_eq_centered_add_principal
#print axioms Gate1B.R11.Frontier.raw_bound_of_centered_and_principal

-- Principal tail interface
#print axioms Gate1B.R11.Frontier.muDivId_mul_oneDivId
#print axioms Gate1B.R11.Frontier.muDivId_mul_hLocal
#print axioms Gate1B.R11.Frontier.hLocal_prime_pow_dvd
#print axioms Gate1B.R11.Frontier.hLocal_prime_pow_not_dvd
#print axioms Gate1B.R11.Frontier.lambda_owner_identity
#print axioms Gate1B.R11.Frontier.main_reassembly
#print axioms Gate1B.R11.Frontier.Ares_eq_conv

-- Squarefull core
#print axioms Gate1B.R11.Frontier.squarefull_decomposition
#print axioms Gate1B.R11.Frontier.squarefull_decomposition_unique
#print axioms Gate1B.R11.Frontier.sqFullPart_ne_div_radNat
#print axioms Gate1B.R11.Frontier.sqFullPart_not_square

-- Squarefree-core reflection and the local e-sum
#print axioms Gate1B.R11.Frontier.Hdiv_reflection
#print axioms Gate1B.R11.Frontier.local_e_sum
#print axioms Gate1B.R11.Frontier.local_e_sum_prime_pow
#print axioms Gate1B.R11.Frontier.local_e_sum_eq_zero_of_two_primes

-- Schinzel-Szekeres
#print axioms Gate1B.R11.Frontier.Fgap_le_iff
#print axioms Gate1B.R11.Frontier.Fgap_mono
#print axioms Gate1B.R11.Frontier.Fgap_eq_sup_tail
#print axioms Gate1B.R11.Frontier.Fgap_squarefree

-- Dense support and the well-factorability firewall
#print axioms Gate1B.R11.Frontier.factorSupport_iff_gapBound
#print axioms Gate1B.R11.Frontier.Fgap_le_of_factorSupport
#print axioms Gate1B.R11.Frontier.minFac_le_nextDiv
#print axioms Gate1B.R11.Frontier.factorSupport_six
#print axioms Gate1B.R11.Frontier.signedChart_not_product
#print axioms Gate1B.R11.Frontier.factor_support_ne_well_factorable

-- Minimal bad-gap kernel
#print axioms Gate1B.R11.Frontier.IsMinKernel.lt_mul_minFac
#print axioms Gate1B.R11.Frontier.IsMinKernel.Fgap_div_minFac_le
#print axioms Gate1B.R11.Frontier.exists_minKernel_dvd
#print axioms Gate1B.R11.Frontier.lcm_gt_of_minKernel
#print axioms Gate1B.R11.Frontier.minKernel_unique_of_dvd
#print axioms Gate1B.R11.Frontier.bad_divisor_iff
#print axioms Gate1B.R11.Frontier.bad_divisor_form
#print axioms Gate1B.R11.Frontier.minKernel_pow_lt
#print axioms Gate1B.R11.Frontier.cofactor_pow_lt

-- Bad-gap fibre contraction
#print axioms Gate1B.R11.Frontier.Hbad_contraction
#print axioms Gate1B.R11.Frontier.Hbad_eq_vonMangoldt
#print axioms Gate1B.R11.Frontier.Hbad_eq_zero_of_not_primePow
#print axioms Gate1B.R11.Frontier.prime_power_of_vonMangoldt_ne_zero

-- Complement-threshold fibre
#print axioms Gate1B.R11.Frontier.full_padic_of_large_divisor
#print axioms Gate1B.R11.Frontier.Hdiv_eq_zero_of_large_prime_sq
#print axioms Gate1B.R11.Frontier.Hdiv_two_large_primes
#print axioms Gate1B.R11.Frontier.Hdiv_one_large_prime
#print axioms Gate1B.R11.Frontier.Hdiv_one_large_prime_prefix

-- Prime-kernel bridge
#print axioms Gate1B.R11.Frontier.Fgap_prime
#print axioms Gate1B.R11.Frontier.isMinKernel_prime_iff
#print axioms Gate1B.R11.Frontier.Hbad_prime_kernel
#print axioms Gate1B.R11.Frontier.short_divisor_le_interface

-- Minimal-kernel status bank
#print axioms Gate1B.R11.Frontier.Hdiv_eq_dense_add_power_add_bridge
#print axioms Gate1B.R11.Frontier.Tsource_eq_Tkernel
#print axioms Gate1B.R11.Frontier.squarefull_mask_partition
#print axioms Gate1B.R11.Frontier.frontier_open_rows
#print axioms Gate1B.R11.Frontier.previous_bank_preserved

/-! ## Residue-aware / generated-grammar delta -/

-- Three-factor selected owner and the centered consumer
#print axioms Gate1B.R11.Frontier.lambdaStar_apply
#print axioms Gate1B.R11.Frontier.lambdaStar_support
#print axioms Gate1B.R11.Frontier.threeFactor_pairwise_coprime
#print axioms Gate1B.R11.Frontier.abs_lambdaStar_le_tau3
#print axioms Gate1B.R11.Frontier.centeredSel_one
#print axioms Gate1B.R11.Frontier.selectedConsumer_add
#print axioms Gate1B.R11.Frontier.selectedConsumer_smul
#print axioms Gate1B.R11.Frontier.selectedConsumer_bound_of_pascadi

-- Modulus lifting and the local principal correction
#print axioms Gate1B.R11.Frontier.deltaSel_mul_of_coprime
#print axioms Gate1B.R11.Frontier.uSel_mul
#print axioms Gate1B.R11.Frontier.modulus_lift_identity
#print axioms Gate1B.R11.Frontier.modulus_lift_identity_odd
#print axioms Gate1B.R11.Frontier.modulus_lift_does_not_erase_localPrincipalCorrection
#print axioms Gate1B.R11.Frontier.lifted_kernel_ne_naive_product
#print axioms Gate1B.R11.Frontier.log_split
#print axioms Gate1B.R11.Frontier.log_split_shift

-- Modulo-3 selector algebra and the direct-residue firewall
#print axioms Gate1B.R11.Frontier.I3_eq_one_iff
#print axioms Gate1B.R11.Frontier.mod3_selector_identity
#print axioms Gate1B.R11.Frontier.chi3_mul
#print axioms Gate1B.R11.Frontier.indMod3_one_eq_chi3
#print axioms Gate1B.R11.Frontier.indMod3_two_eq_chi3
#print axioms Gate1B.R11.Frontier.mod3_selector_chi3_form
#print axioms Gate1B.R11.Frontier.mod3_caller_via_modulus_lifting
#print axioms Gate1B.R11.Frontier.residue_restriction_can_destroy_mean_zero
#print axioms Gate1B.R11.Frontier.restricted_residue_not_automatically_meanZero

-- Residue-aware projections
#print axioms Gate1B.R11.Frontier.ResidueProj.binAvg_idem
#print axioms Gate1B.R11.Frontier.ResidueProj.resAvg_idem
#print axioms Gate1B.R11.Frontier.ResidueProj.resAvg_binAvg
#print axioms Gate1B.R11.Frontier.ResidueProj.binAvg_resAvg
#print axioms Gate1B.R11.Frontier.ResidueProj.binAvg_comm
#print axioms Gate1B.R11.Frontier.ResidueProj.binAvg_resAvg_comm
#print axioms Gate1B.R11.Frontier.ResidueProj.resAvg_comm
#print axioms Gate1B.R11.Frontier.ResidueProj.subT_subP_self
#print axioms Gate1B.R11.Frontier.ResidueProj.subT_subP_comm
#print axioms Gate1B.R11.Frontier.ResidueProj.Q3_subP_comm
#print axioms Gate1B.R11.Frontier.ResidueProj.Q3_Qold
#print axioms Gate1B.R11.Frontier.ResidueProj.binAvg_Qold_eq_zero
#print axioms Gate1B.R11.Frontier.ResidueProj.resAvg_Q3_eq_zero

-- Residue-aware telescoping and R_loc-top,3
#print axioms Gate1B.R11.Frontier.ResidueProj.Qold_sub_Q3_eq_telescope
#print axioms Gate1B.R11.Frontier.ResidueProj.telescope_explicit
#print axioms Gate1B.R11.Frontier.ResidueProj.suffix_stays_P_centered
#print axioms Gate1B.R11.Frontier.ResidueProj.residual_stays_T_centered
#print axioms Gate1B.R11.Frontier.ResidueProj.no_double_charge
#print axioms Gate1B.R11.Frontier.ResidueProj.no_double_charge_middle
#print axioms Gate1B.R11.Frontier.ResidueProj.selectedCenteredFunctional_add
#print axioms Gate1B.R11.Frontier.ResidueProj.selectedConsumer_three_component
#print axioms Gate1B.R11.Frontier.ResidueProj.RlocTop3_def

-- Generated grammar: fresh prime convolution
#print axioms Gate1B.R11.Frontier.divisors_mul_prime
#print axioms Gate1B.R11.Frontier.divisors_mul_prime_disjoint
#print axioms Gate1B.R11.Frontier.dconv_fresh_prime
#print axioms Gate1B.R11.Frontier.dconv_fresh_prime_squarefree
#print axioms Gate1B.R11.Frontier.semExpr_conv_fresh_prime

-- Generated grammar: amplitude and variation
#print axioms Gate1B.R11.Frontier.ampBudget_nonneg
#print axioms Gate1B.R11.Frontier.ampBudget_add_le
#print axioms Gate1B.R11.Frontier.ampBudget_mul_le
#print axioms Gate1B.R11.Frontier.ampBudget_smul_le
#print axioms Gate1B.R11.Frontier.ampBudget_conv_le
#print axioms Gate1B.R11.Frontier.norm_semExpr_le_ampBudget
#print axioms Gate1B.R11.Frontier.pathVar_add_le
#print axioms Gate1B.R11.Frontier.pathVar_mul_le
#print axioms Gate1B.R11.Frontier.pathVar_smul
#print axioms Gate1B.R11.Frontier.pathVar_sum_le
#print axioms Gate1B.R11.Frontier.pathVar_of_monotone_le
#print axioms Gate1B.R11.Frontier.rampR_antitone
#print axioms Gate1B.R11.Frontier.scaledVar_atom_le
#print axioms Gate1B.R11.Frontier.scaledVar_dconv_le
#print axioms Gate1B.R11.Frontier.scaledVar_semExpr_le
#print axioms Gate1B.R11.Frontier.scaledVar_dconv_le_two_pow
#print axioms Gate1B.R11.Frontier.pathVar_supported
#print axioms Gate1B.R11.Frontier.pathVar_zero_extension_le
#print axioms Gate1B.R11.Frontier.countP_dvd_le_omega
#print axioms Gate1B.R11.Frontier.zero_extension_cost_omega
#print axioms Gate1B.R11.Frontier.zero_extension_cost_eleven
#print axioms Gate1B.R11.Frontier.unshifted_variation_does_not_imply_shifted
#print axioms Gate1B.R11.Frontier.semExpr_shift_not_universal

-- Historical realisation interface and Q3 provenance
#print axioms Gate1B.R11.Frontier.generated_of_realFordCertificate
#print axioms Gate1B.R11.Frontier.ResidueProj.histDelta_reassembly
#print axioms Gate1B.R11.Frontier.ResidueProj.selectedCenteredFunctional_hist
#print axioms Gate1B.R11.Frontier.ResidueProj.resAvg_Q3_histDelta_eq_zero
#print axioms Gate1B.R11.Frontier.ResidueProj.histDelta_provenance_split
#print axioms Gate1B.R11.Frontier.ResidueProj.selectedCenteredFunctional_provenance
#print axioms Gate1B.R11.Frontier.ResidueProj.consumer_difference_reduces_to_Q3

-- Firewalls and status bank
#print axioms Gate1B.R11.Frontier.disconnected_hypergraph_firewall
#print axioms Gate1B.R11.Frontier.disconnected_does_not_kill_top_interaction
#print axioms Gate1B.R11.Frontier.finrank_units_mod3
#print axioms Gate1B.R11.Frontier.finrank_units_mod5
#print axioms Gate1B.R11.Frontier.mod3_unit_span
#print axioms Gate1B.R11.Frontier.mod5_unit_two_function_span_fails
#print axioms Gate1B.R11.Frontier.mod3_to_mod5_not_automatic
#print axioms Gate1B.R11.Frontier.bank_modulus_lifting
#print axioms Gate1B.R11.Frontier.bank_local_principal_correction
#print axioms Gate1B.R11.Frontier.bank_log_split
#print axioms Gate1B.R11.Frontier.bank_mod3_selector
#print axioms Gate1B.R11.Frontier.bank_mod3_derived_caller
#print axioms Gate1B.R11.Frontier.bank_direct_residue_firewall
#print axioms Gate1B.R11.Frontier.bank_q3_qold
#print axioms Gate1B.R11.Frontier.bank_residue_aware_telescoping
#print axioms Gate1B.R11.Frontier.bank_fresh_prime_convolution
#print axioms Gate1B.R11.Frontier.bank_amplitude_recursion
#print axioms Gate1B.R11.Frontier.bank_evaluation_point_firewall
#print axioms Gate1B.R11.Frontier.bank_disconnected_gate_firewall
#print axioms Gate1B.R11.Frontier.bank_mod3_mod5_firewall
#print axioms Gate1B.R11.Frontier.frontier_open_rows_not_proved
#print axioms Gate1B.R11.Frontier.rlocTop3_analytic_bound_open
#print axioms Gate1B.R11.Frontier.realFordGrammarCertificate_open
#print axioms Gate1B.R11.Frontier.downstream_all_open

-- R_loc-top,3 reduction delta: self-adjointness, exact pairing identity, deterministic budget
#print axioms Gate1B.R11.Frontier.ResidueProj.abs_Q3_le
#print axioms Gate1B.R11.Frontier.ResidueProj.Q3_sub
#print axioms Gate1B.R11.Frontier.ResidueProj.subT_subT_comm
#print axioms Gate1B.R11.Frontier.ResidueProj.Q3_subT_comm
#print axioms Gate1B.R11.Frontier.ResidueProj.resAvg_self_adjoint
#print axioms Gate1B.R11.Frontier.ResidueProj.subT_self_adjoint
#print axioms Gate1B.R11.Frontier.ResidueProj.Q3_self_adjoint
#print axioms Gate1B.R11.Frontier.ResidueProj.Q3_of_residueDetermined
#print axioms Gate1B.R11.Frontier.ResidueProj.RlocTop3_eq_pair_rowConsumer
#print axioms Gate1B.R11.Frontier.ResidueProj.RlocTop3_eq_pair_Q3_rowConsumer
#print axioms Gate1B.R11.Frontier.ResidueProj.RlocTop3_eq_zero_of_residueDetermined_rowConsumer
#print axioms Gate1B.R11.Frontier.ResidueProj.residueDetermined_rowConsumer_of_kernel
#print axioms Gate1B.R11.Frontier.ResidueProj.RLocTop3Bound_of_residue_approximation
#print axioms Gate1B.R11.Frontier.ResidueProj.RLocTop3Bound_of_profile
#print axioms Gate1B.R11.Frontier.ResidueProj.sharp_RlocTop3_eq_one
#print axioms Gate1B.R11.Frontier.ResidueProj.residue_awareness_alone_does_not_kill_RlocTop3

-- Local principal correction: exact reassembly, exact sign, mod-3 sign pairing
#print axioms Gate1B.R11.Frontier.selected_row_lift_split
#print axioms Gate1B.R11.Frontier.selected_row_lift_split_three
#print axioms Gate1B.R11.Frontier.localPrincipalCorrection_three_selected
#print axioms Gate1B.R11.Frontier.localPrincipalCorrection_three_unselected
#print axioms Gate1B.R11.Frontier.localPrincipalCorrection_three_zero
#print axioms Gate1B.R11.Frontier.localPrincipalCorrection_three_selected_nonpos
#print axioms Gate1B.R11.Frontier.localPrincipalCorrection_three_unselected_nonneg
#print axioms Gate1B.R11.Frontier.localPrincipalCorrection_three_pairs_cancel
#print axioms Gate1B.R11.Frontier.localPrincipalRow_of_paired_window

-- Prime-extrema realisation and the historical-certificate field audit
#print axioms Gate1B.R11.Frontier.greatestPrimeFactor_prime
#print axioms Gate1B.R11.Frontier.greatestPrimeFactor_dvd
#print axioms Gate1B.R11.Frontier.le_greatestPrimeFactor
#print axioms Gate1B.R11.Frontier.primeExtremaRealisation_inhabited
#print axioms Gate1B.R11.Frontier.realFordGrammarObligation_holds_vacuously
#print axioms Gate1B.R11.Frontier.emptySlotFordCertificate_isEmpty
#print axioms Gate1B.R11.Frontier.nonempty_slot_of_realFordGrammarObligationFor
#print axioms Gate1B.R11.Frontier.ResidueProj.rowConsumerResidueProfile_of_oscillation
#print axioms Gate1B.R11.Frontier.ResidueProj.rowConsumerResidueOscillation_of_profile
#print axioms Gate1B.R11.Frontier.ResidueProj.RLocTop3Bound_of_oscillation

-- Latest frontier sync (Gate1B/R11/Frontier/Latest/)
#print axioms Gate1B.R11.Frontier.Latest.globalCore_sum
#print axioms Gate1B.R11.Frontier.Latest.globalCore_mask_split
#print axioms Gate1B.R11.Frontier.Latest.sum_pairs_by_gcd
#print axioms Gate1B.R11.Frontier.Latest.gcd_class_coprime
#print axioms Gate1B.R11.Frontier.Latest.nuk_reassembly_symm
#print axioms Gate1B.R11.Frontier.Latest.cpKernel_eq
#print axioms Gate1B.R11.Frontier.Latest.sum_cpKernel_complete_period
#print axioms Gate1B.R11.Frontier.Latest.sum_positive_branch
#print axioms Gate1B.R11.Frontier.Latest.chi_p_cancels
#print axioms Gate1B.R11.Frontier.Latest.chi_positive_branch_factor
#print axioms Gate1B.R11.Frontier.Latest.partial_period_sum_not_forced_zero
#print axioms Gate1B.R11.Frontier.Latest.sum_over_prime_divisor_coordinate
#print axioms Gate1B.R11.Frontier.Latest.exists_divisor_in_window
#print axioms Gate1B.R11.Frontier.Latest.universal_three_sevenths_split
#print axioms Gate1B.R11.Frontier.Latest.card_residue_class_le
#print axioms Gate1B.R11.Frontier.Latest.card_divisors_in_range_le
#print axioms Gate1B.R11.Frontier.Latest.sum_ee_complete
#print axioms Gate1B.R11.Frontier.Latest.affine_gram
#print axioms Gate1B.R11.Frontier.Latest.affine_parseval
#print axioms Gate1B.R11.Frontier.Latest.affine_mode_bound
#print axioms Gate1B.R11.Frontier.Latest.sum_units_add_nonunits
#print axioms Gate1B.R11.Frontier.Latest.nonunits_prime_eq_zero
#print axioms Gate1B.R11.Frontier.Latest.prime_nonunit_centered_covariance_eq_zero
#print axioms Gate1B.R11.Frontier.Latest.centered_covariance_eq_zero_of_card_one
#print axioms Gate1B.R11.Frontier.Latest.scaledIsometry_no_contraction
#print axioms Gate1B.R11.Frontier.Latest.no_contraction_factor
#print axioms Gate1B.R11.Frontier.Latest.per_mode_bound_does_not_close
#print axioms Gate1B.R11.Frontier.Latest.summed_wrapper_nonclosing
#print axioms Gate1B.R11.Frontier.Latest.synthesis_scaled_isometry
#print axioms Gate1B.R11.Frontier.Latest.synthesis_no_source_contraction
#print axioms Gate1B.R11.Frontier.Latest.retained_trichotomy
#print axioms Gate1B.R11.Frontier.Latest.retained_bounded
#print axioms Gate1B.R11.Frontier.Latest.zero_moment_split
#print axioms Gate1B.R11.Frontier.Latest.ZeroMomentBound.mono
#print axioms Gate1B.R11.Frontier.Latest.total_moment_of_split
#print axioms Gate1B.R11.Frontier.Latest.counting_close_to_main_of_small_zero_mass
#print axioms Gate1B.R11.Frontier.Latest.positive_branch_complete_period_unavailable
#print axioms Gate1B.R11.Frontier.Latest.positive_branch_exponent_gap
#print axioms Gate1B.R11.Frontier.Latest.positive_branch_identities_do_not_bound
#print axioms Gate1B.R11.Frontier.Latest.core_eq_masked_add_rest
#print axioms Gate1B.R11.Frontier.Latest.chamberCoefficient_ne_zero
#print axioms Gate1B.R11.Frontier.Latest.rest_abs_le_of_chamber_bounds
#print axioms Gate1B.R11.Frontier.Latest.rest_eq_single_chamber
#print axioms Gate1B.R11.Frontier.Latest.total_eq_d1_add_d2_iff_d3_zero
#print axioms Gate1B.R11.Frontier.Latest.d3_zero_not_automatic
#print axioms Gate1B.R11.Frontier.Latest.cutSet_r11
#print axioms Gate1B.R11.Frontier.Latest.cutSet_gate1B_extra
#print axioms Gate1B.R11.Frontier.Latest.externalInputs_r11
#print axioms Gate1B.R11.Frontier.Latest.oldCut_rowConsumer_still_live
#print axioms Gate1B.R11.Frontier.Latest.no_old_node_discharged
#print axioms Gate1B.R11.Frontier.Latest.sharp_rowConsumer_oscillation_fails
#print axioms Gate1B.R11.Frontier.Latest.oldFrontier_reduction_still_valid
#print axioms Gate1B.R11.Frontier.Latest.zeroMomentBound_of_card_and_pointwise

-- Canonical root sync (Gate1B/R11/Frontier/CanonicalRootSync/)
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.rootSum_split
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.rootSum_eq_R11Residual
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.rootSum_add_source
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.rootSum_mask_split
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.canonical_root_identity
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.scalarBudget_add
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.scalarBudget_mono
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.scalarBudget_of_parts
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.identity_not_budgeted
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.zero_budgeted
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.errorBudget_not_implied_by_identity
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.hbCoeff_five
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.k5_identity
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.k5_identity_sum
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.k5_identity_dirichlet
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.k5Branch_two
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.k5_j2_isolation
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.physical_iff
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.not_physical_of_atom_large
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.physical_theta_lt
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.maximalPacket_physical
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.theta_le_maximal
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.wright_eta_prefix
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.wright_eta_prefix_iff
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.wright_fails_above_prefix
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.uncovered_eta_two_fifths
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.theta_le_of_certificate
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.pascadi_capacity_firewall
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.not_pascadiCallable_of_theta_large
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.pascadiCallable_nonvacuous
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.pascadi_ceiling_sharp
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.openBox_physical
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.openBox_theta
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.openBox_not_pascadiCallable
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.openBox_not_wright
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.survivor_region_nonempty
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.fixture619_nonphysical
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.fixture619_relaxed_holds
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.relaxed_has_no_four_sevenths_ceiling
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.fixture619_not_literally_callable
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.fixture563_physical
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.fixture563_callable
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.fixture_reconciliation
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.dbRaw_coefficient
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.dbRaw_eq_centered_add_principal
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.dbRaw_mask_split
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.sum_centered_kernel
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.dbCentered_add_source
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.dbPrincipal_eq_zero_iff
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.raw_budget_of_centered_and_principal
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.charts_do_not_create_owners
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.j2_algebra_does_not_imply_bound
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.r11_of_canonical_route
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.canonical_route_bridges_satisfiable
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.j2_owner_is_load_bearing
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.no_owner_discharged
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.absorbedOwners_spec
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.stillIndependentOwners_spec
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.owner_counts
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.absorption_witness
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.independence_witness
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.independence_verdict_unique
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.missing_bridges_are_identities
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.legacy_cut_preserved
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.legacy_cut_length
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.ccutSet_r11
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.ccutSet_r11_length
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.unique_j2_owner
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.legacy_owners_retained
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.legacy_owners_offroute
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.downstream_unchanged
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.rlocTop3_reduction_preserved
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.rlocTop3_owner_independent_of_canonical_root
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.rlocTop3_owner_offroute
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.rlocTop3_not_absorbed
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.rlocTop3_resolved
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.cut_sizes
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.canonical_cut_composition
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.classification_counts
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.classification_partition
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.downstream_still_open
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.nothing_discharged
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.absorption_is_conditional

-- Terminal-Ramanujan layer (EP-M2 route below the canonical j = 2 owner)
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.Cutoffs.mem_I1
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.Cutoffs.mem_I2
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.Cutoffs.mem_box
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.Cutoffs.box_pos
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.Cutoffs.box_prod_le
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.lam_zero
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.lam_eq_zero_of_Qmax_lt
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.lam_eq_zero_of_even
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.lam_eq_sum_filter
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.lam_ne_muConv
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.lam_three_wide
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.assembled_bound_does_not_imply_packetwise
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.assembled_zero_with_large_packets
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.divisors_gcd_eq_filter
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ram_eq_ramAlt
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.sum_ram_divisors
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ram_one
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.lam_cast
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.aCoeff_eq_aDiv
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.filter_dvd_eq_divisors
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.Fsum_eq_ramanujan_expansion
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.aCoeff_eq_zero_of_even
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.aCoeff_eq_zero_of_cube_dvd
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.D1_mul_D2
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.moebius_D1_mul_D2
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.moebius_eq_zero_of_not_coprime_cofactor
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.moebius_interval_extraction
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.indDvd_apply
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.isMultiplicative_indDvd
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ind_mul_of_coprime
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.squarefree_dvd_of_primes_dvd
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.isMultiplicative_allocKernel
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.mult_eval_squarefree
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.allocKernel_prime
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.prod_ind_eq
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.allocKernel_eq_triple
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.alloc_indicator
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.q_dvd_iff
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.alloc_indicator_with_b
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.odd_of_dvd_odd
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.term_alloc_expansion
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.aCoeff_cofactor_allocation
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.Fsum_eq_low_add_top
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.Ftop_zero_cutoff
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.Ftop_full_cutoff
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.Flow_eq_sub
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.aCoeff_complementary_quotient
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.aCoeff_sum_over_quotients
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.Ftop_complementary_quotient
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.filter_dvd_top
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.Ftop_large_divisor
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.terminal_small_complement
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.terminal_small_complement_rat
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.Ftop_terminal_support
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.rowOp_add
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.rowOp_arg_pos
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.rowOp_terminal_split
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.moment_split
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.raw_moment_budget
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.moment_eq_top_of_low_zero
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.moment_algebra_does_not_bound
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.scalarBudget_const_mul
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.epM2_of_terminal_parts
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.epM2_needs_terminal_owner
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.j2_of_epM2
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.j2_of_terminal_route
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.dbRaw_budget_of_terminal_route
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.epM2Realisation_load_bearing
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.j2_owner_still_open
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.terminal_owner_still_open
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.chamber_624_in_window
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.chamber_624_lt_five_eighths
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.chamber_621_in_window
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.terminal_factorable_small_complement
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.factorable_structure_does_not_imply_topBound
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.canonical_cut_retained
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.canonical_cut_length_retained
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.tcutSet_r11
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.tcutSet_j2ViaTerminal
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.terminal_nodes_offroute
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.unique_new_bridge
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.terminal_owner_below_j2
