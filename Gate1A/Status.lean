/-
# Gate-1A §21 / A21: machine-readable status ledger

Status codes used below (exactly as specified):

    PROVED
    PROVED_AFTER_REPAIR
    CONDITIONAL_INTERFACE
    OPEN_NOT_ASSUMED
    RETRACTED

The controlling final label for this project is

    GATE1A_FIXED_QUOTIENT_CORE_FORMALISED

i.e. the finite/algebraic/functional-analytic core is kernel-checked and the
closure theorems are conditional; the source interfaces are **not** derived.
`gate1a_direct_generic_closed` is absent by design.
-/
import Gate1A.Exponents
import Gate1A.MovingFamily
import Gate1A.Countermodels
import Gate1A.Kloosterman
import Gate1A.CRTSign
import Gate1A.CenteredIncidence
import Gate1A.QuotientKernel
import Gate1A.SineDecomposition
import Gate1A.ProjectivePacket
import Gate1A.FourCycle
import Gate1A.ErrorAlgebra
import Gate1A.RankFloor
import Gate1A.HardSupport
import Gate1A.NuclearCountermodels
import Gate1A.ThetaPhase
import Gate1A.Projectors
import Gate1A.PoissonBruhat
import Gate1A.NormedTransport
import Gate1A.QuotientRecombination
import Gate1A.SourceInterfaces
import Gate1A.ConditionalClosure

namespace Gate1A

namespace Status

/-! ## EXPONENT / VERTEX LEDGER — PROVED -/

#check @Gate1A.gate1a_DH_eq_Lsq
#check @Gate1A.gate1a_RK_eq_M
#check @Gate1A.gate1a_MsqH_eq_RLsq
#check @Gate1A.gate1a_H_over_M
#check @Gate1A.gate1a_outer_capacity
#check @Gate1A.gate1a_face_capacity
#check @Gate1A.gate1a_u2_error_capacity
#check @Gate1A.gate1a_u2_margin_v1
#check @Gate1A.gate1a_u2_margin_v2
#check @Gate1A.gate1a_u2_margin_v3
#check @Gate1A.gate1a_outer_margin_v1
#check @Gate1A.gate1a_outer_margin_v2
#check @Gate1A.gate1a_outer_margin_v3
#check @Gate1A.gate1a_face_margin_v1
#check @Gate1A.gate1a_face_margin_v2
#check @Gate1A.gate1a_face_margin_v3
#check @Gate1A.gate1a_projective_exp_v1
#check @Gate1A.gate1a_projective_exp_v2
#check @Gate1A.gate1a_projective_exp_v3

#print axioms Gate1A.gate1a_outer_capacity
#print axioms Gate1A.gate1a_face_capacity
#print axioms Gate1A.gate1a_u2_error_capacity
#print axioms Gate1A.gate1a_projective_exp_v1

/-! ## MOVING-FAMILY INEQUALITY — PROVED -/

#check @Gate1A.moving_family_energy_le
#check @Gate1A.offdiag_energy_le_D_mul_coherence
#print axioms Gate1A.moving_family_energy_le

/-! ## DISJOINT-MOVING-BLOCK COUNTERMODEL — PROVED -/

#check @Gate1A.Countermodel.moving_blocks_counterexample
#check @Gate1A.Countermodel.blockPr_collision_card_le_one
#print axioms Gate1A.Countermodel.moving_blocks_counterexample

/-! ## COMMON-ENVELOPE NORMALIZATION COUNTERMODEL — PROVED -/

#check @Gate1A.Countermodel.common_envelope_not_diagonal_saving
#check @Gate1A.Countermodel.absolute_scale_vs_diagonal_scale_example
#print axioms Gate1A.Countermodel.common_envelope_not_diagonal_saving
#print axioms Gate1A.Countermodel.absolute_scale_vs_diagonal_scale_example

/-! ## KLOOSTERMAN SIGN INVOLUTION / AXES / LOCAL CORRELATION — PROVED -/

#check @Gate1A.Kloosterman.kloosterman_neg_neg
#check @Gate1A.Kloosterman.kloosterman_zero_zero
#check @Gate1A.Kloosterman.kloosterman_axis_left
#check @Gate1A.Kloosterman.kloosterman_axis_right
#check @Gate1A.Kloosterman.kloosterman_local_correlation
#print axioms Gate1A.Kloosterman.kloosterman_neg_neg
#print axioms Gate1A.Kloosterman.kloosterman_local_correlation

/-! ## SIDE-2 NEGATIVE CROSS-q ARGUMENT — PROVED
    OLD PLUS/PLUS SIDE-2 FORM — RETRACTED (refuted by an explicit witness) -/

#check @Gate1A.CRTSign.crt_side2_inverse_negative
#check @Gate1A.CRTSign.cross_q_side2_negative
#check @Gate1A.CRTSign.old_plus_plus_cross_q_false
#print axioms Gate1A.CRTSign.cross_q_side2_negative
#print axioms Gate1A.CRTSign.old_plus_plus_cross_q_false

/-! ## ONE-q CENTERED DUAL-LIFT INCIDENCE — PROVED (all modes, incl. b = 0) -/

#check @Gate1A.CenteredIncidence.dualLift_zero_mode
#check @Gate1A.CenteredIncidence.centered_dual_lift_incidence
#print axioms Gate1A.CenteredIncidence.centered_dual_lift_incidence

/-! ## QUOTIENT KERNEL EXACT NONZERO FORMULA + h = 0 FIREWALL — PROVED -/

#check @Gate1A.QuotientKernel.quotient_kernel_exact_nonzero
#check @Gate1A.QuotientKernel.quotient_kernel_zero_mode
#print axioms Gate1A.QuotientKernel.quotient_kernel_exact_nonzero
#print axioms Gate1A.QuotientKernel.quotient_kernel_zero_mode

/-! ## EXACT SINE DECOMPOSITION + QUADRATIC SINE-RATIO ERROR — PROVED -/

#check @Gate1A.SineDecomposition.sine_ratio_exact
#check @Gate1A.SineDecomposition.sine_ratio_quadratic_error
#print axioms Gate1A.SineDecomposition.sine_ratio_exact
#print axioms Gate1A.SineDecomposition.sine_ratio_quadratic_error

/-! ## PROJECTIVE CROSSED-CONVOLUTION — PROVED_AFTER_REPAIR
    (the informal inner-product ordering was repaired to Mathlib's
     conjugate-linear-in-the-first-slot convention) -/

#check @Gate1A.ProjectivePacket.projective_crossed_convolution
#check @Gate1A.ProjectivePacket.projective_energy_le_of_factorMultiplicity
#print axioms Gate1A.ProjectivePacket.projective_crossed_convolution
#print axioms Gate1A.ProjectivePacket.projective_energy_le_of_factorMultiplicity

/-! ## OUTER FOUR-CYCLE — PROVED (as an exact identity, both layers) -/

#check @Gate1A.FourCycle.outer_four_cycle_trace
#check @Gate1A.FourCycle.outer_four_cycle_matrix
#check @Gate1A.FourCycle.outer_four_cycle_operator
#print axioms Gate1A.FourCycle.outer_four_cycle_matrix
#print axioms Gate1A.FourCycle.outer_four_cycle_operator

/-! ## ERROR CROSS-TERM ALGEBRA (ROOT DEPTH) — PROVED
    Route A (theta EXACTLY RETAINED) and Route B (theta DISCARDED WITH U⁻¹)
    are both recorded, and both are admissible on the frozen polytope. -/

#check @Gate1A.ErrorAlgebra.square_norm_add_error
#check @Gate1A.ErrorAlgebra.error_absorbed_of_le_sqrtSaving
#check @Gate1A.ErrorAlgebra.route_A_theta_retained_admissible
#check @Gate1A.ErrorAlgebra.route_B_theta_discarded_admissible
#print axioms Gate1A.ErrorAlgebra.square_norm_add_error
#print axioms Gate1A.ErrorAlgebra.error_absorbed_of_le_sqrtSaving

/-! ## POINTWISE RANK-SCHATTEN — PROVED (Layer A **and** Layer B) -/

#check @Gate1A.RankFloor.rank_floor_from_pointwise_hs
#check @Gate1A.RankFloor.rank_floor_hs_of_rank_le
#check @Gate1A.RankFloor.rank_floor_symbolic_new
#print axioms Gate1A.RankFloor.rank_floor_from_pointwise_hs
#print axioms Gate1A.RankFloor.rank_floor_hs_of_rank_le

/-! ## HARD-SUPPORT FINITE EXCLUSION — PROVED FOR LISTED UNIT CONDITIONS -/

#check @Gate1A.HardSupport.at_most_one_moving_r_bad
#check @Gate1A.HardSupport.moving_r_bad_of_nu_zero_independent
#print axioms Gate1A.HardSupport.at_most_one_moving_r_bad

/-! ## A5 / A10 NUCLEAR-SCALE COUNTERMODELS — PROVED -/

#check @Gate1A.NuclearCountermodels.uniform_row_smoothness_not_nuclear_transport
#check @Gate1A.NuclearCountermodels.scalar_l1_mass_not_operator_norm
#print axioms Gate1A.NuclearCountermodels.uniform_row_smoothness_not_nuclear_transport
#print axioms Gate1A.NuclearCountermodels.scalar_l1_mass_not_operator_norm

/-! ## A7 THETA-PHASE NUCLEAR SEPARATION — PROVED -/

#check @Gate1A.ThetaPhase.theta_phase_separated
#check @Gate1A.ThetaPhase.theta_phase_nuclear_cost
#check @Gate1A.ThetaPhase.theta_phase_tail_bound_simple
#print axioms Gate1A.ThetaPhase.theta_phase_nuclear_cost
#print axioms Gate1A.ThetaPhase.theta_phase_tail_bound_simple

/-! ## A12 CENTERED LOCAL PROJECTORS — PROVED -/

#check @Gate1A.Projectors.centered_posSemidef
#check @Gate1A.Projectors.centered_le
#check @Gate1A.Projectors.subProjector_le
#print axioms Gate1A.Projectors.centered_posSemidef

/-! ## A9 POISSON–BRUHAT NORMALISATION (exponent layer) — PROVED
    The Schwartz lattice ℓ¹ bound and the operator bound are
    CONDITIONAL_INTERFACE (fields of `Gate1AAnalyticInterfaces`). -/

#check @Gate1A.PoissonBruhat.pb_normalisation_one
#check @Gate1A.PoissonBruhat.pb_normalisation_two
#print axioms Gate1A.PoissonBruhat.pb_normalisation_two

/-! ## NORMED SOURCE TRANSPORT (abstract) — PROVED
    NUCLEAR PROJECTIVE ABSTRACT BOUND — PROVED
    The corresponding *source* statements are CONDITIONAL_INTERFACE. -/

#check @Gate1A.NormedTransport.normed_transported_curvature
#check @Gate1A.NormedTransport.nuclear_projective_pushforward_bound
#print axioms Gate1A.NormedTransport.normed_transported_curvature
#print axioms Gate1A.NormedTransport.nuclear_projective_pushforward_bound

/-! ## SCHWARTZ POISSON RECOMBINATION
    Exact Poisson summation: PROVED (from Mathlib, in Mathlib's convention).
    The affine Fourier dictionary and the quantitative alias/wrap bounds:
    CONDITIONAL_INTERFACE — never `sorry`. -/

#check @Gate1A.QuotientRecombination.exact_poisson
#check @Gate1A.QuotientRecombination.quotient_recombination_of_dictionary
#check @Gate1A.QuotientRecombination.QuotientRecombinationEstimate
#check @Gate1A.QuotientRecombination.total_close_to_main
#print axioms Gate1A.QuotientRecombination.exact_poisson
#print axioms Gate1A.QuotientRecombination.quotient_recombination_of_dictionary
#print axioms Gate1A.QuotientRecombination.total_close_to_main

/-! ## SOURCE INTERFACES — CONDITIONAL_INTERFACE / OPEN_NOT_ASSUMED

POST-ν EXACT SOURCE COEFFICIENT      : CONDITIONAL_INTERFACE
Φ_flat FULL CENSUS                   : CONDITIONAL_INTERFACE
POST-ν G_i COORDINATE DICTIONARY     : CONDITIONAL_INTERFACE
TRANSFORM ORDER                      : CONDITIONAL_INTERFACE
ACTUAL NORMED SOURCE TRANSPORT       : CONDITIONAL_INTERFACE
ACTUAL PROJECTIVE SOURCE PUSHFORWARD : CONDITIONAL_INTERFACE
r-LOCAL TRUE-ZERO / CONDUCTOR ROUTING: CONDITIONAL_INTERFACE
RECOMBINED DOMAIN                    : CONDITIONAL_INTERFACE

No term of any of these structures is constructed anywhere in the project. -/

#check @Gate1A.SourceInterfaces.Gate1ASourceInterfaces
#check @Gate1A.SourceInterfaces.Gate1AAnalyticInterfaces
#check @Gate1A.SourceInterfaces.S1FiveFaceIntertwiner
#check @Gate1A.SourceInterfaces.S2TF4Normalisation
#check @Gate1A.SourceInterfaces.S3ProjectivePushforward

/-! ## GATE1A DIRECT GENERIC — CONDITIONAL ONLY
    UNCONDITIONAL GATE1A CLOSED — NOT PRESENT -/

#check @Gate1A.ConditionalClosure.gate1a_conditional_closure
#check @Gate1A.ConditionalClosure.gate1a_direct_generic_of_interfaces
#check @Gate1A.ConditionalClosure.gate1a_candidate_closed_of_fixed_quotient_interfaces
#check @Gate1A.ConditionalClosure.gate1a_of_S1_S2_S3
#check @Gate1A.ConditionalClosure.gate1a_fixed_quotient_core

#print axioms Gate1A.ConditionalClosure.gate1a_conditional_closure
#print axioms Gate1A.ConditionalClosure.gate1a_direct_generic_of_interfaces
#print axioms Gate1A.ConditionalClosure.gate1a_candidate_closed_of_fixed_quotient_interfaces
#print axioms Gate1A.ConditionalClosure.gate1a_of_S1_S2_S3
#print axioms Gate1A.ConditionalClosure.gate1a_fixed_quotient_core

end Status

end Gate1A
