/-
# Gate-1A Δv4 — status ledger and axiom audit

Status codes (as in `Gate1A/Status.lean`):

```
PROVED                 kernel-checked in this project
PROVED_AFTER_REPAIR    kernel-checked after correcting the requested statement
CONDITIONAL_INTERFACE  proved only from explicitly named open hypotheses
OPEN_NOT_ASSUMED       not proved and never assumed
RETRACTED              withdrawn; a countermodel is banked
```

Controlling Δv4 label:

```
GATE1A_CLOSURE_FORMALISED_CONDITIONAL_ON_EXPLICIT_INTERFACES
```

`gate1a_direct_generic_closed_under_frozen_clean_bank` is **absent by
design** (§28): nine items of the exceptional table are still `open_`, and
the flat-profile source legality, the corrected-PB analytic lattice bound and
the `h = 0` firewall bound remain hypotheses.

Every `#print axioms` below must report at most
`propext`, `Classical.choice`, `Quot.sound`.
-/
import Gate1A.Delta4.Scale
import Gate1A.Delta4.RootSource
import Gate1A.Delta4.FlatProfile
import Gate1A.Delta4.S2Upper
import Gate1A.Delta4.RankOne
import Gate1A.Delta4.PBAxis
import Gate1A.Delta4.OuterAxis
import Gate1A.Delta4.Projective
import Gate1A.Delta4.Curvature
import Gate1A.Delta4.RootDepth
import Gate1A.Delta4.Partition
import Gate1A.Delta4.FaceCascade
import Gate1A.Delta4.Interfaces

namespace Gate1A

namespace Delta4

namespace StatusV4

/-! ## §2 / §8 / §14 / §24 scale ledger — PROVED -/

#print axioms Gate1A.Delta4.scale_DH
#print axioms Gate1A.Delta4.scale_RK
#print axioms Gate1A.Delta4.scale_MsqH
#print axioms Gate1A.Delta4.scale_MK
#print axioms Gate1A.Delta4.uInv_over_sqrt_saving_eq_sqrt_M_over_D
#print axioms Gate1A.Delta4.errorRootMargin_eq
#print axioms Gate1A.Delta4.error_root_capacity
#print axioms Gate1A.Delta4.error_root_margin_V1
#print axioms Gate1A.Delta4.error_root_margin_V2
#print axioms Gate1A.Delta4.error_root_margin_V3
#print axioms Gate1A.Delta4.MH_over_Lsq_eq_M_over_D
#print axioms Gate1A.Delta4.MH_over_Lsq_lt_one
#print axioms Gate1A.Delta4.H_over_Lsq_lt_one
#print axioms Gate1A.Delta4.rootDepthMargin_eq
#print axioms Gate1A.Delta4.root_depth_capacity
#print axioms Gate1A.Delta4.root_depth_margin_V1
#print axioms Gate1A.Delta4.root_depth_margin_V2
#print axioms Gate1A.Delta4.root_depth_margin_V3
#print axioms Gate1A.Delta4.both_root_margins_positive

/-! ## §3 / §4 authoritative root source — PROVED -/

#print axioms Gate1A.Delta4.alpha_is_integer
#print axioms Gate1A.Delta4.alpha_range
#print axioms Gate1A.Delta4.archimedean_alpha_bound
#print axioms Gate1A.Delta4.root_phase_m_component_cancels
#print axioms Gate1A.Delta4.root_phase_m_component_cancels_zmod
#print axioms Gate1A.Delta4.root_phase_m_component_cancels_exp

/-! ## §7 / §8 flat profile and root-scale error — PROVED

The *identification* of the actual source profile with the schematic flat
form is CONDITIONAL_INTERFACE (`Delta4OpenInterfaces.flatProfileSourceLegality`). -/

#print axioms Gate1A.Delta4.norm_prod_sub_one_le
#print axioms Gate1A.Delta4.one_add_pow_le
#print axioms Gate1A.Delta4.flat_profile_remainder_le_Uinv
#print axioms Gate1A.Delta4.phase_factor_close_to_one
#print axioms Gate1A.Delta4.amplitude_factor_close_to_one
#print axioms Gate1A.Delta4.error_absorbed_root_scale

/-! ## §9 two-sided S2 — RETRACTED (countermodel PROVED) -/

#print axioms Gate1A.Delta4.l1_control_not_l2_equivalence
#print axioms Gate1A.Delta4.no_two_sided_S2_constant

/-! ## §10 S2-UPPER — PROVED -/

#print axioms Gate1A.Delta4.one_sided_source_transport_l2
#print axioms Gate1A.Delta4.one_sided_source_transport_l2_pi

/-! ## §11 rank-one preservation — PROVED -/

#print axioms Gate1A.Delta4.smooth_pq_separation_preserves_rankOne
#print axioms Gate1A.Delta4.rankOne_nuclear_bound

/-! ## §12 / §14 corrected PB coordinate and axis arithmetic — PROVED -/

#print axioms Gate1A.Delta4.pb_phase_eq_Z_over
#print axioms Gate1A.Delta4.pb_phase_factors_through_Z
#print axioms Gate1A.Delta4.pbRowWeight_depends_only_on_Z_n
#print axioms Gate1A.Delta4.Z_zero_divisibility
#print axioms Gate1A.Delta4.Z_zero_forces_a_zero_n_zero
#print axioms Gate1A.Delta4.Z_zero_needs_both_truncations
#print axioms Gate1A.Delta4.L_zero_dvd_h1
#print axioms Gate1A.Delta4.L_zero_forces_h1_h2_zero
#print axioms Gate1A.Delta4.L_zero_needs_distinct_primes

/-! ## §15 / §16 / §17 outer axis — PROVED_AFTER_REPAIR

The retracted claim "all five local factors are always `-1`" is refuted by
`outer_axis_not_always_minus_one`. -/

#print axioms Gate1A.Delta4.outer_axis_local_factor
#print axioms Gate1A.Delta4.outer_axis_not_always_minus_one
#print axioms Gate1A.Delta4.inner_axis_local_factor_neg_one
#print axioms Gate1A.Delta4.outer_regular_axis_contraction
#print axioms Gate1A.Delta4.outer_axis_plancherel
#print axioms Gate1A.Delta4.outer_true_zero_divisor_bound
#print axioms Gate1A.Delta4.outer_true_zero_is_rank_loss

/-! ## §18 / §19 / §20 / §21 generic projective S3 — PROVED_AFTER_REPAIR

The addendum's product grouping `Z·L` is corrected to the projective ratio;
see `product_class_ne_ratio_class`. -/

#print axioms Gate1A.Delta4.norm_sum_sq_expand
#print axioms Gate1A.Delta4.class_energy_identity
#print axioms Gate1A.Delta4.ratioClass_eq_iff_cross
#print axioms Gate1A.Delta4.product_class_ne_ratio_class
#print axioms Gate1A.Delta4.generic_projective_pushforward_bound
#print axioms Gate1A.Delta4.character_tuple_splits
#print axioms Gate1A.Delta4.character_multiplicative
#print axioms Gate1A.Delta4.projective_sum_over_prime_quadruples_no_extra_tax

/-! ## §22 outer curvature — PROVED -/

#print axioms Gate1A.Delta4.deltaOut_indep_of_moving_prime
#print axioms Gate1A.Delta4.outer_collision_forces_r_dvd_deltaOut
#print axioms Gate1A.Delta4.curvature_divisor_multiplicity
#print axioms Gate1A.Delta4.family_saving_from_multiplicity

/-! ## §24 root depth — PROVED (one root only) -/

#print axioms Gate1A.Delta4.single_cauchy_over_r
#print axioms Gate1A.Delta4.root_depth_assembly
#print axioms Gate1A.Delta4.four_cycle_input

/-! ## §25 clean-block partition — PROVED -/

#print axioms Gate1A.Delta4.classify_total
#print axioms Gate1A.Delta4.classify_curvature
#print axioms Gate1A.Delta4.classify_axisRegular
#print axioms Gate1A.Delta4.classify_axisTrueZero
#print axioms Gate1A.Delta4.classify_firewall
#print axioms Gate1A.Delta4.classify_generic
#print axioms Gate1A.Delta4.classify_disjoint
#print axioms Gate1A.Delta4.classify_sectors_nonvacuous

/-! ## §23 p/q face cascade — NON_LOAD_BEARING_FOR_MAIN_CLEAN_BLOCK -/

#print axioms Gate1A.Delta4.clean_block_bound_without_face_savings
#print axioms Gate1A.Delta4.clean_block_bound_five_sectors
#print axioms Gate1A.Delta4.pq_face_cascade_non_load_bearing

/-! ## §26 / §27 exceptional table and conditional assembly -/

#print axioms Gate1A.Delta4.routingStatus_total
#print axioms Gate1A.Delta4.routingStatus_open_items
#print axioms Gate1A.Delta4.physical_eq_normalized_div_Hsq
#print axioms Gate1A.Delta4.physicalTarget_eq_MDsqH
#print axioms Gate1A.Delta4.gate1a_of_final_interfaces
#print axioms Gate1A.Delta4.gate1a_of_final_interfaces_nonvacuous
#print axioms Gate1A.Delta4.gate1a_interfaces_load_bearing
#print axioms Gate1A.Delta4.delta4_closure_is_conditional

/-! ## §28 — the unconditional theorem is NOT created

There is deliberately no declaration named
`gate1a_direct_generic_closed_under_frozen_clean_bank` anywhere in this
project.  The strongest Δv4 statement is
`Gate1A.Delta4.gate1a_of_final_interfaces`, which carries its open interfaces
as explicit hypotheses. -/

end StatusV4

end Delta4

end Gate1A
