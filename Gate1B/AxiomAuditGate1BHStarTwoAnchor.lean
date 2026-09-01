import Gate1B.CurrentStatusGate1BHStarTwoAnchor

/-!
# Gate 1B · axiom audit for the HSTAR two-anchor safe bank

`#print axioms` for every principal public theorem of the modules

* `Gate1B.HStarTwoAnchorPhysicalSource`
* `Gate1B.HStarTwoAnchorDifferenceAlgebra`
* `Gate1B.HStarTwoAnchorCounterguards`
* `Gate1B.HStarOneTTwoTFirewall`
* `Gate1B.HStarCenteredAdditiveProjector`
* `Gate1B.HStarHZeroFiniteRouter`
* `Gate1B.HStarMobiusPrimeSource`
* `Gate1B.HStarAnchorPreservingCovariance`
* `Gate1B.HStarAnchorPreservingAnalyticInterface`
* `Gate1B.CurrentStatusGate1BHStarTwoAnchor`

Only the standard foundations `propext`, `Classical.choice` and `Quot.sound`
may appear.  There is no `sorry`, no `sorryAx`, no custom `axiom`, no
`native_decide`, no `implemented_by`, no `unsafe` and no `opaque` shortcut
anywhere in this bank.
-/

namespace TwinPrimeProject
namespace CurrentProgramme

open TwinPrimeProject.CurrentProgramme.HStarTwoAnchor
open TwinPrimeProject.CurrentProgramme.HStarCentered
open TwinPrimeProject.CurrentProgramme.HStarHZero
open TwinPrimeProject.CurrentProgramme.HStarMobiusPrime
open TwinPrimeProject.CurrentProgramme.HStarAnchorCovariance
open TwinPrimeProject.CurrentProgramme.HStarAnchorInterface

-- HStarTwoAnchorPhysicalSource
#print axioms HStarTwoAnchorSource.anchor1Z
#print axioms HStarTwoAnchorSource.anchor2Z
#print axioms HStarTwoAnchorSource.defect1_eq_two
#print axioms HStarTwoAnchorSource.defect2_eq_two
#print axioms HStarTwoAnchorSource.defect1_eq_defect2
#print axioms HStarTwoAnchorSource.q1_pos
#print axioms HStarTwoAnchorSource.q2_pos
#print axioms HStarTwoAnchorSource.q1_dvd
#print axioms HStarTwoAnchorSource.q2_dvd
#print axioms HStarTwoAnchorSource.g_dvd_q1
#print axioms HStarTwoAnchorSource.g_dvd_q2
#print axioms hStarTwoAnchorSource_nonempty

-- HStarTwoAnchorDifferenceAlgebra
#print axioms TwoTRawConfig.anchor1_iff_defect1
#print axioms TwoTRawConfig.anchor2_iff_defect2
#print axioms TwoTRawConfig.hnum_eq_g_mul_quotDiff
#print axioms TwoTRawConfig.anchors_imply_difference_system
#print axioms TwoTRawConfig.hnum_eq_iff_quotDiff_eq
#print axioms TwoTRawConfig.twoAnchor_iff_differenceSystem_with_anchor
#print axioms TwoTRawConfig.anchor2_of_differences_and_anchor1
#print axioms HStarTwoAnchorSource.toRaw_anchor1
#print axioms HStarTwoAnchorSource.toRaw_anchor2
#print axioms HStarTwoAnchorSource.toRaw_g_ne_zero
#print axioms HStarTwoAnchorSource.physical_difference_system
#print axioms HStarTwoAnchorSource.physical_hnum_iff_quotDiff

-- HStarTwoAnchorCounterguards
#print axioms TwoTRawConfig.differenceSystem_implies_common_defect
#print axioms defectCountermodel_positive
#print axioms defectCountermodel_differenceSystem
#print axioms defectCountermodel_defects
#print axioms differenceSystem_does_not_imply_physicalAnchors
#print axioms differenceSystem_does_not_imply_defect_two
#print axioms AFactor_mul_BFactor_ne_zero_iff
#print axioms independentH_product_implies_common_defect
#print axioms independentHEnergy_not_physicalSource
#print axioms independentHEnergy_does_not_imply_anchors
#print axioms TwoTRawConfig.singleLineDelta_iff_common_defect
#print axioms singleLineDelta_strictly_weaker

-- HStarOneTTwoTFirewall
#print axioms OneT.oneT_prime_congruence
#print axioms OneT.oneT_length_relation
#print axioms OneT.oneT_rigidity
#print axioms twoT_congruence
#print axioms twoT_congruence_does_not_imply_prime_congruence
#print axioms no_prime_congruence_from_twoT_source
#print axioms sumV_mul_conj_eq_twoTExactSquare
#print axioms sumV_norm_sq_le_majorant
#print axioms oneTCauchyMajorant_ne_twoTExactSquare
#print axioms majorant_does_not_determine_exactSquare

-- HStarCenteredAdditiveProjector
#print axioms ramanujanSum_zero
#print axioms totient_cast_ne_zero
#print axioms unitPrincipal_total_mass
#print axioms centeredProjector_total_mass_zero
#print axioms centeredFourier_zero_eq_zero
#print axioms eM_zero_sub_ramanujanSum_zero_div_totient
#print axioms centeredFourier_eq_ramanujan_form
#print axioms twoCopyMode_eq_zero_of_second_zero
#print axioms centered_twoCopyMode_zero_zero
#print axioms four_signed_pieces_cancel
#print axioms centered_four_pieces_cancel

-- HStarHZeroFiniteRouter
#print axioms cross_dvd_of_coprime
#print axioms hZero_impossible_of_short_length
#print axioms hZero_impossible_of_short_lengths
#print axioms hZeroOffDiagonalCell_impossible
#print axioms not_nonempty_hZeroOffDiagonalCell
#print axioms hZero_two_anchor_source_impossible

-- HStarMobiusPrimeSource
#print axioms CleanSquarefreeCell.coprime_d_wp
#print axioms CleanSquarefreeCell.moebius_q
#print axioms moebius_common_g_cancel
#print axioms no_cancellation_in_residual_moebius
#print axioms primeRole_ford_ne_vaughan
#print axioms value_does_not_determine_role
#print axioms vaughan_not_dvd_g_of_gt
#print axioms no_cross_incidence
#print axioms lambdaSharp_support
#print axioms norm_lambdaSharp_le
#print axioms lambdaSharp_cauchy
#print axioms opened_shift_equation
#print axioms lambdaSharp_not_identically_zero
#print axioms shift_bound_of_interface

-- HStarAnchorPreservingCovariance
#print axioms residue1_eq_neg_two
#print axioms residue2_eq_neg_two
#print axioms covariance_evaluated_at_neg_two
#print axioms factor1_eq
#print axioms factor2_eq
#print axioms norm_familyCovariance_le
#print axioms toRaw_defect_eq_two
#print axioms covariance_source_not_freeHLine

-- HStarAnchorPreservingAnalyticInterface
#print axioms unitPrincipal_of_unit
#print axioms centeredProjector_at_unit
#print axioms centeredProjector_neg_two_ne_zero
#print axioms single_source_bound
#print axioms scaled_family_bound
#print axioms fm722_sourceClass_has_four_ingredients
#print axioms fm722_sourceClass_nodup
#print axioms fm722_bound_of_target

-- CurrentStatusGate1BHStarTwoAnchor
#print axioms LedgerGate1BHStarTwoAnchor.no_closed_rows
#print axioms LedgerGate1BHStarTwoAnchor.ledger_is_honest
#print axioms LedgerGate1BHStarTwoAnchor.current_research_frontier
#print axioms LedgerGate1BHStarTwoAnchor.global_gate1B_open
#print axioms LedgerGate1BHStarTwoAnchor.twin_prime_open
#print axioms LedgerGate1BHStarTwoAnchor.interfaces_open
#print axioms LedgerGate1BHStarTwoAnchor.new_exact_rows_kernel_proved
#print axioms LedgerGate1BHStarTwoAnchor.v13_provider_retired_not_refuted
#print axioms LedgerGate1BHStarTwoAnchor.previous_layer_preserved

end CurrentProgramme
end TwinPrimeProject
