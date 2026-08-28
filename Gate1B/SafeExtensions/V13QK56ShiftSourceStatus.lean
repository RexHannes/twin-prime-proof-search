/-
# Gate 1B v13 — axiom audit and status

**Status: audit module.**  Every principal v13 theorem is passed through
`#print axioms`.  The expected output for each is the standard triple
`[propext, Classical.choice, Quot.sound]`; no user axiom, no `sorry`, no
`native_decide`, no unsafe escape hatch is used anywhere in the v13 bank.
-/
import Gate1B.SafeAlgebra.SameQDiscrepancyCapacity
import Gate1B.SafeAlgebra.CrossQThetaFibre
import Gate1B.SafeExtensions.V13Counterguards

namespace Gate1B.SafeExtensions.V13Status

/-! ### Same-`q` character Gram -/

#print axioms Gate1B.SafeAlgebra.sameQGram_split
#print axioms Gate1B.SafeAlgebra.sameQGramDiag_eq
#print axioms Gate1B.SafeAlgebra.sameQGramDiag_eq_zero_of_centred
#print axioms Gate1B.SafeAlgebra.sameQGramDiag_ne_zero_of_flat_kernel

/-! ### Product-residue character kernel -/

#print axioms Gate1B.SafeAlgebra.MulCharSystem.kernel_eq_sum_productResidue
#print axioms Gate1B.SafeAlgebra.MulCharSystem.centredKernel_fourier_eq
#print axioms Gate1B.SafeAlgebra.MulCharSystem.centredKernel_convolution_eigen
#print axioms Gate1B.SafeAlgebra.MulCharSystem.centredSpectralRadius_isGreatest

/-! ### Same-`q` routers and discrepancy -/

#print axioms Gate1B.SafeExtensions.sameQGramDiag_bound_of_input
#print axioms Gate1B.SafeExtensions.sameQDiagonalResidueEnergyInput_not_vacuous
#print axioms Gate1B.SafeExtensions.centredKernel_norm_le_of_discrepancy
#print axioms Gate1B.SafeExtensions.sameQGramOff_bound_of_kernel_bound
#print axioms Gate1B.SafeExtensions.sameQGramOff_bound_of_discrepancy
#print axioms Gate1B.SafeExtensions.modularHyperbolaDiscrepancyInput_not_vacuous

/-! ### Capacity arithmetic and fibre counting -/

#print axioms Gate1B.SafeAlgebra.discrepancy_relative_exponent
#print axioms Gate1B.SafeAlgebra.relative_exponent_in_X
#print axioms Gate1B.SafeAlgebra.sameQ_capacity_margin
#print axioms Gate1B.SafeAlgebra.card_residue_class_in_interval
#print axioms Gate1B.SafeAlgebra.card_residue_class_in_interval_rat
#print axioms Gate1B.SafeAlgebra.maxThetaFibre_le

/-! ### Cross-`q` Θ spread -/

#print axioms Gate1B.SafeExtensions.crossL2_sq_le_maxFibre_mul_l1
#print axioms Gate1B.SafeExtensions.crossL1_le_states_mul_maxFibre
#print axioms Gate1B.SafeExtensions.crossL2_le_crossL1
#print axioms Gate1B.SafeExtensions.crossQ_spread_criterion
#print axioms Gate1B.SafeExtensions.crossQThetaSourceMassCertificate_of_multiplicity
#print axioms Gate1B.SafeExtensions.crossQThetaSourceMassCertificate_not_vacuous

/-! ### QK5/6 conditional closure and V10 bridge -/

#print axioms Gate1B.SafeExtensions.qk56_full_covariance_of_v13_inputs
#print axioms Gate1B.SafeExtensions.v13_to_v10AnalyticLeaves
#print axioms Gate1B.SafeExtensions.qk56_v13_conclusion_not_automatic
#print axioms Gate1B.SafeExtensions.v13LeafBundle_not_automatic

/-! ### Literal shifted TT\* source and SHAPE metadata -/

#print axioms Gate1B.SafeExtensions.shiftMult4CharacterMoment_eq_linked
#print axioms Gate1B.SafeExtensions.shiftSourceLinkedCharacterMoment_empty
#print axioms Gate1B.SafeExtensions.shiftSourceLinkedCharacterBound_not_vacuous
#print axioms Gate1B.SafeExtensions.monomialShape_of_determinantShape
#print axioms Gate1B.SafeExtensions.fourCycle_det_determinantShape
#print axioms Gate1B.SafeExtensions.fourCycle_trace_not_determinantShape

/-! ### High-`p₃` packet dictionary and weight-dependence compiler -/

#print axioms Universal.SafeExtensions.common_weight_constant
#print axioms Universal.SafeExtensions.edgeDependent_not_constant
#print axioms Universal.SafeAlgebra.packetSum_common
#print axioms Universal.SafeAlgebra.packetSum_finiteTemplate
#print axioms Universal.SafeAlgebra.packetSum_edgeDependent_le
#print axioms Universal.SafeAlgebra.edgeDependent_not_absorbed_by_common

/-! ### FM → Gate census -/

#print axioms Gate1B.SafeExtensions.census_slots_generated
#print axioms Gate1B.SafeExtensions.census_requires_fordProvenance
#print axioms Gate1B.SafeExtensions.census_requires_packetDictionary

/-! ### Counterguards A–H -/

#print axioms Gate1B.SafeExtensions.v13_guardA_diagonal_not_negligible
#print axioms Gate1B.SafeExtensions.v13_guardB_discrepancy_not_vacuous
#print axioms Gate1B.SafeExtensions.v13_guardC_l2_eq_l1_possible
#print axioms Gate1B.SafeExtensions.v13_guardD_edgeDependent_not_common
#print axioms Gate1B.SafeExtensions.v13_guardE_fourCopies_ne_fourParameters
#print axioms Gate1B.SafeExtensions.v13_guardF_conditional_is_not_closure
#print axioms Gate1B.SafeExtensions.v13_guardG_census_source_blocked
#print axioms Gate1B.SafeExtensions.v13_guardH_shape_not_transportable

end Gate1B.SafeExtensions.V13Status
