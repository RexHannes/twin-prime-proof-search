/-
# Gate1B / R11 / Frontier / … / ReciprocityBG / JCore : axiom audit  (J13)

`#print axioms` for every principal theorem of the JCORE layer and of the EP-M2 row
identification.  Each one must report only a subset of `propext`, `Classical.choice`,
`Quot.sound`.  No custom axiom, no `sorry`, no `admit`, no `native_decide`, no `unsafe`, no
`opaque`, no `@[implemented_by]` occurs in this directory.
-/
import Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.JCore.Firewall
import Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.RowFixture

open Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG
open Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.JCore

-- EP-M2 row identification (B13)
#print axioms rowCoefficientIdentification
#print axioms pairIdx_injective
#print axioms canonicalRowKernel_pairIdx
#print axioms canonicalRowKernel_eq_ramRow
#print axioms rowData_indexSet
#print axioms rowData_chartInjectivity
#print axioms rowData_mask
#print axioms rowData_sourceSupport
#print axioms rowData_sourceWeight
#print axioms rowData_normalisation
#print axioms rowData_rowIdentification
#print axioms rowData_epM2Realisation
#print axioms epM2RowIdentification_rowDataClosed
#print axioms epM2Realisation_rowDataClosed
#print axioms rowDataClosed_epM2Family_eq
#print axioms rowDataClosed_ne_zero
#print axioms j2_of_epM2Bound_rowDataClosed
#print axioms j2_of_terminal_parts_rowDataClosed
#print axioms attachment_closes_no_owner

-- JCore : Core (J1)
#print axioms JCore.den_pos
#print axioms JCore.masks_do_not_give_cross_coprimality
#print axioms JCore.jMoment_eq_jExpand

-- JCore : RationalFrequency (J2)
#print axioms JCore.freq_eq_iff_cross
#print axioms JCore.equalRationalFrequency_iff
#print axioms JCore.equalRationalFrequency_of_same_product
#print axioms JCore.equalFrequency_distinct_factorisations
#print axioms JCore.signed_frequencies_distinguished

-- JCore : Determinant (J3)
#print axioms JCore.lcmPart_eq
#print axioms JCore.aPart_coprime_bPart
#print axioms JCore.freq_sub_eq_delta_div
#print axioms JCore.delta_eq_zero_iff
#print axioms JCore.delta_ne_zero_of_unequal

-- JCore : MomentSplit (J4)
#print axioms JCore.jExpand_split
#print axioms JCore.jOff_support_delta
#print axioms JCore.deleting_terms_not_monotone

-- JCore : CleanSupport (J5)
#print axioms JCore.cleanSupport_coprime_left
#print axioms JCore.cleanSupport_coprime_right
#print axioms JCore.cleanSupport_not_automatic
#print axioms JCore.jOff_clean_split
#print axioms JCore.jExpand_three_way

-- JCore : CrossPhase (J6)
#print axioms JCore.isInverseMod_unique
#print axioms JCore.sourcePhase_congr
#print axioms JCore.crtPhase_congr
#print axioms JCore.detPhase_eq_freq_diff
#print axioms JCore.detPhase_ne_zero
#print axioms JCore.crossPhase_factorisation
#print axioms JCore.crossPhase_factorisation_mod1
#print axioms JCore.crossPhase_without_cross_coprimality

-- JCore : Conductor (J7)
#print axioms JCore.sourcePhase_lower
#print axioms JCore.sourcePhase_gcd_lower
#print axioms JCore.ee_sourcePhase_lower
#print axioms JCore.crtPhase_lower
#print axioms JCore.ee_intCast
#print axioms JCore.ee_pow
#print axioms JCore.ee_eq_one_iff
#print axioms JCore.sum_period

-- JCore : CombinedConductor (J8)
#print axioms JCore.exists_crt_shift
#print axioms JCore.combine_two_phases
#print axioms JCore.combined_conductor_shifted
#print axioms JCore.ee_combined_conductor
#print axioms JCore.smallLabel_shift
#print axioms JCore.combinedConductorRealisation_of_common_residue

-- JCore : FactorisationData (J9)
#print axioms JCore.QEffFactorisation.modulus_eq
#print axioms JCore.QEffFactorisation.cop_src_corePart
#print axioms JCore.QEffFactorisation.modulus_pos
#print axioms JCore.QEffFactorisation.src_dvd
#print axioms JCore.QEffFactorisation.corePart_dvd
#print axioms JCore.cleanSupport_gives_block_coprimality

-- JCore : Owners (J10)
#print axioms JCore.jCoreOffBound_of_clean_and_overlap
#print axioms JCore.jCoreBound_of_owners
#print axioms JCore.jCoreOffCleanBound_open
#print axioms JCore.sourceCoreOverlapBudget_open
#print axioms JCore.jCoreEqualBudget_open
#print axioms JCore.jCore_needs_clean_owner

-- JCore : Bridge (J11)
#print axioms JCore.epM2TopBound_of_jCore
#print axioms JCore.epM2Bound_of_jCore_owners
#print axioms JCore.j2_of_jCore_route
#print axioms JCore.jCoreMomentRealisation_load_bearing
#print axioms JCore.jCore_route_closes_no_owner

-- JCore : Firewall (J12)
#print axioms JCore.ee_eq_iff_congMod1
#print axioms JCore.second_factor_not_determined_by_source
#print axioms JCore.jCore_algebra_implies_no_budget
#print axioms JCore.delta_nonvanishing_is_not_a_bound
#print axioms JCore.jCore_non_claims

-- EP-M2 row fixture (B14)
#print axioms lam_fix_one
#print axioms lam_fix_two
#print axioms lam_fix_three
#print axioms lam_fix_four
#print axioms Fsum_fix_three
#print axioms Fsum_fix_four
#print axioms divRow_fix
#print axioms divRow_fix_one
#print axioms divRow_fix_two
#print axioms rowCentering_fix
#print axioms rowDataClosed_fix_ne_zero
#print axioms rowDataClosed_fix_value
