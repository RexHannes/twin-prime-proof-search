import RequestProject.CurrentProgramme.CurrentStatusHighKShift
import RequestProject.CurrentProgramme.EndpointCharacterTransfer

/-!
# Trust audit · high-`k` short-shift bank

`#print axioms` for every principal declaration of the shifted-determinant,
character-transfer, band-kernel and shifted-MAM modules.

Expected: only `propext`, `Classical.choice`, `Quot.sound`.  No `sorry`,
`admit`, `axiom`, `opaque`, `unsafe`, `native_decide` or `@[implemented_by]`
occurs in any file of this bank.

**No analytic or source interface is inhabited:**
`BandKernel.BandKernelLocalizationInput`, `ShiftedMAM.ShiftedMAMFamilyInput`,
`ShiftedMAM.MidKShiftAveragedMAMInput`, `ShiftedMAM.TopKFiniteShiftMAMInput`,
`ShiftedMAM.NativePure5SourceAdapter` — no constructor call anywhere.
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace AuditHighKShift

/-! ## Shifted determinant algebra -/

#print axioms ShiftedDet.shifted_lineDet2
#print axioms ShiftedDet.shiftedDeterminant_eq
#print axioms ShiftedDet.shiftedDeterminant_betaForm
#print axioms ShiftedDet.determinantDefect_phase_identity
#print axioms ShiftedDet.determinantDefect_eq_shift
#print axioms ShiftedDet.shiftedMAM_mod_u
#print axioms ShiftedDet.shiftedMAM_mod_ell
#print axioms ShiftedDet.shiftedDet_zmod
#print axioms ShiftedDet.shiftedMAM_divisorSwitch
#print axioms ShiftedDet.shiftedMAM_prime_solve
#print axioms ShiftedDet.shiftedMAM_solve_v
#print axioms ShiftedDet.shiftedMAM_solve_p

/-! ## Determinant character transfer -/

#print axioms CharTransfer.shiftedDet_character_product
#print axioms CharTransfer.shiftedDet_character_transfer
#print axioms CharTransfer.shiftedMAM_character_transfer_uniform
#print axioms CharTransfer.character_transfer_shift_independent
#print axioms CharTransfer.twoByTwo_character_transfer
#print axioms CharTransfer.twoByTwo_character_transfer_toV
#print axioms CharTransfer.determinantResidue_character_transfer
#print axioms CharTransfer.determinantResidue_iff

/-! ## Band kernel and band-to-shift identity -/

#print axioms BandKernel.dft_pair_expand
#print axioms BandKernel.bandPairing_eq_shiftKernelSum
#print axioms BandKernel.shiftKernelSum_regroup
#print axioms BandKernel.bandPairing_eq_shiftSum
#print axioms BandKernel.zeroShift_survives
#print axioms BandKernel.zeroShift_isolated
#print axioms BandKernel.phaseVariation_alone_does_not_force_decay
#print axioms BandKernel.phaseVariation_counterguard_nonvacuous
#print axioms BandKernel.bandKernelLocalization_budget_nonneg
#print axioms BandKernel.bandKernelLocalization_not_automatic
#print axioms BandKernel.kernelL1_gives_only_trivial_bound

/-! ## Shift ledger -/

#print axioms ShiftLedger.shiftLength_antitone
#print axioms ShiftLedger.FrequencySplit.midK_shift_ge
#print axioms ShiftLedger.FrequencySplit.topK_shift_le
#print axioms ShiftLedger.FrequencySplit.midK_topK_disjoint
#print axioms ShiftLedger.FrequencySplit.midK_topK_exhaustive

/-! ## Shifted MAM packets and sockets -/

#print axioms ShiftedMAM.ShiftedMAMSourceData.shiftedMAM_zero_eq_native
#print axioms ShiftedMAM.nativeAdapter_not_automatic
#print axioms ShiftedMAM.finiteShift_sameArithmeticArchitecture
#print axioms ShiftedMAM.finiteShift_values_may_differ
#print axioms ShiftedMAM.topK_controls_native
#print axioms ShiftedMAM.family_singleton_gives_native
#print axioms ShiftedMAM.shiftedMAMFamilyInput_not_automatic
#print axioms ShiftedMAM.topKInput_not_automatic
#print axioms ShiftedMAM.midKInput_not_automatic

/-! ## Revised all-`k` compilers -/

#print axioms AllKV2.allK_endpoint_compiler_v2
#print axioms AllKV2.allK_endpoint_of_three_sockets
#print axioms AllKV2.topPart_le_of_topKInput
#print axioms AllKV2.allK_operator_compiler
#print axioms AllKV2.bandPairing_is_shift_operator
#print axioms AllKV2.allKV2_not_unconditional
#print axioms AllKV2.allKV2_comparison_not_included
#print axioms AllKV2.pure5Certificate_projections
#print axioms AllKV2.allK_v2_needs_no_frequency_gain

/-! ## Status layer -/

#print axioms LedgerHighKShift.no_closed_rows
#print axioms LedgerHighKShift.ledger_is_honest
#print axioms LedgerHighKShift.gate1B_open
#print axioms LedgerHighKShift.historical_charSquare_row_preserved
#print axioms LedgerHighKShift.frequencyGain_superseded_not_false

end AuditHighKShift
end CurrentProgramme
end TwinPrimeProject
