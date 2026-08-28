import RequestProject.CurrentProgramme.CurrentStatusShiftedMAMOperator
import RequestProject.CurrentProgramme.AxiomAuditHighKShift

/-!
# Trust audit · shifted-MAM operator bank

`#print axioms` for every principal declaration of the source-minimal
character-pairing module, the shifted-MAM fivefold operator socket, the revised
all-`k` compiler and the operator status ledger.

Expected: only `propext`, `Classical.choice`, `Quot.sound` (or a subset).  No
`sorry`, `admit`, `axiom`, `opaque`, `unsafe`, `native_decide` or
`@[implemented_by]` occurs in any file of this bank.

**No analytic or source interface is inhabited.**  The uninhabited structures of
this layer are

* `CharPairing.FiveDefectResidueSourceAdapter` (source),
* `MAMOperator.ShiftedMAMFivefoldOperatorInput` (analytic frontier),
* `AllKV2.Pure5EndpointCertificateInput` (assembled conditional certificate),

together with the previously banked
`ShiftedMAM.NativePure5SourceAdapter`, `ShiftedMAM.ShiftedMAMFamilyInput`,
`ShiftedMAM.MidKShiftAveragedMAMInput`, `ShiftedMAM.TopKFiniteShiftMAMInput`,
`BandKernel.BandKernelLocalizationInput`,
`BetaSource.BetaDPPhysicalSourceAdapter` and
`CharSquareSocket.EndpointCharTwistedFactorModSquareInput`.
None of these has a constructor call anywhere in the repository; each carries an
explicit `*_not_automatic` non-vacuity theorem instead.
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace AuditMAMOperator

/-! ## Source-minimal character pairing -/

#print axioms CharPairing.residue_fibre
#print axioms CharPairing.residueSource_eq
#print axioms CharPairing.AHat_eq
#print axioms CharPairing.fiveDefectAdapter_not_automatic
#print axioms CharPairing.fullCharacterPairing
#print axioms CharPairing.centeredPairing_eq_nonprincipalCharacterPairing
#print axioms CharPairing.squareBundle_nonneg
#print axioms CharPairing.characterSquare_is_Cauchy_strengthening

/-! ## Shifted-MAM fivefold operator socket -/

#print axioms MAMOperator.Csharp_add_local
#print axioms MAMOperator.PhysicalShiftKernel.l1Budget_nonneg
#print axioms MAMOperator.operator_trivial_bound
#print axioms MAMOperator.operator_controls_native
#print axioms MAMOperator.operatorInput_budget_nonneg
#print axioms MAMOperator.operatorInput_not_automatic
#print axioms MAMOperator.betaMultiplier_not_sourceDecoupled
#print axioms MAMOperator.motohashi_dictionary_slot_mismatch

/-! ## Revised all-`k` compiler -/

#print axioms AllKV2.allK_endpoint_compiler_v2
#print axioms AllKV2.smallPart_le_of_charSquareInput
#print axioms AllKV2.midPart_le_of_midKInput
#print axioms AllKV2.topPart_le_of_topKInput
#print axioms AllKV2.allK_endpoint_of_three_sockets
#print axioms AllKV2.allK_operator_compiler
#print axioms AllKV2.bandPairing_is_shift_operator
#print axioms AllKV2.allKV2_not_unconditional
#print axioms AllKV2.allKV2_comparison_not_included
#print axioms AllKV2.pure5Certificate_projections
#print axioms AllKV2.allK_v2_needs_no_frequency_gain

/-! ## Operator status ledger -/

#print axioms LedgerMAMOperator.no_closed_rows
#print axioms LedgerMAMOperator.ledger_is_honest
#print axioms LedgerMAMOperator.gate1B_open
#print axioms LedgerMAMOperator.current_analytic_frontier
#print axioms LedgerMAMOperator.charSquare_superseded_not_false
#print axioms LedgerMAMOperator.historical_highk_row_preserved
#print axioms LedgerMAMOperator.end_of_run_nonclaims

end AuditMAMOperator
end CurrentProgramme
end TwinPrimeProject
