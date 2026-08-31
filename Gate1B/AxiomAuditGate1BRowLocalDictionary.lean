import Gate1B.Gate1BLeaf4FormalLocalTree
import Gate1B.Gate1BLeaf4RowLocalStatus
import Gate1B.Gate1BPhysicalRowLocalDictionaryInterface
import Gate1B.CurrentStatusGate1BRowLocalDictionary

/-!
# Gate 1B · axiom audit for the row-local dictionary safe bank

`#print axioms` for every principal declaration added by this append-only
delta.  The expected output for each is a subset of
`{propext, Classical.choice, Quot.sound}`; there is no `sorryAx`, no new custom
axiom, no `unsafe`, no `opaque` proof shortcut, no `implemented_by` and no
`native_decide` anywhere in the delta.

Conditional interface theorems (`leaf4_closed_of_physical_dictionary`,
`hZeroHighHigh_closed_of_local_dictionary`) depend only on hypotheses supplied
as explicit arguments.
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace AxiomAuditGate1BRowLocalDictionary

open TwinPrimeProject.CurrentProgramme.Gate1BRowLocal
open TwinPrimeProject.CurrentProgramme.LedgerGate1BRowLocalDictionary

/-! ## 1. Bézout-row and product-difference arithmetic (unconditional) -/

#print axioms aRow
#print axioms bRow
#print axioms bezoutRow_det_invariant
#print axioms scaledBezoutRow_det_invariant
#print axioms gate1B_leaf4_productDifference
#print axioms gate1B_leaf4_productDifference_shift

/-! ## 2. Dirichlet / additive convolution firewall -/

#print axioms DirichletConv.dmul
#print axioms DirichletConv.dmul_apply
#print axioms DirichletConv.dmul_assoc
#print axioms DirichletConv.dmul_comm
#print axioms AdditiveConv.aconv
#print axioms AdditiveConv.aconv_apply
#print axioms dirichlet_ne_additive_conv

/-! ## 3. Noncommutative major-tree interface -/

#print axioms MajorTreeInterface
#print axioms MajorTreeInterface.alphaComp
#print axioms MajorTreeInterface.gammaLocComp
#print axioms MajorTreeInterface.localComp
#print axioms MajorTreeInterface.slots
#print axioms MajorTreeInterface.slots_length
#print axioms MajorTreeInterface.localComp_eq_alpha_comp_gammaLoc
#print axioms Leaf4FormalLocalTree
#print axioms Leaf4FormalLocalTree.comp
#print axioms Leaf4FormalLocalTree.slots
#print axioms Leaf4FormalLocalTree.slots_length
#print axioms majorTree_comp_not_commutative

/-! ## 4. Formal Leaf-4 split and owner firewall -/

#print axioms alpha4
#print axioms gamma4
#print axioms rho5
#print axioms gamma4Loc
#print axioms gamma4Rem
#print axioms gamma4_split
#print axioms c44Loc
#print axioms c45
#print axioms c44Loc_eq_alpha4_dmul_gamma4Loc
#print axioms c45_eq_alpha4_dmul
#print axioms c44Loc_eq_c45_of_lambda4_eq_lambda5
#print axioms c44Loc_ne_c45

/-! ## 5. Row-local status metadata -/

#print axioms RowLocalStatus
#print axioms RowLocalStatus.toStatus
#print axioms RowLocalStatus.isKernelProved
#print axioms rowLocalStatus_never_closed
#print axioms rowLocalStatus_analytic_not_kernelProved
#print axioms analyticBanked_not_kernelProved
#print axioms retracted_ne_kernelProved
#print axioms productFourier_algebra_banked_mechanism_retracted
#print axioms puncturedFrame_banked_jointGain_retracted
#print axioms leaf4_does_not_close_gate1B
#print axioms leaves123_open
#print axioms hNe_lowerD_open
#print axioms current_first_residual_is_rowLocal_dictionary
#print axioms only_algebra_rows_kernelProved
#print axioms residual_labels_distinct

/-! ## 6. Physical row-local dictionary interface -/

#print axioms PhysicalRowLocalDictionary
#print axioms RowLocalObligations
#print axioms PhysicalRowLocalDictionaryValid
#print axioms placeholderDictionary
#print axioms placeholderObligations
#print axioms physicalRowLocalDictionaryValid_not_unconditional
#print axioms dictionary_data_not_pinned
#print axioms kappa4_not_pinned

/-! ## 7. Conditional compilers (hypotheses are explicit arguments) -/

#print axioms Leaf4AnalyticHypotheses
#print axioms Leaf4ClosureConclusion
#print axioms leaf4_closed_of_physical_dictionary
#print axioms leaf4_closure_requires_dictionary
#print axioms leaf4_closure_not_unconditional
#print axioms HZeroLeafHypotheses
#print axioms HZeroHighHighConclusion
#print axioms hZeroHighHigh_closed_of_local_dictionary
#print axioms hZeroHighHigh_does_not_close_gate1B
#print axioms hZeroHighHigh_requires_leaves123
#print axioms q1NormalisationStatus
#print axioms q2NormalisationStatus
#print axioms smallQ_normalisations_are_source_pins

/-! ## 8. Ledger layer -/

#print axioms LedgerGate1BRowLocalDictionary.full
#print axioms LedgerGate1BRowLocalDictionary.no_closed_rows
#print axioms LedgerGate1BRowLocalDictionary.ledger_is_honest
#print axioms LedgerGate1BRowLocalDictionary.gate1B_open
#print axioms LedgerGate1BRowLocalDictionary.current_first_source_residual
#print axioms LedgerGate1BRowLocalDictionary.old_c4shift_superseded
#print axioms LedgerGate1BRowLocalDictionary.previous_layer_preserved
#print axioms LedgerGate1BRowLocalDictionary.historical_research_rows_preserved
#print axioms LedgerGate1BRowLocalDictionary.algebra_banked_while_mechanism_retracted
#print axioms LedgerGate1BRowLocalDictionary.new_exact_rows_kernel_proved
#print axioms LedgerGate1BRowLocalDictionary.analytic_bank_rows_not_kernel_proved
#print axioms LedgerGate1BRowLocalDictionary.open_branches
#print axioms LedgerGate1BRowLocalDictionary.leaf4_does_not_close_gate1B
#print axioms LedgerGate1BRowLocalDictionary.source_pins_open

end AxiomAuditGate1BRowLocalDictionary
end CurrentProgramme
end TwinPrimeProject
