import Gate1B.CurrentStatusGate1BFM722Kloosterman

/-!
# Gate 1B · axiom audit for the FM722 centred-Kloosterman / generated-DFT bank

`#print axioms` for every principal public theorem of the modules

* `Gate1B.FM722GeneratedGammaSource`
* `Gate1B.FM722BalancedCoagulation`
* `Gate1B.FM722CenteredOneFactorCompletion`
* `Gate1B.FM722CenteredTwoFactorKloosterman`
* `Gate1B.FM722CenteredDualAxes`
* `Gate1B.FM722GeneratedDFTFourierSparsity`
* `Gate1B.FM722KloostermanCRT`
* `Gate1B.FM722PrimeSeparationFirewall`
* `Gate1B.FM722LongLineNormalForm`
* `Gate1B.FM722CrossQAnalyticInterface`
* `Gate1B.CurrentStatusGate1BFM722Kloosterman`

Only the standard foundations `propext`, `Classical.choice` and `Quot.sound`
may appear.  There is no `sorry`, no `sorryAx`, no custom `axiom`, no
`native_decide`, no `implemented_by`, no `unsafe` and no `opaque` shortcut
anywhere in this bank.

The uninhabited interfaces
`FM722GeneratedDFTCenteredKloostermanCrossQBound`,
`SparseFourierKloostermanBoundInput`, `BPCriticalBlockBoundInput`,
`FordGeneratedGammaSource`, `LongLineRangeData` and
`RamanujanSquarefreeClosedForm` are never constructed, so no `#print axioms`
line below depends on an analytic input.
-/

namespace TwinPrimeProject
namespace CurrentProgramme

open TwinPrimeProject.CurrentProgramme.FM722

-- FM722GeneratedGammaSource
#print axioms GeneratedGammaAtomization.expoList_sum
#print axioms GeneratedGammaAtomization.expoList_mem
#print axioms generated_source_admits_balanced_coagulation
#print axioms generated_source_window_lt_half

-- FM722BalancedCoagulation
#print axioms prefix_sum_step
#print axioms prefix_step_le
#print axioms balanced_coagulation
#print axioms coagulation_window_lt_half

-- FM722CenteredOneFactorCompletion
#print axioms cast_card_ne_zero
#print axioms invDFT_dftHat
#print axioms fourier_inversion
#print axioms dftHat_invDFT
#print axioms ramanujanSum_unit_mul
#print axioms ramanujanSum_neg
#print axioms centered_twisted_transform
#print axioms oneFactor_centered_completion
#print axioms centeredOneFactorCoeff_zero
#print axioms oneFactor_zero_frequency_term
#print axioms ramanujanSum_prime_nonzero

-- FM722CenteredTwoFactorKloosterman
#print axioms sum_ite_isUnit
#print axioms unitPrincipal_eq_ite
#print axioms sum_unitSector_eM
#print axioms kloostermanSum_eq_units
#print axioms kloostermanSum_zero_right
#print axioms kloostermanSum_zero_left
#print axioms indicator_double_sum
#print axioms principal_double_sum
#print axioms centered_twoFrequency_transform
#print axioms sum_comm4
#print axioms twoFactor_centered_completion

-- FM722CenteredDualAxes
#print axioms centeredKloostermanKernel_zero_left
#print axioms centeredKloostermanKernel_zero_right
#print axioms centeredKloostermanKernel_dual_axes_zero
#print axioms twoFactor_axis_terms_vanish

-- FM722GeneratedDFTFourierSparsity
#print axioms parseval_complex
#print axioms parseval_norm
#print axioms generatedDFT_sparseInverseFourier
#print axioms generatedDFT_sparseInverseFourier_card
#print axioms deltaZero_support
#print axioms dftHat_deltaZero
#print axioms dftHat_deltaZero_full_support
#print axioms crtTestHat_is_a_dft
#print axioms crt_dft_no_factorisation

-- FM722KloostermanCRT
#print axioms exists_bezout
#print axioms eM_crt
#print axioms crtUnits_fst
#print axioms crtUnits_snd
#print axioms crtUnits_fst_inv
#print axioms crtUnits_snd_inv
#print axioms kloostermanSum_crt
#print axioms bezout_units
#print axioms ramanujanSum_crt
#print axioms centered_crt_decomposition
#print axioms centered_crt_decomposition_applied

-- FM722PrimeSeparationFirewall
#print axioms no_common_prime_of_coprime
#print axioms prime_separation
#print axioms prime_separation_gcd_form

-- FM722LongLineNormalForm
#print axioms longline_parametrisation

-- FM722CrossQAnalyticInterface
#print axioms crossQAtom_eq_physicalAtom
#print axioms CrossQFamily.J_eq_packet
#print axioms crossQDiagonal_nonneg
#print axioms crossQDiagonal_cast
#print axioms crossQTotal_split
#print axioms crossQTotal_bound_of_interface
#print axioms packet_covariance_bound_of_interface

-- CurrentStatusGate1BFM722Kloosterman
#print axioms LedgerGate1BFM722Kloosterman.no_closed_rows
#print axioms LedgerGate1BFM722Kloosterman.ledger_is_honest
#print axioms LedgerGate1BFM722Kloosterman.current_analytic_frontier
#print axioms LedgerGate1BFM722Kloosterman.analytic_rows_open
#print axioms LedgerGate1BFM722Kloosterman.new_exact_rows_kernel_proved
#print axioms LedgerGate1BFM722Kloosterman.gamma_source_row_not_kernel_proved
#print axioms LedgerGate1BFM722Kloosterman.literature_row_not_kernel_proved
#print axioms LedgerGate1BFM722Kloosterman.hstar_gateexport_open
#print axioms LedgerGate1BFM722Kloosterman.global_gate1B_open
#print axioms LedgerGate1BFM722Kloosterman.twin_prime_open
#print axioms LedgerGate1BFM722Kloosterman.previous_layer_preserved

end CurrentProgramme
end TwinPrimeProject
