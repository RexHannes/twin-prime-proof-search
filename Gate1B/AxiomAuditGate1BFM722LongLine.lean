import Gate1B.CurrentStatusGate1BFM722LongLine

/-!
# Gate 1B · axiom audit for the FM722 long-line determinant-2 bank

`#print axioms` for every principal public declaration of the modules

* `Gate1B.FM722LongLineDiophantine`
* `Gate1B.FM722OneAtomLongLine`
* `Gate1B.FM722AtomTypeInterface`
* `Gate1B.FM722SecondAtomHardOpening`
* `Gate1B.FM722IteratedDeterminantTwo`
* `Gate1B.FM722LongLineLengthLedger`
* `Gate1B.FM722SecondAtomSoftProjector`
* `Gate1B.FM722LongLineCenteredInterface`
* `Gate1B.FM722LongLineAnalyticInterface`
* `Gate1B.CurrentStatusGate1BFM722LongLine`

Only the standard foundations `propext`, `Classical.choice` and `Quot.sound`
may appear.  There is no `sorry`, no `sorryAx`, no custom `axiom`, no
`native_decide`, no `implemented_by`, no `unsafe` and no `opaque` shortcut
anywhere in this bank.

The interfaces `FM722LongLineOneAtomMobiusGammaBound`,
`FM722LongLineTwoAtomHardBound`, `FM722LongLineTwoAtomSoftBound` and
`PhysicalGammaAtomFactorisation` are never constructed, so no `#print axioms`
line below depends on an analytic input.  The two conditional compilers
`softBound_to_oneAtomBound` and `hardBound_to_oneAtomBound` *take* an interface
term as an argument; they do not produce one.
-/

namespace TwinPrimeProject
namespace CurrentProgramme

open TwinPrimeProject.CurrentProgramme.FM722LongLine

-- FM722LongLineDiophantine
#print axioms det2_line_forward
#print axioms det2_line_converse
#print axioms det2_line_iff
#print axioms gcd_divides_two_of_det2
#print axioms odd_divisor_coprime_ell
#print axioms odd_divisor_isCoprime_ell
#print axioms det2_even_y_countermodel
#print axioms even_case_gcd_dvd_two

-- FM722OneAtomLongLine
#print axioms OneAtomDeterminant2Data.det_at
#print axioms OneAtomDeterminant2Data.det_iff
#print axioms oneAtomDeterminant2Data_nonempty

-- FM722AtomTypeInterface
#print axioms gammaAtomMetadata_nonempty
#print axioms TwoAtomIncidenceData.det_at
#print axioms TwoAtomIncidenceData.y_coprime_ell

-- FM722SecondAtomHardOpening
#print axioms exists_opening_residue
#print axioms opening_residue_unique
#print axioms hard_opening_q
#print axioms hard_opening_c
#print axioms hard_opening_determinant
#print axioms hard_opening_determinant_at
#print axioms HardSecondAtomOpening.det_at
#print axioms hard_opening_fibre_iff
#print axioms hard_opening_converse
#print axioms compileHard
#print axioms compileHard_newSlope
#print axioms compileHard_qAt
#print axioms compileHard_cAt

-- FM722IteratedDeterminantTwo
#print axioms odd_dividing_atom_coprime
#print axioms det2_open_one
#print axioms det2_open_list
#print axioms det2_open_odd_step

-- FM722LongLineLengthLedger
#print axioms LongLineExponents.twoAtomLineExp_eq
#print axioms LongLineExponents.twoAtomSlopeExp_eq
#print axioms LongLineExponents.oneAtom_line_add_slope
#print axioms LongLineExponents.twoAtom_line_add_slope
#print axioms LongLineExponents.hard_opening_transfer
#print axioms twoAtomLine_le_oneAtomLine
#print axioms oneAtomSlope_le_twoAtomSlope
#print axioms slope_threshold_not_inherited
#print axioms no_slope_threshold_inheritance
#print axioms hard_opening_can_shorten_below
#print axioms line_length_not_determined_by_one_atom_data

-- FM722SecondAtomSoftProjector
#print axioms soft_divisibility_projector
#print axioms soft_opening_phase
#print axioms SoftSecondAtomOpening.frequency_count
#print axioms soft_zero_nonzero_split
#print axioms nzFreq_card
#print axioms hard_slope_ne_soft_slope
#print axioms hard_soft_representations_differ
#print axioms compileSoft
#print axioms compileSoft_reconstruction

-- FM722LongLineCenteredInterface
#print axioms hardTransform_centred
#print axioms softTransform_centred
#print axioms model_cannot_be_dropped_hard
#print axioms model_cannot_be_dropped_soft
#print axioms centred_transform_pair

-- FM722LongLineAnalyticInterface
#print axioms softValue_eq_oneAtomValue
#print axioms hardValue_eq_oneAtomValue
#print axioms softBound_to_oneAtomBound
#print axioms hardBound_to_oneAtom_packet
#print axioms hardBound_to_oneAtomBound
#print axioms hard_and_soft_interfaces_are_independent_inputs

-- CurrentStatusGate1BFM722LongLine
#print axioms LedgerGate1BFM722LongLine.no_closed_rows
#print axioms LedgerGate1BFM722LongLine.ledger_is_honest
#print axioms LedgerGate1BFM722LongLine.current_analytic_frontier
#print axioms LedgerGate1BFM722LongLine.analytic_rows_open
#print axioms LedgerGate1BFM722LongLine.new_exact_rows_kernel_proved
#print axioms LedgerGate1BFM722LongLine.atom_metadata_row_not_kernel_proved
#print axioms LedgerGate1BFM722LongLine.generated_dft_lane_not_false
#print axioms LedgerGate1BFM722LongLine.kloosterman_row_still_banked
#print axioms LedgerGate1BFM722LongLine.hstar_gateexport_open
#print axioms LedgerGate1BFM722LongLine.global_gate1B_open
#print axioms LedgerGate1BFM722LongLine.twin_prime_open
#print axioms LedgerGate1BFM722LongLine.previous_layer_preserved

end CurrentProgramme
end TwinPrimeProject
