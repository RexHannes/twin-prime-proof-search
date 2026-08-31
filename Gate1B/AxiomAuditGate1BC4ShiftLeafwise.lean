import Gate1B.CurrentStatusGate1BC4ShiftLeafwise

/-!
# Axiom audit — Gate 1B C4Shift leafwise major / one-minor delta

`#print axioms` for every principal declaration of the leafwise delta.
Expected: only `propext`, `Classical.choice`, `Quot.sound` (or none).
No `sorryAx`, no custom axiom, no proof escape.

`C4ShiftLeafwise.C4ShiftOneMinorPushedEnergyInput` and
`C4ShiftLeafwise.C4ShiftOneMinorAPIndexRestrictionInput` are analytic source
sockets and are **never constructed**.
-/

namespace TwinPrimeProject
namespace CurrentProgramme

/-! ## §B — major-arc ownership -/

#print axioms C4ShiftLeafwise.farey_separation
#print axioms C4ShiftLeafwise.major_arc_ownership_unique

/-! ## §C — character diagonalisation -/

#print axioms C4ShiftLeafwise.gaussSumChar
#print axioms C4ShiftLeafwise.conj_char_apply
#print axioms C4ShiftLeafwise.major_char_diagonal

/-! ## §D — unit / non-unit reduction -/

#print axioms C4ShiftLeafwise.nonunit_reduction
#print axioms C4ShiftLeafwise.gcd_partition

/-! ## §E — multiplicative four-fold factorisation -/

#print axioms C4ShiftLeafwise.char_fourfold_factor
#print axioms C4ShiftLeafwise.fourProduct_2plus2'

/-! ## §F — leafwise source classification -/

#print axioms C4ShiftLeafwise.firstDefectIndex
#print axioms C4ShiftLeafwise.leaf_five_pure
#print axioms C4ShiftLeafwise.leaf_first_defect

/-! ## §H — one-minor projector and the tuple-level split -/

#print axioms C4ShiftLeafwise.P1m
#print axioms C4ShiftLeafwise.P1m_eq_one_iff
#print axioms C4ShiftLeafwise.P1m_eq_zero_iff
#print axioms C4ShiftLeafwise.GammaOneMinorSharp
#print axioms C4ShiftLeafwise.GammaDoubleMajorSharp
#print axioms C4ShiftLeafwise.gammaSharp_one_minor_split

/-! ## §I — `(h,K)` AP-index normal form -/

#print axioms C4ShiftLeafwise.hK_inversion
#print axioms C4ShiftLeafwise.apindex_phase_normalform
#print axioms C4ShiftLeafwise.full_sum_support
#print axioms C4ShiftLeafwise.full_hK_sums_force_A

/-! ## §J — `ℓ`-normalisation firewall (restated) -/

#print axioms C4ShiftLeafwise.ell_normalisation_no_saving'

/-! ## Status layer -/

#print axioms C4ShiftLeafwise.statusRows_no_closed
#print axioms C4ShiftLeafwise.broad_major_tree_match_not_closed
#print axioms LedgerC4ShiftLeafwise.no_closed_rows
#print axioms LedgerC4ShiftLeafwise.ledger_is_honest
#print axioms LedgerC4ShiftLeafwise.gate1B_open
#print axioms LedgerC4ShiftLeafwise.parent_open
#print axioms LedgerC4ShiftLeafwise.first_analytic_residual
#print axioms LedgerC4ShiftLeafwise.parallel_local_residual
#print axioms LedgerC4ShiftLeafwise.previous_layer_preserved
#print axioms LedgerC4ShiftLeafwise.analytic_rows_not_kernel_proved

end CurrentProgramme
end TwinPrimeProject
