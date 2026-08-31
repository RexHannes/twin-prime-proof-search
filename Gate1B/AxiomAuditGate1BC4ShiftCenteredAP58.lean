import Gate1B.CurrentStatusGate1BC4ShiftCenteredAP58

/-!
# Axiom audit — Gate 1B C4Shift centered AP 5/8 delta

`#print axioms` for every principal declaration of the centered-AP-kernel /
physical `2+2` shift / Bézout delta.

Expected: only `propext`, `Classical.choice`, `Quot.sound` (or none).
No `sorryAx`, no custom axiom, no proof escape.

`C4ShiftCenteredAP.C4ShiftOffdiagCenteredAP58GramInput` is the new analytic
source socket and is **never constructed**; the two previous sockets
`C4ShiftLeafwise.C4ShiftOneMinorPushedEnergyInput` and
`C4ShiftLeafwise.C4ShiftOneMinorAPIndexRestrictionInput` remain uninhabited too.
-/

namespace TwinPrimeProject
namespace CurrentProgramme

/-! ## §1 — exact centered AP phase identity -/

#print axioms C4ShiftCenteredAP.centered_ap_phase_identity
#print axioms C4ShiftCenteredAP.centered_A0_spec
#print axioms C4ShiftCenteredAP.centered_target_of_unit

/-! ## §2 — full `(k₁,k₂)` orthogonality -/

#print axioms C4ShiftCenteredAP.Rfull
#print axioms C4ShiftCenteredAP.Rfull_eq_indicator
#print axioms C4ShiftCenteredAP.Rfull_eq_one_of_unit

/-! ## §3 — sampled double-major operators and the centered kernel -/

#print axioms C4ShiftCenteredAP.Mplus
#print axioms C4ShiftCenteredAP.Mminus
#print axioms C4ShiftCenteredAP.RMM
#print axioms C4ShiftCenteredAP.R1m
#print axioms C4ShiftCenteredAP.RMM_factor
#print axioms C4ShiftCenteredAP.R1m_centered

/-! ## §4 — owner decomposition -/

#print axioms C4ShiftCenteredAP.APdeltaPlus
#print axioms C4ShiftCenteredAP.APdeltaMinus
#print axioms C4ShiftCenteredAP.mplus
#print axioms C4ShiftCenteredAP.mminus
#print axioms C4ShiftCenteredAP.Rfull_factor
#print axioms C4ShiftCenteredAP.R1m_owner_decomposition
#print axioms C4ShiftCenteredAP.ownerMm
#print axioms C4ShiftCenteredAP.ownermM
#print axioms C4ShiftCenteredAP.ownermm
#print axioms C4ShiftCenteredAP.R1m_owners

/-! ## §5 — major-projector aliasing -/

#print axioms C4ShiftCenteredAP.M4model
#print axioms C4ShiftCenteredAP.Mplus_aliasing
#print axioms C4ShiftCenteredAP.Mminus_aliasing

/-! ## §6 — state-count firewall -/

#print axioms C4ShiftCenteredAP.ell_state_count_no_saving

/-! ## §7 — physical `2+2` shift -/

#print axioms C4ShiftCenteredAP.Physical2Plus2Shift
#print axioms C4ShiftCenteredAP.Physical2Plus2Shift.A1
#print axioms C4ShiftCenteredAP.Physical2Plus2Shift.A2
#print axioms C4ShiftCenteredAP.Physical2Plus2Shift.shift_A
#print axioms C4ShiftCenteredAP.Physical2Plus2Shift.shift_product
#print axioms C4ShiftCenteredAP.Physical2Plus2Shift.g_relation

/-! ## §10 — nonzero-shift firewall -/

#print axioms C4ShiftCenteredAP.Physical2Plus2Shift.congruence_mod_ell
#print axioms C4ShiftCenteredAP.Physical2Plus2Shift.true_diagonal_excluded
#print axioms C4ShiftCenteredAP.congruence_not_equality

/-! ## §8 — Bézout normal form -/

#print axioms C4ShiftCenteredAP.bezout_2plus2_normalform

/-! ## §9 — Bézout solution line -/

#print axioms C4ShiftCenteredAP.bezout_solution_line_forward
#print axioms C4ShiftCenteredAP.bezout_solution_line_converse
#print axioms C4ShiftCenteredAP.bezout_line_card_bound

/-! ## §12 — the new analytic socket (UNINHABITED) and its trivial consumer -/

#print axioms C4ShiftCenteredAP.C4ShiftOffdiagCenteredAP58GramInput
#print axioms C4ShiftCenteredAP.centeredAP58_conditional_consumer

/-! ## Status layer -/

#print axioms C4ShiftCenteredAP.statusRows_no_closed
#print axioms C4ShiftCenteredAP.statusRows_first_residual
#print axioms C4ShiftCenteredAP.pushed_energy_not_false
#print axioms LedgerC4ShiftCenteredAP58.no_closed_rows
#print axioms LedgerC4ShiftCenteredAP58.ledger_is_honest
#print axioms LedgerC4ShiftCenteredAP58.gate1B_open
#print axioms LedgerC4ShiftCenteredAP58.pushed_energy_superseded
#print axioms LedgerC4ShiftCenteredAP58.previous_layer_preserved
#print axioms LedgerC4ShiftCenteredAP58.old_closure_retracted
#print axioms LedgerC4ShiftCenteredAP58.first_analytic_residual
#print axioms LedgerC4ShiftCenteredAP58.first_analytic_residual_alias
#print axioms LedgerC4ShiftCenteredAP58.parallel_local_residual
#print axioms LedgerC4ShiftCenteredAP58.new_exact_rows_kernel_proved
#print axioms LedgerC4ShiftCenteredAP58.analytic_rows_not_kernel_proved
#print axioms LedgerC4ShiftCenteredAP58.no_closed_analytic_row

end CurrentProgramme
end TwinPrimeProject
