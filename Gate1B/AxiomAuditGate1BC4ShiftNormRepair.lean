import Gate1B.CurrentStatusGate1BC4ShiftNormRepair

/-!
# Axiom audit — Gate 1B C4Shift norm-promotion repair

`#print axioms` for every principal declaration of the repair delta.  Expected:
only `propext`, `Classical.choice`, `Quot.sound`.  No `sorryAx`, no custom
axiom, no proof escape.

`C4ShiftNormRepair.FourProductMinorEnergyInput` is a research **candidate**
socket and is never constructed.
-/

namespace TwinPrimeProject
namespace CurrentProgramme

/-! ## §3 — norm-mismatch firewall -/

#print axioms C4ShiftNormRepair.sq_abs_sum_le_card_mul_sum_sq
#print axioms C4ShiftNormRepair.l1_le_l2_normalised
#print axioms C4ShiftNormRepair.pointwise_substitution_nonclosing

/-! ## §6 — `ℓ`-normalisation firewall -/

#print axioms C4ShiftNormRepair.ell_normalisation_no_saving
#print axioms C4ShiftNormRepair.ell_normalisation_sum

/-! ## §7 — AP index change of variables -/

#print axioms C4ShiftNormRepair.hKmap_bijective
#print axioms C4ShiftNormRepair.hKmap_not_injective_two
#print axioms C4ShiftNormRepair.apindex_hK_normalform

/-! ## §8 — leafwise source classification -/

#print axioms C4ShiftNormRepair.c4leaf_five
#print axioms C4ShiftNormRepair.c4leaf_first_defect

/-! ## Status -/

#print axioms C4ShiftNormRepair.statusRows_no_closed
#print axioms C4ShiftNormRepair.retraction_is_precise
#print axioms LedgerC4ShiftNormRepair.no_closed_rows
#print axioms LedgerC4ShiftNormRepair.ledger_is_honest
#print axioms LedgerC4ShiftNormRepair.gate1B_open
#print axioms LedgerC4ShiftNormRepair.parent_frontier_open
#print axioms LedgerC4ShiftNormRepair.retraction_is_precise
#print axioms LedgerC4ShiftNormRepair.children_partition_recorded
#print axioms LedgerC4ShiftNormRepair.previous_apfourier_layer_preserved

end CurrentProgramme
end TwinPrimeProject
