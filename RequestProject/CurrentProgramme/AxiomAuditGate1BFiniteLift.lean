import RequestProject.CurrentProgramme.CurrentStatusGate1BFiniteLift
import RequestProject.CurrentProgramme.AxiomAuditShiftedMAMOperator

/-!
# Trust audit · Gate 1B finite-lift status layer

`#print axioms` over the **new** declarations of
`CurrentStatusGate1BFiniteLift` only.  Earlier audits
(`AxiomAuditShiftedMAMOperator`, `AxiomAuditHighKShift`, …) are imported and
left untouched.

Expected results: `propext`, `Classical.choice`, `Quot.sound`, or a subset.
No `sorryAx`, no `Lean.ofReduceBool`.

The new layer contains no `sorry`, `admit`, user `axiom`, `opaque`, `unsafe`,
`native_decide` or `@[implemented_by]` (the only textual occurrences of those
tokens in this file are in this documentation paragraph).
-/

namespace TwinPrimeProject
namespace CurrentProgramme

#print axioms LedgerFiniteLift.full
#print axioms LedgerFiniteLift.no_closed_rows
#print axioms LedgerFiniteLift.ledger_is_honest
#print axioms LedgerFiniteLift.gate1B_open
#print axioms LedgerFiniteLift.current_research_frontier
#print axioms LedgerFiniteLift.formal_socket_distinct_from_research_frontier
#print axioms LedgerFiniteLift.previous_operator_row_preserved
#print axioms LedgerFiniteLift.detline_rows_are_not_kernel_proved
#print axioms LedgerFiniteLift.finiteLift_tail_budget
#print axioms LedgerFiniteLift.finiteLift_tail_budget_is_order_arithmetic_only

end CurrentProgramme
end TwinPrimeProject
