/-
# Universal safe algebra — budgeted synthesis (re-export)

Proved in `UniversalV8/Budget.lean`.  Elementary order algebra: the admissible congestion
budget may grow; `C = o(1)` is deliberately NOT encoded, and no claim is made that an
actual arithmetic congestion satisfies any budget.
-/
import UniversalV8.Budget

namespace Universal.SafeAlgebra

export UniversalV8 (budgetedSynthesis budgetedSynthesis_closes budgetedSynthesis_ratio)

end Universal.SafeAlgebra
