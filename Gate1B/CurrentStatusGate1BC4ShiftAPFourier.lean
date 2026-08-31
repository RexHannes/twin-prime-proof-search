import Gate1B.CurrentStatusGate1BC4Shift
import Gate1B.C4ShiftAPFourierDoubleMajor

/-!
# Gate 1B · C4Shift AP-Fourier / double-major status layer (append-only)

This module **appends** a status layer on top of `LedgerC4Shift.full`.  The
historical layers are imported, never edited.

## Firewall

Nothing in this layer promotes a research statement to a Lean theorem.  The two
routes refuted in `Gate1B.C4ShiftAPFourierDoubleMajor` are recorded as
`falseRoute` *with explicit countermodels in Lean*; every analytic row is
`analyticOpen` and every source row is `sourceOpen`.

```
GATE1B : OPEN.
```
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace LedgerC4ShiftAPFourier

open Status

set_option maxRecDepth 40000

/-- The AP-Fourier / double-major layer, appended on top of
`LedgerC4Shift.full`. -/
def full : List LedgerEntry :=
  C4ShiftAPFourier.statusRows ++
  [ ⟨"C4SHIFT-GAMMASHARP-RANGE-INPUT45", Status.sourceOpen,
     "UNINHABITED. C4ShiftAPFourier.GammaSharpRangeInput carries the physical routing threshold; it is never constructed. gamma_smallG_vanishes is a conditional consequence only."⟩,
    ⟨"C4SHIFT-QFOURIER-PUSHFORWARD45", Status.analyticOpen,
     "PARENT ANALYTIC RESIDUAL, UNCHANGED. Still ANALYTIC OPEN / UNINHABITED."⟩,
    ⟨"TOPBAND-BETA-BROADMINOR-DETLINE45", Status.open_, "OPEN THROUGH C4SHIFT."⟩,
    ⟨"TOPBAND-BROAD-MAJOR-TREE-MATCH45", Status.sourceOpen, "NOT RUN / SOURCE OPEN."⟩,
    ⟨"SHIFTED-MAM-TOPBAND45", Status.open_, "OPEN."⟩,
    ⟨"PURE5", Status.open_, "OPEN. Not activated."⟩,
    ⟨"GATE1B", Status.open_, "OPEN."⟩ ]

/-! ## Honesty invariants -/

/-- **No row of this layer is `closed`.** -/
theorem no_closed_rows : ∀ e ∈ full, e.status ≠ Status.closed := by decide

/-- **The layer is honest.** -/
theorem ledger_is_honest : ∀ e ∈ full, e.honest := fun e he =>
  LedgerEntry.honest_of_not_closed (no_closed_rows e he)

/-- Gate 1B remains open at this layer. -/
theorem gate1B_open : (⟨"GATE1B", Status.open_, "OPEN."⟩ : LedgerEntry) ∈ full := by decide

/-- **The double-major AP-Gram sector is analytic open**, and `analyticOpen` is
not a kernel proof. -/
theorem doublemajor_apgram_open :
    (∃ e ∈ full, e.label = "C4SHIFT-DOUBLEMAJOR-FOURPRODUCT-APGRAM45" ∧
      e.status = Status.analyticOpen) ∧
    Status.analyticOpen.isKernelProved = false := by
  refine ⟨by decide, by decide⟩

/-- **The parent analytic residual is untouched.** -/
theorem parent_residual_still_open :
    ∃ e ∈ full, e.label = "C4SHIFT-QFOURIER-PUSHFORWARD45" ∧
      e.status = Status.analyticOpen := by decide

/-- **Preservation.**  The previous C4Shift layer is unchanged: it still records
`C4SHIFT-QFOURIER-PUSHFORWARD45` as `analyticOpen`. -/
theorem previous_c4shift_layer_preserved :
    ∃ e ∈ LedgerC4Shift.full, e.label = "C4SHIFT-QFOURIER-PUSHFORWARD45" ∧
      e.status = Status.analyticOpen := by decide

/-- **The two refuted routes are recorded as `falseRoute`.**  Both refutations
are backed by Lean countermodels in `Gate1B.C4ShiftAPFourierDoubleMajor`. -/
theorem refuted_routes_recorded :
    (∃ e ∈ full, e.label = "C4SHIFT-C4-FOURIER-FACTOR45" ∧
      e.status = Status.falseRoute) ∧
    (∃ e ∈ full, e.label = "C4SHIFT-NO-DOUBLE-MAJOR45" ∧
      e.status = Status.falseRoute) := by
  refine ⟨by decide, by decide⟩

end LedgerC4ShiftAPFourier
end CurrentProgramme
end TwinPrimeProject
