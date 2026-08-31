import Gate1B.CurrentStatusGate1BC4ShiftNormRepair
import Gate1B.C4ShiftLeafwiseOneMinor

/-!
# Gate 1B · C4Shift leafwise major / one-minor status layer (append-only)

This layer appends the leafwise-major / one-minor routing delta on top of
`LedgerC4ShiftNormRepair.full`.  Historical layers are **imported, never
edited**.

## What is new here

* deterministic **major-arc ownership** (Farey separation) — formally proved;
* **character diagonalisation** of the major-arc phase, with the correct
  conjugations and no primitivity assumption — formally proved;
* exact **unit / non-unit reduction** and the finite `gcd` partition;
* the multiplicative four-fold factorisation (the *false* additive-Fourier
  factorisation is not revived);
* the tuple-level **one-minor projector** `P₁ₘ` and the exact `Γ♯` split;
* the `(h,K)` **AP-index normal form** on the odd clean sector.

Everything analytic remains an **uninhabited** source socket.

```
GATE1B : OPEN.
FIRST EXACT ANALYTIC RESIDUAL : C4SHIFT-ONE-MINOR-PUSHED-ENERGY45.
PARALLEL LOCAL RESIDUAL       : TOPBAND-BROAD-MAJOR-TREE-MATCH45.
```
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace LedgerC4ShiftLeafwise

open Status

set_option maxRecDepth 40000

/-- The leafwise major / one-minor layer, appended on top of
`LedgerC4ShiftNormRepair.full`. -/
def full : List LedgerEntry :=
  C4ShiftLeafwise.statusRows ++
  [ ⟨"TOPBAND-BETA-BROADMINOR-DETLINE45", Status.open_, "OPEN THROUGH C4SHIFT."⟩,
    ⟨"TOPBAND-RECURSIVE-MAJOR-TREE-PAIRING45", Status.open_, "OPEN."⟩,
    ⟨"SHIFTED-MAM-TOPBAND45", Status.open_, "OPEN."⟩,
    ⟨"RANKONE-ENDPOINT-ALLK45", Status.open_, "OPEN."⟩,
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

/-- **The parent analytic frontier is unchanged and still open.** -/
theorem parent_open :
    ∃ e ∈ full, e.label = "C4SHIFT-QFOURIER-PUSHFORWARD45" ∧
      e.status = Status.analyticOpen := by decide

/-- **First exact analytic residual of this layer.** -/
theorem first_analytic_residual :
    ∃ e ∈ full, e.label = "C4SHIFT-ONE-MINOR-PUSHED-ENERGY45" ∧
      e.status = Status.analyticOpen := by decide

/-- **Parallel local residual**: the broad major-tree match is not closed. -/
theorem parallel_local_residual :
    ∃ e ∈ full, e.label = "TOPBAND-BROAD-MAJOR-TREE-MATCH45" ∧
      e.status = Status.sourceOpen := by decide

/-- **Preservation.**  The previous norm-repair layer is untouched: the
retraction it recorded is still visible. -/
theorem previous_layer_preserved :
    ∃ e ∈ LedgerC4ShiftNormRepair.full,
      e.label = "ONE-FOURPRODUCT-MINOR-NORM-PROMOTION45" ∧
      e.status = Status.falseRoute := by decide

/-- **No kernel-proved status is attached to any analytic row of this layer.** -/
theorem analytic_rows_not_kernel_proved :
    ∀ e ∈ full, e.status = Status.analyticOpen → e.status.isKernelProved = false := by decide

end LedgerC4ShiftLeafwise
end CurrentProgramme
end TwinPrimeProject
