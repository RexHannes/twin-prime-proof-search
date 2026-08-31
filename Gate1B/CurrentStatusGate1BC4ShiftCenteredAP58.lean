import Gate1B.CurrentStatusGate1BC4ShiftLeafwise
import Gate1B.C4ShiftCenteredAPKernel

/-!
# Gate 1B · C4Shift centered AP 5/8 status layer (append-only)

This layer appends the centered-AP-kernel / physical `2+2` shift / Bézout delta
on top of `LedgerC4ShiftLeafwise.full`.  **Historical layers are imported, never
edited.**

## Status supersession

The historical row

```
C4SHIFT-ONE-MINOR-PUSHED-ENERGY45 : ANALYTIC OPEN / PREVIOUS FIRST EXACT
                                    ANALYTIC RESIDUAL
```

has been **strictly reduced** by the exact reduction banked in
`Gate1B.C4ShiftCenteredAPKernel`.  It is recorded here as
`supersededAsControllingFrontier` — **not** as false; its original
`analyticOpen` row remains visible in the previous layer.

```
GATE1B : OPEN.

CURRENT FIRST EXACT ANALYTIC RESIDUAL :
  C4SHIFT-OFFDIAG-CENTERED-AP5/8-GRAM45
  (equivalent sharper name: C4SHIFT-1M-BEZOUT-2PLUS2-GRAM45).

PARALLEL LOCAL RESIDUAL :
  TOPBAND-BROAD-MAJOR-TREE-MATCH45 : SOURCE OPEN.
```

## State-count firewall

`NO AUTOMATIC 1/ell^2 SAVING.`  The `ℓ^{-2}` normalisation is exactly consumed
by the `ℓ²` states `(k₁,k₂) mod ℓ`
(`C4ShiftCenteredAP.ell_state_count_no_saving`).

No row of this layer is `closed`, and no analytic row is kernel-proved.
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace LedgerC4ShiftCenteredAP58

open Status

set_option maxRecDepth 40000

/-- The centered-AP / Bézout layer, appended on top of
`LedgerC4ShiftLeafwise.full`. -/
def full : List LedgerEntry :=
  C4ShiftCenteredAP.statusRows ++
  [ ⟨"C4SHIFT-ELL-STATECOUNT-NOTE45", Status.provedFinite,
     "NO AUTOMATIC 1/ell^2 SAVING. Restated in this layer; see C4ShiftCenteredAP.ell_state_count_no_saving."⟩,
    ⟨"TOPBAND-BROAD-MAJOR-TREE-MATCH45", Status.sourceOpen,
     "PARALLEL LOCAL RESIDUAL. SOURCE OPEN."⟩,
    ⟨"C4SHIFT-QFOURIER-PUSHFORWARD45", Status.analyticOpen, "OPEN."⟩,
    ⟨"TOPBAND", Status.open_, "OPEN."⟩,
    ⟨"PURE5", Status.open_, "NOT RUN."⟩,
    ⟨"GATE1B", Status.open_, "OPEN."⟩ ]

/-! ## Honesty invariants -/

/-- **No row of this layer is `closed`.** -/
theorem no_closed_rows : ∀ e ∈ full, e.status ≠ Status.closed := by decide

/-- **The layer is honest.** -/
theorem ledger_is_honest : ∀ e ∈ full, e.honest := fun e he =>
  LedgerEntry.honest_of_not_closed (no_closed_rows e he)

/-- Gate 1B remains open at this layer. -/
theorem gate1B_open : (⟨"GATE1B", Status.open_, "OPEN."⟩ : LedgerEntry) ∈ full := by decide

/-- **The old first residual is recorded as strictly reduced / superseded, and
is NOT marked false.** -/
theorem pushed_energy_superseded :
    ∃ e ∈ full, e.label = "C4SHIFT-ONE-MINOR-PUSHED-ENERGY45" ∧
      e.status = Status.supersededAsControllingFrontier := by decide

/-- **The previous layer is preserved**: the old first analytic residual is
still recorded there as `analyticOpen`. -/
theorem previous_layer_preserved :
    ∃ e ∈ LedgerC4ShiftLeafwise.full,
      e.label = "C4SHIFT-ONE-MINOR-PUSHED-ENERGY45" ∧
      e.status = Status.analyticOpen := by decide

/-- **The old closure retraction is preserved.** -/
theorem old_closure_retracted :
    ∃ e ∈ full, e.label = "C4SHIFT-ONE-FOURPRODUCT-MINOR45" ∧
      e.status = Status.supersededAsControllingFrontier := by decide

/-- **Current first exact analytic residual.** -/
theorem first_analytic_residual :
    ∃ e ∈ full, e.label = "C4SHIFT-OFFDIAG-CENTERED-AP5/8-GRAM45" ∧
      e.status = Status.analyticOpen := by decide

/-- **Equivalent sharper name of the current residual.** -/
theorem first_analytic_residual_alias :
    ∃ e ∈ full, e.label = "C4SHIFT-1M-BEZOUT-2PLUS2-GRAM45" ∧
      e.status = Status.analyticOpen := by decide

/-- **Parallel local residual.** -/
theorem parallel_local_residual :
    ∃ e ∈ full, e.label = "TOPBAND-BROAD-MAJOR-TREE-MATCH45" ∧
      e.status = Status.sourceOpen := by decide

/-- **The four new exact rows are kernel-proved algebra.** -/
theorem new_exact_rows_kernel_proved :
    ∀ e ∈ full,
      (e.label = "C4SHIFT-1M-APKERNEL45" ∨ e.label = "C4SHIFT-1M-CENTERED-KERNEL45" ∨
        e.label = "C4SHIFT-MAJORPROJECTOR-HKFOURIER45" ∨
        e.label = "C4SHIFT-2PLUS2-PHYSICAL-SHIFT45" ∨
        e.label = "C4SHIFT-BEZOUT-2PLUS2-NORMALFORM45" ∨
        e.label = "C4SHIFT-BEZOUT-SOLUTION-LINE45") →
      e.status.isKernelProved = true := by decide

/-- **No analytic row of this layer is kernel-proved.** -/
theorem analytic_rows_not_kernel_proved :
    ∀ e ∈ full, e.status = Status.analyticOpen → e.status.isKernelProved = false := by decide

/-- **No CLOSED analytic row exists in this layer.** -/
theorem no_closed_analytic_row :
    ¬ ∃ e ∈ full, e.status = Status.closed := by decide

end LedgerC4ShiftCenteredAP58
end CurrentProgramme
end TwinPrimeProject
