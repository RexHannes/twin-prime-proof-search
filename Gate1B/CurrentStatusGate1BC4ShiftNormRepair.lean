import Gate1B.CurrentStatusGate1BC4ShiftAPFourier
import Gate1B.C4ShiftNormPromotionRepair

/-!
# Gate 1B · C4Shift norm-promotion repair status layer (append-only)

This layer appends the **retraction** of one research promotion and the updated
child partition of the parent analytic frontier.  Historical layers are
imported, never edited.

## Retraction recorded here

* `C4SHIFT-ONE-FOURPRODUCT-MINOR45` — old research CLOSURE **retracted**.
* `ONE-FOURPRODUCT-MINOR-NORM-PROMOTION45` — NONCLOSING / INVALID IMPLICATION.
* `DOUBLEMAJOR-AS-SOLE-RESIDUAL` — **retracted**: the double-major child stays
  open, but it is no longer the unique controlling child.

The underlying **pointwise** minor estimate is *not* marked false: it is
`externallyAudited` (research PASS, log-corrected).

```
GATE1B : OPEN.
CURRENT PARENT ANALYTIC FRONTIER : C4SHIFT-QFOURIER-PUSHFORWARD45.
```
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace LedgerC4ShiftNormRepair

open Status

set_option maxRecDepth 40000

/-- The norm-promotion repair layer, appended on top of
`LedgerC4ShiftAPFourier.full`. -/
def full : List LedgerEntry :=
  C4ShiftNormRepair.statusRows ++
  [ ⟨"TOPBAND-BETA-BROADMINOR-DETLINE45", Status.open_, "OPEN."⟩,
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

/-- **The parent analytic frontier is unchanged and still open.** -/
theorem parent_frontier_open :
    ∃ e ∈ full, e.label = "C4SHIFT-QFOURIER-PUSHFORWARD45" ∧
      e.status = Status.analyticOpen := by decide

/-- **The retraction is precise**: the *promotion* is `falseRoute`, the
*pointwise* estimate is only `externallyAudited` and explicitly not false. -/
theorem retraction_is_precise :
    (∃ e ∈ full, e.label = "ONE-FOURPRODUCT-MINOR-NORM-PROMOTION45" ∧
      e.status = Status.falseRoute) ∧
    (∃ e ∈ full, e.label = "FOURPRODUCT-POINTWISE-MINOR45" ∧
      e.status ≠ Status.falseRoute) := by
  refine ⟨by decide, by decide⟩

/-- **Double-major is no longer the sole residual.**  Both the one-minor pushed
energy and the leafwise major router are open children of the same parent. -/
theorem children_partition_recorded :
    (∃ e ∈ full, e.label = "C4SHIFT-ONE-MINOR-PUSHED-ENERGY45" ∧
      e.status = Status.analyticOpen) ∧
    (∃ e ∈ full, e.label = "C4SHIFT-MAJOR-LEAFWISE-ROUTER45" ∧
      e.status = Status.sourceOpen) ∧
    (∃ e ∈ full, e.label = "DOUBLEMAJOR-AS-SOLE-RESIDUAL" ∧
      e.status = Status.falseRoute) := by
  refine ⟨by decide, by decide, by decide⟩

/-- **Preservation.**  The previous AP-Fourier layer is untouched. -/
theorem previous_apfourier_layer_preserved :
    ∃ e ∈ LedgerC4ShiftAPFourier.full,
      e.label = "C4SHIFT-DOUBLEMAJOR-FOURPRODUCT-APGRAM45" ∧
      e.status = Status.analyticOpen := by decide

end LedgerC4ShiftNormRepair
end CurrentProgramme
end TwinPrimeProject
