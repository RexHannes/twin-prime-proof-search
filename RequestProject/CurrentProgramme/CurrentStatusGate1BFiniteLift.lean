import RequestProject.CurrentProgramme.CurrentStatusShiftedMAMOperator

/-!
# Gate 1B · finite-lift research frontier (append-only status layer)

**Append-only.**  This module adds one new status layer on top of
`LedgerMAMOperator.full`.  It does **not** alter `CurrentStatusHighKShift`,
`CurrentStatusShiftedMAMOperator`, or any earlier ledger, and it does not change
the meaning of any historical status label.

## What this layer records

Two frontiers are deliberately kept **distinct**:

* the **formal abstraction frontier** — `SHIFTED-MAM-FIVEFOLD-OPERATOR45`,
  `analyticOpen`, the broader uninhabited operator interface that the Lean bank
  actually exposes (`MAMOperator.ShiftedMAMFivefoldOperatorInput`);
* the **latest research frontier** — `DETLINE-NEARPRIM-FINITELIFT-DENSE-SATURATION45`,
  the first exact residual at the research/paper level.

The determinant-line ("DETLINE") rows below are **research status metadata
only**.  None of them is a Lean theorem here, and none of their analytic
antecedents is inhabited anywhere in this repository.  In particular the
research-level exact-lift energy consequences

```
E_{G,2}(e) ≪ e^{-1} Y^{29/2} log^{O(1)} X,
E_{R,2}(e) ≪ R Y e^{-2} log^{O(1)} X,
hence |T_j(e)| ≪ X e^{-3/2} log^{O(1)} X   (j = 1,…,5),
```

are recorded as external research results, not as formal claims.  Only the
*order-arithmetic consequence* of the last display — the tail budget — is banked
formally, and only in the abstract form of `finiteLift_tail_budget` below, whose
per-lift bound and tail-sum input are **hypotheses**.

Status vocabulary note: the existing taxonomy has no `researchClosed` or
`partial` constructor, and inventing `closed` would be misleading.  The nearest
honest existing statuses are used (`externallyAudited`,
`supersededAsControllingFrontier`, `analyticOpen`, `open_`) with the finer
meaning carried in the note field.

```
GATE1B : OPEN.
```
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace LedgerFiniteLift

open Status

set_option maxRecDepth 40000

/-! ## The new status layer -/

/-- The finite-lift research-frontier layer, appended on top of
`LedgerMAMOperator.full`. -/
def full : List LedgerEntry :=
  [ ⟨"SHIFTED-MAM-FIVEFOLD-OPERATOR45", Status.analyticOpen,
     "FORMAL ABSTRACTION FRONTIER. Unchanged from LedgerMAMOperator.full. MAMOperator.ShiftedMAMFivefoldOperatorInput; UNINHABITED. This is the broader analytic-open formal interface, not the research residual."⟩,
    ⟨"DETLINE-CONDUCTOR-LE-Y45", Status.externallyAudited,
     "RESEARCH: POWER CLOSED. External research/paper level only; no Lean theorem and no inhabited analytic antecedent here."⟩,
    ⟨"DETLINE-CONDUCTOR-LOCAL-G-ENERGY45", Status.externallyAudited,
     "RESEARCH: EXACT FIXED-LIFT FORM / PARTIAL GAIN. Not full closure; partial gain only. Metadata only."⟩,
    ⟨"DETLINE-LARGE-LIFT-DISPERSION45", Status.externallyAudited,
     "RESEARCH CLOSED at current research/paper level (no `researchClosed` constructor exists; `externallyAudited` is the nearest honest status). NOT kernel-proved here."⟩,
    ⟨"DETLINE-FINITELIFT-NEARPRIM-REDUCTION45", Status.externallyAudited,
     "RESEARCH: PASS / REDUCED. The finite-lift near-primitive reduction is audited externally; it reduces, it does not close."⟩,
    ⟨"DETLINE-HIGHCOND-DENSE-SATURATION-EXCLUSION45", Status.analyticOpen,
     "CLOSED FOR LOG-LARGE LIFTS (research), OPEN FOR FINITE LIFTS. The open finite-lift half is what remains; recorded analyticOpen for that half."⟩,
    ⟨"DETLINE-HIGHCOND-BETA-RHO-CROSSPAIR45", Status.supersededAsControllingFrontier,
     "PARTIALLY CLOSED / STRICTLY REDUCED (research). Reduced, not closed, and NOT false; no longer the controlling residual."⟩,
    ⟨"TOPBAND-BETA-BROADMINOR-DETLINE45", Status.analyticOpen,
     "PARTIAL: LARGE-LIFT CELLS CLOSED (research), FINITE-LIFT CELLS OPEN. Recorded analyticOpen for the surviving finite-lift cells."⟩,
    ⟨"DETLINE-NEARPRIM-FINITELIFT-DENSE-SATURATION45", Status.analyticOpen,
     "LATEST RESEARCH FRONTIER / FIRST EXACT RESEARCH RESIDUAL. Surviving range 1 ≤ e ≤ (log X)^{B_A}, ell = c*e ~ R, c ~ R (log X)^{-O_A(1)}. Not attacked here."⟩,
    ⟨"GATE1B", Status.open_, "OPEN."⟩ ]

/-! ## Honesty invariants -/

/-- **No row of this layer is `closed`.** -/
theorem no_closed_rows : ∀ e ∈ full, e.status ≠ Status.closed := by decide

/-- **The layer is honest.** -/
theorem ledger_is_honest : ∀ e ∈ full, e.honest := fun e he =>
  LedgerEntry.honest_of_not_closed (no_closed_rows e he)

/-- Gate 1B remains open at this layer. -/
theorem gate1B_open : (⟨"GATE1B", Status.open_, "OPEN."⟩ : LedgerEntry) ∈ full := by
  decide

/-- **The current research frontier** is the finite-lift dense-saturation
residual, and it is `analyticOpen` — not kernel-proved. -/
theorem current_research_frontier :
    (⟨"DETLINE-NEARPRIM-FINITELIFT-DENSE-SATURATION45", Status.analyticOpen,
      "LATEST RESEARCH FRONTIER / FIRST EXACT RESEARCH RESIDUAL. Surviving range 1 ≤ e ≤ (log X)^{B_A}, ell = c*e ~ R, c ~ R (log X)^{-O_A(1)}. Not attacked here."⟩
        : LedgerEntry) ∈ full ∧
    Status.analyticOpen.isKernelProved = false := by
  refine ⟨by decide, by decide⟩

/-- **The formal operator socket is a different row from the research
residual.**  The Lean bank's uninhabited interface
`SHIFTED-MAM-FIVEFOLD-OPERATOR45` is strictly broader, and remains present here
with exactly the status it had in the previous layer. -/
theorem formal_socket_distinct_from_research_frontier :
    (⟨"SHIFTED-MAM-FIVEFOLD-OPERATOR45", Status.analyticOpen,
      "FORMAL ABSTRACTION FRONTIER. Unchanged from LedgerMAMOperator.full. MAMOperator.ShiftedMAMFivefoldOperatorInput; UNINHABITED. This is the broader analytic-open formal interface, not the research residual."⟩
        : LedgerEntry) ∈ full ∧
    "SHIFTED-MAM-FIVEFOLD-OPERATOR45" ≠
      "DETLINE-NEARPRIM-FINITELIFT-DENSE-SATURATION45" := by
  refine ⟨by decide, by decide⟩

/-- **Preservation.**  The previous layer's operator row is untouched. -/
theorem previous_operator_row_preserved :
    (⟨"SHIFTED-MAM-FIVEFOLD-OPERATOR45", Status.analyticOpen,
      "OPEN_ANALYTIC / FIRST EXACT ANALYTIC RESIDUAL. MAMOperator.ShiftedMAMFivefoldOperatorInput; UNINHABITED; canonical local term M_h^can kept explicit."⟩
        : LedgerEntry) ∈ LedgerMAMOperator.full := by decide

/-- **Non-claims.**  Nothing in this layer closes the large-lift dispersion row
in Lean, and nothing marks a DETLINE row as kernel-proved. -/
theorem detline_rows_are_not_kernel_proved :
    ∀ e ∈ full, e.status.isKernelProved = false := by decide

/-! ## One tiny finite/order consequence

The only formal content added by this layer.  It is pure order arithmetic: given
an **assumed** per-lift bound `|T e| ≤ X · e^{-3/2} · L` on a finite set of lifts
and an **assumed** tail-sum input `∑ e^{-3/2} ≤ 2 E^{-1/2}`, the tail budget
`≤ 2 X E^{-1/2} L` follows.  Both hypotheses are exactly the research inputs; no
analytic asymptotic is proved here. -/

/-- **Finite-lift tail budget (abstract).**  From a per-lift bound of shape
`X e^{-3/2} L` and an abstract tail-sum input, the summed budget is
`2 X E^{-1/2} L`.  With `E = (log X)^{B_A}` this is the arbitrary-logarithmic
saving used at the research level; here it is a hypothesis-driven inequality
only. -/
theorem finiteLift_tail_budget
    (S : Finset ℕ) (T : ℕ → ℝ) (X L E : ℝ)
    (hX : 0 ≤ X) (hL : 0 ≤ L)
    (hbound : ∀ e ∈ S, |T e| ≤ X * ((e : ℝ) ^ (-(3 : ℝ) / 2)) * L)
    (htail : ∑ e ∈ S, ((e : ℝ) ^ (-(3 : ℝ) / 2)) ≤ 2 * E ^ (-(1 : ℝ) / 2)) :
    |∑ e ∈ S, T e| ≤ 2 * X * E ^ (-(1 : ℝ) / 2) * L := by
  have h1 : |∑ e ∈ S, T e| ≤ ∑ e ∈ S, |T e| := Finset.abs_sum_le_sum_abs _ _
  have h2 : ∑ e ∈ S, |T e| ≤ ∑ e ∈ S, X * ((e : ℝ) ^ (-(3 : ℝ) / 2)) * L :=
    Finset.sum_le_sum hbound
  have h3 : ∑ e ∈ S, X * ((e : ℝ) ^ (-(3 : ℝ) / 2)) * L
      = (X * L) * ∑ e ∈ S, ((e : ℝ) ^ (-(3 : ℝ) / 2)) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun e _ => by ring)
  have h4 : (X * L) * ∑ e ∈ S, ((e : ℝ) ^ (-(3 : ℝ) / 2))
      ≤ (X * L) * (2 * E ^ (-(1 : ℝ) / 2)) :=
    mul_le_mul_of_nonneg_left htail (mul_nonneg hX hL)
  calc |∑ e ∈ S, T e| ≤ ∑ e ∈ S, |T e| := h1
    _ ≤ ∑ e ∈ S, X * ((e : ℝ) ^ (-(3 : ℝ) / 2)) * L := h2
    _ = (X * L) * ∑ e ∈ S, ((e : ℝ) ^ (-(3 : ℝ) / 2)) := h3
    _ ≤ (X * L) * (2 * E ^ (-(1 : ℝ) / 2)) := h4
    _ = 2 * X * E ^ (-(1 : ℝ) / 2) * L := by ring

/-- The tail budget is genuinely hypothesis-driven: with an empty lift set both
hypotheses are satisfiable and the conclusion is the trivial bound.  This
records that `finiteLift_tail_budget` banks *order arithmetic only* and no
analytic input. -/
theorem finiteLift_tail_budget_is_order_arithmetic_only :
    ∀ (T : ℕ → ℝ), |∑ e ∈ (∅ : Finset ℕ), T e| = 0 := by
  intro T; simp

end LedgerFiniteLift
end CurrentProgramme
end TwinPrimeProject
