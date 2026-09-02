/-
# Universal / D0WP — the OTHER45 conditional compiler

**Status of this module: CONDITIONAL_KERNEL.**

Given

* the RUN1B source-exact conclusion (a bound for the RUN1B-routed rows),
* the ultra provider conclusion (a bound for the ultra residual rows),
* the existing Gate0 / local / HB-reassembly router conclusions,

the deterministic router assembles them into a bound for

```
FM722-OTHERPARENT-LINEARHB-SELECTE-ANCHOR2-LONGLINE45.
```

The assembly is finite and exact: the router partitions the rows, so no saving
is counted twice.  Research status of the *inputs*:
`PAPER_CLOSED_PENDING_SOURCE_AUDIT`.  Nothing analytic is proved here.
-/
import Universal.D0WP.OtherParentRouter
import Universal.D0WP.FinitePacketCompiler

namespace Universal.D0WP

open Finset

/-- **OTHER45 CONDITIONAL COMPILER (kernel-proved implication).**

`Bd r` is the bound available for the rows routed to `r`; the conclusion is the
sum of the five route bounds. -/
theorem other45_conditional {ι : Type*} [DecidableEq ι]
    (rows : Finset ι) (rd : ι → RowData) (F : ι → ℂ) (Bd : Route → ℝ)
    (hgate0 : ‖∑ i ∈ rows.filter (fun i => route (rd i) = Route.gate0), F i‖
      ≤ Bd Route.gate0)
    (hlocal : ‖∑ i ∈ rows.filter (fun i => route (rd i) = Route.localBranch), F i‖
      ≤ Bd Route.localBranch)
    (hrun1b : ‖∑ i ∈ rows.filter (fun i => route (rd i) = Route.run1b), F i‖
      ≤ Bd Route.run1b)
    (hhb : ‖∑ i ∈ rows.filter (fun i => route (rd i) = Route.hbReassembly), F i‖
      ≤ Bd Route.hbReassembly)
    (hultra : ‖∑ i ∈ rows.filter (fun i => route (rd i) = Route.thetaUltra), F i‖
      ≤ Bd Route.thetaUltra) :
    ‖∑ i ∈ rows, F i‖ ≤ ∑ r : Route, Bd r := by
  refine owner_bound_assembly rows (fun i => route (rd i)) F Bd ?_
  intro k
  cases k
  · exact hgate0
  · exact hlocal
  · exact hrun1b
  · exact hhb
  · exact hultra

end Universal.D0WP
