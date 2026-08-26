import Mathlib

/-!
# Route-A fibre frame: permanent namespace repair

This file fixes, once and for all, the naming of the sectors that were previously
written with decorated symbols (`V★`, `T₀★`, `T*`).  The decorated names were
ambiguous and caused old *analytically closed* sectors to be confused with the
new, analytically **open** Route-A edge variance.

Nothing in this file asserts an analytic theorem.  It only records names, their
mutual distinctness, and their bank status as data.
-/

namespace RouteAFibreFrame

/-- The sectors of the Route-A fibre frame, under their repaired names. -/
inductive Sector
  /-- Old `V★` analytic sector; closed outside Lean by zero-frequency
  reassembly and the multiplicative large sieve. -/
  | V_BDH
  /-- Old `T₀★` analytic sector; closed outside Lean after the CRT repair and
  the multiplicative large sieve. -/
  | T0_CRT
  /-- The separate, older shifted operator.  It must **not** be identified with
  the new Route-A variance. -/
  | Tsh_SHIFT
  /-- The new Route-A edge variance, formerly written `T*`.  Analytically open. -/
  | V_ROUTE_A
  /-- The sufficient one-row fourth-moment theorem.  Analytically open. -/
  | FF4
  /-- The remaining one-row mixed-prime covariance.  Analytically open, and
  related to the CDV mixed covariance. -/
  | FF4_MIX
  deriving DecidableEq, Repr

/-- Bank status of a sector. -/
inductive BankStatus
  /-- Closed by an argument carried out outside Lean; inside Lean it may only be
  used as an explicit hypothesis. -/
  | ClosedOutsideLean
  /-- A separate legacy object, retained only to keep it distinct. -/
  | LegacySeparate
  /-- Analytically open. -/
  | AnalyticallyOpen
  deriving DecidableEq, Repr

/-- The status ledger. -/
def status : Sector → BankStatus
  | .V_BDH => .ClosedOutsideLean
  | .T0_CRT => .ClosedOutsideLean
  | .Tsh_SHIFT => .LegacySeparate
  | .V_ROUTE_A => .AnalyticallyOpen
  | .FF4 => .AnalyticallyOpen
  | .FF4_MIX => .AnalyticallyOpen

/-- The new Route-A edge variance is a *different* sector from the old `V★`. -/
theorem routeA_ne_VBDH : Sector.V_ROUTE_A ≠ Sector.V_BDH := by decide

/-- The new Route-A edge variance is a *different* sector from the old `T₀★`. -/
theorem routeA_ne_T0CRT : Sector.V_ROUTE_A ≠ Sector.T0_CRT := by decide

/-- The new Route-A edge variance is a *different* sector from the old shifted
operator. -/
theorem routeA_ne_Tsh : Sector.V_ROUTE_A ≠ Sector.Tsh_SHIFT := by decide

/-- The three sectors that remain analytically open are exactly
`V_ROUTE_A`, `FF4`, `FF4_MIX`. -/
theorem open_sectors (s : Sector) :
    status s = BankStatus.AnalyticallyOpen ↔
      s = Sector.V_ROUTE_A ∨ s = Sector.FF4 ∨ s = Sector.FF4_MIX := by
  cases s <;> simp [status]

/-- No sector that is closed outside Lean is one of the open Route-A sectors. -/
theorem closed_sectors (s : Sector) :
    status s = BankStatus.ClosedOutsideLean ↔ s = Sector.V_BDH ∨ s = Sector.T0_CRT := by
  cases s <;> simp [status]

end RouteAFibreFrame
