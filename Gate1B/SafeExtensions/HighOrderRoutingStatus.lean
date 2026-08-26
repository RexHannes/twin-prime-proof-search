/-
# Gate 1B v8.3 — high-order routing table

**Status: COMMENTS_ONLY / PROVED_FINITE bookkeeping.**

A finite record of the *structural* status of defect orders `0, …, 9`.  The
status type has exactly three constructors — `structuralBank`, `analyticOpen`,
`sourceOpen` — and there is deliberately **no** `closed` constructor: orders
5–9 are never recorded as closed anywhere in this development.
-/
import Mathlib
import Gate1B.SafeAlgebra.HighOrderRegroupGeometry

namespace Gate1B.SafeExtensions

/-- Structural status of a defect order.  Note the absence of any "closed"
constructor. -/
inductive HighOrderStatus where
  /-- Finite/algebraic structure is banked. -/
  | structuralBank : HighOrderStatus
  /-- The analytic estimate for this order is open. -/
  | analyticOpen : HighOrderStatus
  /-- The source input for this order is open. -/
  | sourceOpen : HighOrderStatus
  deriving DecidableEq, Repr

/-- A node of the high-order routing table. -/
structure HighOrderNode where
  /-- Defect order. -/
  order : ℕ
  /-- Whether the exact regroup geometry is banked. -/
  geometryBanked : Bool
  /-- Status of the analytic child. -/
  analyticStatus : HighOrderStatus
  /-- Human-readable description of the geometric skeleton. -/
  note : String
  deriving Repr

/-- The routing table for defect orders `0, …, 9`. -/
def highOrderStatus : ℕ → HighOrderNode
  | 0 => ⟨0, true, HighOrderStatus.sourceOpen, "model / main source"⟩
  | 1 => ⟨1, true, HighOrderStatus.analyticOpen, "prior banked low-order structure"⟩
  | 2 => ⟨2, true, HighOrderStatus.analyticOpen, "prior banked low-order structure"⟩
  | 3 => ⟨3, true, HighOrderStatus.analyticOpen, "prior banked low-order structure"⟩
  | 4 => ⟨4, true, HighOrderStatus.analyticOpen, "prior banked low-order structure"⟩
  | 5 => ⟨5, true, HighOrderStatus.analyticOpen, "2D QK geometry"⟩
  | 6 => ⟨6, true, HighOrderStatus.analyticOpen, "2D QK regroup geometry"⟩
  | 7 => ⟨7, true, HighOrderStatus.analyticOpen, "2D QK geometry + 1D reciprocal alternative"⟩
  | 8 => ⟨8, true, HighOrderStatus.analyticOpen, "1D reciprocal geometry"⟩
  | 9 => ⟨9, true, HighOrderStatus.analyticOpen, "pure-defect character packet"⟩
  | j + 10 => ⟨j + 10, false, HighOrderStatus.sourceOpen, "out of range"⟩

/-- Every order in range records its regroup geometry as banked. -/
theorem highOrderStatus_geometry_banked (j : ℕ) (h : j ≤ 9) :
    (highOrderStatus j).geometryBanked = true := by
  interval_cases j <;> rfl

/-- Orders 5–9 are recorded as analytically **open**. -/
theorem highOrderStatus_analytic_open (j : ℕ) (h5 : 5 ≤ j) (h9 : j ≤ 9) :
    (highOrderStatus j).analyticStatus = HighOrderStatus.analyticOpen := by
  interval_cases j <;> rfl

/-- The order field is the index. -/
theorem highOrderStatus_order (j : ℕ) (h : j ≤ 9) : (highOrderStatus j).order = j := by
  interval_cases j <;> rfl

/-- Orders up to 7 carry at least two model coordinates, matching the two-model
regroup geometry recorded in the table. -/
theorem highOrderStatus_twoModels (j : ℕ) (h7 : j ≤ 7) :
    2 ≤ Gate1B.SafeAlgebra.remainingModels j :=
  Gate1B.SafeAlgebra.hasTwoModels_of_order_le_seven h7

end Gate1B.SafeExtensions
