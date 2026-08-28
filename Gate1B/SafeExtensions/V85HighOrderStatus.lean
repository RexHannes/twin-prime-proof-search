/-
# Gate 1B v8.5 — updated high-order routing status

**Status: PROVED_FINITE (a finite status record; no analytic content).**

The record is deliberately coarse: each node carries one of a small set of
status tags, and no tag says "closed" for anything that is not closed.
-/
import Mathlib

namespace Gate1B.SafeExtensions

/-- Status tags used by the v8.5 routing record. -/
inductive V85Status
  /-- Banked in an earlier version (finite / algebraic). -/
  | Banked
  /-- Research-level analytic closure *conditional* on explicitly supplied
  source / common-sequence / large-sieve inputs, plus a banked capacity margin. -/
  | ConditionalCompiler
  /-- A separate open node. -/
  | Open
  deriving DecidableEq, Repr

/-- The high-order routing nodes tracked at v8.5. -/
inductive V85Node
  /-- Defect orders 1–4. -/
  | Orders1to4
  /-- H6 regroup geometry (shares the QK order-5 analytic residuals). -/
  | H6
  /-- H7 short-short (`alpha, beta < 4/9`). -/
  | H7ShortShort
  /-- H7 high-prime complement (`max(alpha, beta) ≥ 4/9`). -/
  | H7HighPrimeComplement
  /-- H8 robustness audit. -/
  | H8
  /-- H9 explicit Type-II residual. -/
  | H9
  /-- The same-`q` node. -/
  | SameQ
  /-- The D₁₂ moving-`D` node. -/
  | D12MovingD
  /-- The `R_E` source interface. -/
  | RE
  /-- Gate 1B itself. -/
  | Gate1B
  deriving DecidableEq, Repr

/-- The v8.5 routing status. -/
def v85Status : V85Node → V85Status
  | .Orders1to4 => .Banked
  | .H6 => .Banked
  | .H7ShortShort => .ConditionalCompiler
  | .H7HighPrimeComplement => .Open
  | .H8 => .Open
  | .H9 => .Open
  | .SameQ => .Open
  | .D12MovingD => .Open
  | .RE => .Open
  | .Gate1B => .Open

/-- H7 short-short is the only node upgraded at v8.5, and only to
`ConditionalCompiler`. -/
theorem v85_h7ShortShort : v85Status .H7ShortShort = .ConditionalCompiler := rfl

/-- The H7 high-prime complement stays open and separate. -/
theorem v85_h7Complement_open : v85Status .H7HighPrimeComplement = .Open := rfl

/-- Gate 1B remains open. -/
theorem v85_gate1B_open : v85Status .Gate1B = .Open := rfl

/-- No node is marked "closed": the tag does not exist.  Every node is either
previously banked finite material, the H7 conditional compiler, or open. -/
theorem v85_no_closed_tag (n : V85Node) :
    v85Status n = .Banked ∨ v85Status n = .ConditionalCompiler ∨ v85Status n = .Open := by
  cases n <;> simp [v85Status]

end Gate1B.SafeExtensions
