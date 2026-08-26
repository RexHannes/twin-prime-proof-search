import RequestProject.NANC.Gate01Root.Ledger
import RequestProject.NANC.Gate01Switch.Ledger

/-!
# Gate 0–1: the combined direct / switched status ledger

A single top-level table recording the state of the two *separate* branches.
It asserts nothing beyond what each branch ledger already records; in
particular it does **not** assert that the direct and switched operators
exhaust the high-`P₃` packets — that remains
`Gate0ExhaustiveOperatorCoverageStatement`, an explicit interface.
-/

namespace TwinPrimeProject
namespace Gate01Combined

/-- The top-level gate items. -/
inductive Item
  /-- The direct/root finite bank (`Gate01Root`). -/
  | DirectFiniteBank
  /-- The direct analytic gate 1A. -/
  | DirectAnalyticGate1A
  /-- The switched finite bank (`Gate01Switch`). -/
  | SwitchedFiniteBank
  /-- The switched analytic gate 1B. -/
  | SwitchedAnalyticGate1B
  /-- Exhaustion of all high-`P₃` operators by direct + switched. -/
  | Gate0OperatorExhaustion
  deriving DecidableEq, Repr

/-- Top-level status codes. -/
inductive Status
  /-- Finite bank complete and proved in Lean. -/
  | Proved
  /-- Open. -/
  | Open
  deriving DecidableEq, Repr

/-- The combined ledger. -/
def status : Item → Status
  | .DirectFiniteBank => .Proved
  | .DirectAnalyticGate1A => .Open
  | .SwitchedFiniteBank => .Proved
  | .SwitchedAnalyticGate1B => .Open
  | .Gate0OperatorExhaustion => .Open

/-- Both finite banks are proved. -/
theorem finiteBanks_proved :
    status .DirectFiniteBank = .Proved ∧ status .SwitchedFiniteBank = .Proved := by decide

/-- Both analytic gates remain open. -/
theorem analyticGates_open :
    status .DirectAnalyticGate1A = .Open ∧ status .SwitchedAnalyticGate1B = .Open := by decide

/-- Operator exhaustion remains open: no claim that direct + switched exhaust
the high-`P₃` packets. -/
theorem operatorExhaustion_open : status .Gate0OperatorExhaustion = .Open := by decide

/-- The switched finite bank entry is backed by the switched ledger. -/
theorem switchedFiniteBank_backed :
    ∀ i ∈ Gate01Switch.switchedFiniteBank, Gate01Switch.status i = .Proved :=
  Gate01Switch.switchedFiniteBank_proved

/-- The switched analytic entry is backed by the switched ledger. -/
theorem switchedAnalytic_backed :
    ∀ i ∈ Gate01Switch.switchedAnalyticItems, Gate01Switch.status i ≠ .Proved :=
  Gate01Switch.switchedAnalyticItems_not_proved

end Gate01Combined
end TwinPrimeProject
