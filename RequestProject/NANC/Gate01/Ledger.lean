import RequestProject.NANC.Gate01.DStarInterfaces
import RequestProject.NANC.Gate01.SlotDictionaryAudit

/-!
# Gate 0–1 status ledger

The ledger records, as machine-checkable data, the status of every Gate 0–1
item of this bank.  It is deliberately conservative: the only items with status
`Proved` are the finite algebraic statements actually proved in this
development; every analytic item is `OpenAnalytic`, `Conditional` or
`Interface`; and `FULL_TYPE_II`, `FCPT`, `TWIN_PRIME` are explicitly `Open`.

No Gate 0 or Gate 1 closure is claimed.
-/

namespace RouteAFibreFrame
namespace Gate01

/-- The Gate 0–1 bank items. -/
inductive Item
  /-- `CANONICAL_CONGRUENCE_BANKED`. -/
  | CanonicalCongruence
  /-- `GENERIC_CRT_RESIDUE_BANKED`. -/
  | GenericCRTResidue
  /-- `H_ZERO_CENTERING_CANCELLATION_BANKED`. -/
  | HZeroCentering
  /-- `SAME_PRIME_NO_JOINT_HIT_BANKED`. -/
  | SamePrimeNoJointHit
  /-- `EXCEPTIONAL_ROW_NO_HIT_BANKED`. -/
  | ExceptionalRowNoHit
  /-- `RAMANUJAN_MINUS_ONE_REMAINDER_BANKED`. -/
  | RamanujanRemainder
  /-- `COMP_GENERIC_COMPLETION_INTERFACE`. -/
  | CompGenericCompletion
  /-- `STRUCTURED_DSTAR_OPEN_ANALYTIC_INPUT`. -/
  | StructuredDStar
  /-- `ARBITRARY_DSTAR_STRONGER_OPEN_ANALYTIC_INPUT`. -/
  | ArbitraryDStar
  /-- `DSTAR_IMP_AVG_COV_CONDITIONAL_BANKED`. -/
  | DStarImpliesAvgCov
  /-- `AVG_COV`. -/
  | AvgCov
  /-- `GENERIC_HIGH_P3_CLOSURE`. -/
  | GenericHighP3Closure
  /-- `OLD_DIRECT_BC_SLOT_DICTIONARY_FALSE_FOR_COMP_REPRESENTATION`. -/
  | OldDirectBCSlotDictionary
  /-- `FULL_TYPE_II`. -/
  | FullTypeII
  /-- `FCPT`. -/
  | FCPT
  /-- `TWIN_PRIME`. -/
  | TwinPrime
  deriving DecidableEq, Repr

/-- Status codes of the Gate 0–1 ledger. -/
inductive Status
  /-- Proved in Lean as finite algebra, with no analytic input. -/
  | Proved
  /-- Recorded as an interface: the content is supplied from outside Lean. -/
  | ConditionalInterface
  /-- An open analytic input; not proved anywhere here. -/
  | OpenAnalytic
  /-- A conditional implication banked without its hypotheses. -/
  | Conditional
  /-- Open both at the source level and analytically. -/
  | OpenSourceAndAnalytic
  /-- Audited negative result about a representation, of restricted scope. -/
  | Audited
  /-- Open. -/
  | Open
  deriving DecidableEq, Repr

/-- The Gate 0–1 status ledger. -/
def status : Item → Status
  | .CanonicalCongruence => .Proved
  | .GenericCRTResidue => .Proved
  | .HZeroCentering => .Proved
  | .SamePrimeNoJointHit => .Proved
  | .ExceptionalRowNoHit => .Proved
  | .RamanujanRemainder => .Proved
  | .CompGenericCompletion => .ConditionalInterface
  | .StructuredDStar => .OpenAnalytic
  | .ArbitraryDStar => .OpenAnalytic
  | .DStarImpliesAvgCov => .Conditional
  | .AvgCov => .OpenAnalytic
  | .GenericHighP3Closure => .OpenSourceAndAnalytic
  | .OldDirectBCSlotDictionary => .Audited
  | .FullTypeII => .Open
  | .FCPT => .Open
  | .TwinPrime => .Open

/-- The six finite items banked in this run. -/
def bankedFinite : List Item :=
  [.CanonicalCongruence, .GenericCRTResidue, .HZeroCentering,
   .SamePrimeNoJointHit, .ExceptionalRowNoHit, .RamanujanRemainder]

/-- Every banked finite item has status `Proved`. -/
theorem bankedFinite_proved : ∀ i ∈ bankedFinite, status i = .Proved := by decide

/-- The analytic items of the ledger. -/
def analyticItems : List Item :=
  [.CompGenericCompletion, .StructuredDStar, .ArbitraryDStar, .DStarImpliesAvgCov,
   .AvgCov, .GenericHighP3Closure, .FullTypeII, .FCPT, .TwinPrime]

/-- **No analytic item is marked proved.**  In particular `D*`, AVG-COV, the
generic high-`P3` closure, full Type II, FCPT and the twin-prime statement are
not claimed. -/
theorem analyticItems_not_proved : ∀ i ∈ analyticItems, status i ≠ .Proved := by decide

/-- `AVG-COV` is open analytic, not proved. -/
theorem avgCov_open : status .AvgCov = .OpenAnalytic := by decide

/-- `D*` is open analytic, not proved. -/
theorem structuredDStar_open : status .StructuredDStar = .OpenAnalytic := by decide

/-- Full Type II remains open. -/
theorem fullTypeII_open : status .FullTypeII = .Open := by decide

/-- FCPT remains open. -/
theorem fcpt_open : status .FCPT = .Open := by decide

/-- The twin-prime statement remains open. -/
theorem twinPrime_open : status .TwinPrime = .Open := by decide

/-- The old direct Bettin–Chandee slot dictionary is only *audited* (for the
direct COMP representation); no general impossibility is banked. -/
theorem oldSlotDictionary_audited : status .OldDirectBCSlotDictionary = .Audited := by decide

end Gate01
end RouteAFibreFrame
