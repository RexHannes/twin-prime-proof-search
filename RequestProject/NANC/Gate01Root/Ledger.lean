import RequestProject.NANC.Gate01Root.ExponentLedger

/-!
# Gate01Root: the ROOT-COLLAPSE / R4C / PPD route ledger

Machine-checkable status of every item of the new bank.  As in the Gate 0–1
ledger the only `Proved` items are the finite statements actually proved in this
development; every analytic item is `OpenAnalytic`, `Conditional` or
`Interface`; and `FULL_TYPE_II`, `FCPT`, `TWIN_PRIME` remain `Open`.

No Gate 0–4 closure, no Type II, no FCPT and no twin-prime claim is made.
-/

namespace RouteAFibreFrame
namespace Gate01Root

/-- Items of the root-route bank. -/
inductive Item
  /-- Affine root data and the identities `m'α - mβ = 2k`, `rβ = m'w₀ + 2`. -/
  | RootAffine
  /-- The BAL residue theorem and its CRT projections. -/
  | Bal
  /-- The exact CRT roots `t_p`, `t_q`, `T_{pq}`. -/
  | CrtRoots
  /-- ROOT-COLLAPSE: divisibility, residues, rational identity. -/
  | RootCollapse
  /-- Root-collision determinants and rigidity. -/
  | RootCollisions
  /-- Divisor-relaxed row injection and the divisor cardinal comparison. -/
  | DivisorRows
  /-- The exact finite fourth-moment row/column duality. -/
  | MatrixFourthMoment
  /-- The conditional R4C implications. -/
  | R4CImplication
  /-- The conditional repeated-`p` bound. -/
  | RepeatedPConditional
  /-- The PPD interface and the exact `PPD + repeated-p ⇒ R4C` implication. -/
  | PpdInterface
  /-- The SOURCE-G consistency module (exact identities only). -/
  | SourceGConsistency
  /-- HIT-p: open analytic input. -/
  | HitP
  /-- R4C as an analytic estimate: open. -/
  | R4CAnalytic
  /-- PPD as an analytic estimate: the first open analytic input. -/
  | Ppd
  /-- Exhaustive weighted clean-edge coverage: open source obligation. -/
  | Gate0Coverage
  /-- Gate 1: conditional on PPD. -/
  | Gate1
  /-- Full Type II. -/
  | FullTypeII
  /-- FCPT. -/
  | FCPT
  /-- The twin-prime statement. -/
  | TwinPrime
  deriving DecidableEq, Repr

/-- Status codes. -/
inductive Status
  /-- Proved in Lean as finite algebra, with no analytic input. -/
  | Proved
  /-- A conditional implication banked without its hypotheses. -/
  | Conditional
  /-- Recorded as an interface supplied from outside Lean. -/
  | Interface
  /-- An open analytic input, not proved anywhere here. -/
  | OpenAnalytic
  /-- An open source-level obligation. -/
  | OpenSource
  /-- Provisional, awaiting independent audit. -/
  | AwaitingAudit
  /-- Open. -/
  | Open
  deriving DecidableEq, Repr

/-- The route ledger. -/
def status : Item → Status
  | .RootAffine => .Proved
  | .Bal => .Proved
  | .CrtRoots => .Proved
  | .RootCollapse => .Proved
  | .RootCollisions => .Proved
  | .DivisorRows => .Proved
  | .MatrixFourthMoment => .Proved
  | .R4CImplication => .Conditional
  | .RepeatedPConditional => .Conditional
  | .PpdInterface => .Interface
  | .SourceGConsistency => .AwaitingAudit
  | .HitP => .OpenAnalytic
  | .R4CAnalytic => .OpenAnalytic
  | .Ppd => .OpenAnalytic
  | .Gate0Coverage => .OpenSource
  | .Gate1 => .Conditional
  | .FullTypeII => .Open
  | .FCPT => .Open
  | .TwinPrime => .Open

/-- The finite items banked in this run. -/
def finiteBanked : List Item :=
  [.RootAffine, .Bal, .CrtRoots, .RootCollapse, .RootCollisions, .DivisorRows,
   .MatrixFourthMoment]

/-- **Every finite item of the root route is proved.** -/
theorem rootRouteFiniteBank_proved : ∀ i ∈ finiteBanked, status i = .Proved := by decide

/-- The analytic (and source) items of the route. -/
def analyticItems : List Item :=
  [.HitP, .R4CAnalytic, .Ppd, .Gate0Coverage, .Gate1, .FullTypeII, .FCPT, .TwinPrime]

/-- **No analytic item is marked proved.** -/
theorem rootRouteAnalyticItems_not_proved : ∀ i ∈ analyticItems, status i ≠ .Proved := by
  decide

/-- PPD is the first open analytic input. -/
theorem ppd_open : status .Ppd = .OpenAnalytic := by decide

/-- R4C as an analytic estimate is open. -/
theorem r4cAnalytic_open : status .R4CAnalytic = .OpenAnalytic := by decide

/-- HIT-p is open. -/
theorem hitP_open : status .HitP = .OpenAnalytic := by decide

/-- The exhaustive weighted clean-edge coverage is an open source obligation. -/
theorem gate0Coverage_open : status .Gate0Coverage = .OpenSource := by decide

/-- Gate 1 is only conditional on PPD. -/
theorem gate1_conditional_on_ppd : status .Gate1 = .Conditional := by decide

/-- The R4C implication is banked only conditionally. -/
theorem r4cImplication_conditional : status .R4CImplication = .Conditional := by decide

/-- The repeated-`p` bound is banked only conditionally. -/
theorem repeatedPConditional_conditional : status .RepeatedPConditional = .Conditional := by
  decide

/-- The PPD module is an interface. -/
theorem ppdInterface_banked : status .PpdInterface = .Interface := by decide

/-- The SOURCE-G consistency module awaits an independent audit. -/
theorem sourceGConsistency_conditional : status .SourceGConsistency = .AwaitingAudit := by
  decide

/-- Full Type II remains open. -/
theorem fullTypeII_open : status .FullTypeII = .Open := by decide

/-- FCPT remains open. -/
theorem fcpt_open : status .FCPT = .Open := by decide

/-- The twin-prime statement remains open. -/
theorem twinPrime_open : status .TwinPrime = .Open := by decide

end Gate01Root
end RouteAFibreFrame
