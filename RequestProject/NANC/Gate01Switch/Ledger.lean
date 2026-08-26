import RequestProject.NANC.Gate01Switch.AnalyticInterfaces
import RequestProject.NANC.Gate01Switch.RepeatedPrime
import RequestProject.NANC.Gate01Switch.WellFactorable
import RequestProject.NANC.Gate01Switch.VaughanSwitchIdentity
import RequestProject.NANC.Gate01Switch.ExponentGeometry

/-!
# Gate01Switch: the decidable switched-branch status ledger

A machine-checkable table of every item of the switched bank.  Only genuinely
finite, Lean-proved items carry `Proved`; every analytic statement is
`ExplicitInterface` or `AnalyticOpen`, and every unverified source claim is
`SourceOpen`.  The consistency theorems below make a silent upgrade of an
interface impossible.

Documented source discrepancies (SOURCE WINS):

* the archive's `finiteDiscrepancy` uses a fixed natural residue `a`; the
  switched progression `n ≡ -2 (mod q)` cannot be encoded by one universal
  natural `a`, so the switched bank defines it by divisibility and records the
  exact bridge `finiteDiscrepancy_eq_discrMinusTwo`;
* the archive has **no** `c₉ = κ_j(α_j * β_{9-j}) + E_j` identity, so
  `R9_CELL_CONVOLUTION` is `SourceOpen` and the shape is only ever a
  hypothesis;
* the archive's `lambda3` has codomain `ℝ` with Mathlib's `Λ`, which is the
  convention used throughout.
-/

namespace TwinPrimeProject
namespace Gate01Switch

/-- Items of the switched bank. -/
inductive Item
  /-- The residue `-2` repair and its boundary analysis. -/
  | ResidueMinusTwo
  /-- Reuse of the archive `lambda3`. -/
  | Lambda3Source
  /-- The prime-power expansion of `λ₃`. -/
  | Lambda3PrimePower
  /-- The squarefree specialization of `λ₃`. -/
  | Lambda3Squarefree
  /-- The exact SW0 → SW1 reindexing. -/
  | SW0SW1
  /-- The exact SW1 → SW2 divisor-pair opening. -/
  | SW1SW2
  /-- The exact prime / higher-prime-power decomposition. -/
  | PrimePowerDecomposition
  /-- The analytic sparse bound for the higher-prime-power stratum. -/
  | PrimePowerAnalyticBound
  /-- The finite repeated-prime algebra. -/
  | RepeatedPAlgebra
  /-- The analytic sparse bound for the repeated-prime stratum. -/
  | RepeatedPAnalyticBound
  /-- The generic switched operator and the exact three-way split. -/
  | GenericSwitchedOperator
  /-- The rational switched exponent geometry. -/
  | SwitchedExponentGeometry
  /-- The finite local well-factorability obstruction. -/
  | WellFactorableLocalObstruction
  /-- The global well-factorability conclusion. -/
  | WellFactorableGlobalConclusion
  /-- The Vaughan divisor-switch identity `P₃ = Λ - P₁ + P₂`. -/
  | VaughanSwitchIdentity
  /-- The `r = 9` cell convolution identity (C9). -/
  | R9CellConvolution
  /-- The Q5 equation `mn + 2 = dpr` and its exact reindexing. -/
  | Q5Equation
  /-- The Q5 analytic cancellation. -/
  | Q5AnalyticBound
  /-- The actual switched coefficient dictionary. -/
  | ActualCDictionary
  /-- The actual switched main-term dictionary. -/
  | ActualEDictionary
  /-- Gate 0 coverage for the switched branch. -/
  | Gate0SwitchedCoverage
  /-- Exhaustion of all high-`P₃` operators by direct + switched. -/
  | Gate0ExhaustiveOperatorCoverage
  /-- Gate 1B. -/
  | Gate1B
  deriving DecidableEq, Repr

/-- Status codes. -/
inductive Status
  /-- Proved in Lean as finite algebra, with no analytic input. -/
  | Proved
  /-- A named proposition that is never inhabited here. -/
  | ExplicitInterface
  /-- An open source-level obligation: the archive does not contain it. -/
  | SourceOpen
  /-- An open analytic input. -/
  | AnalyticOpen
  /-- Refuted and retired. -/
  | FalseRetired
  /-- Not audited. -/
  | NotAudited
  deriving DecidableEq, Repr

/-- The switched-branch ledger. -/
def status : Item → Status
  | .ResidueMinusTwo => .Proved
  | .Lambda3Source => .Proved
  | .Lambda3PrimePower => .Proved
  | .Lambda3Squarefree => .Proved
  | .SW0SW1 => .Proved
  | .SW1SW2 => .Proved
  | .PrimePowerDecomposition => .Proved
  | .PrimePowerAnalyticBound => .ExplicitInterface
  | .RepeatedPAlgebra => .Proved
  | .RepeatedPAnalyticBound => .ExplicitInterface
  | .GenericSwitchedOperator => .Proved
  | .SwitchedExponentGeometry => .Proved
  | .WellFactorableLocalObstruction => .Proved
  | .WellFactorableGlobalConclusion => .SourceOpen
  | .VaughanSwitchIdentity => .Proved
  | .R9CellConvolution => .SourceOpen
  | .Q5Equation => .Proved
  | .Q5AnalyticBound => .AnalyticOpen
  | .ActualCDictionary => .SourceOpen
  | .ActualEDictionary => .SourceOpen
  | .Gate0SwitchedCoverage => .SourceOpen
  | .Gate0ExhaustiveOperatorCoverage => .SourceOpen
  | .Gate1B => .AnalyticOpen

/-- The finite items banked in this run. -/
def switchedFiniteBank : List Item :=
  [.ResidueMinusTwo, .Lambda3Source, .Lambda3PrimePower, .Lambda3Squarefree,
   .SW0SW1, .SW1SW2, .PrimePowerDecomposition, .RepeatedPAlgebra,
   .GenericSwitchedOperator, .SwitchedExponentGeometry,
   .WellFactorableLocalObstruction, .VaughanSwitchIdentity, .Q5Equation]

/-- **Every finite item of the switched bank is proved.** -/
theorem switchedFiniteBank_proved : ∀ i ∈ switchedFiniteBank, status i = .Proved := by decide

/-- The analytic and source-open items of the switched branch. -/
def switchedAnalyticItems : List Item :=
  [.PrimePowerAnalyticBound, .RepeatedPAnalyticBound, .WellFactorableGlobalConclusion,
   .R9CellConvolution, .Q5AnalyticBound, .ActualCDictionary, .ActualEDictionary,
   .Gate0SwitchedCoverage, .Gate0ExhaustiveOperatorCoverage, .Gate1B]

/-- **No analytic or source-open item is marked proved.** -/
theorem switchedAnalyticItems_not_proved :
    ∀ i ∈ switchedAnalyticItems, status i ≠ .Proved := by decide

/-- The two lists are exactly complementary: nothing is unclassified. -/
theorem switched_items_classified :
    ∀ i : Item, i ∈ switchedFiniteBank ∨ i ∈ switchedAnalyticItems := by
  intro i; cases i <;> decide

/-- Gate 0 coverage for the switched branch is not proved. -/
theorem gate0Coverage_not_proved : status .Gate0SwitchedCoverage = .SourceOpen := by decide

/-- Exhaustion of the high-`P₃` operators is not proved. -/
theorem gate0Exhaustion_not_proved :
    status .Gate0ExhaustiveOperatorCoverage = .SourceOpen := by decide

/-- Gate 1B is not proved. -/
theorem gate1B_not_proved : status .Gate1B = .AnalyticOpen := by decide

/-- The Q5 analytic cancellation is not proved. -/
theorem q5Analytic_not_proved : status .Q5AnalyticBound = .AnalyticOpen := by decide

/-- The prime-power sparse bound is an interface only. -/
theorem primePowerBound_interface :
    status .PrimePowerAnalyticBound = .ExplicitInterface := by decide

/-- The repeated-prime sparse bound is an interface only. -/
theorem repeatedPBound_interface :
    status .RepeatedPAnalyticBound = .ExplicitInterface := by decide

/-- `WF_GLOBAL_NOT_PROVED`: no global non-well-factorability of `lambda3` is
claimed. -/
theorem wellFactorableGlobal_not_proved :
    status .WellFactorableGlobalConclusion = .SourceOpen := by decide

/-- The `r = 9` cell convolution identity is a source-open claim. -/
theorem r9CellConvolution_sourceOpen : status .R9CellConvolution = .SourceOpen := by decide

end Gate01Switch
end TwinPrimeProject
