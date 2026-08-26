/-
NANC V5 CONTROLLING LAYER — THE CONDITIONAL ENDGAME DAG.

`ShiftedPrimeFMEndgamePackage` makes every dependency of the shifted-prime
Ford–Maynard endgame explicit as a **field**: Gate-0 Type I, comparison
regularity, full arbitrary-coefficient Type II, the controlling `N₂` cell-sum
upper bound, its ε-uniformity, the Theorem-8.3 geometric mass, the positive
sieve certificate, and the conclusion (positivity of the weighted twin mass).

No deep implication is hidden inside a proof term: the conclusion is carried, not
derived.  The only Lean deduction is the finite V4 step

    positive weighted twin mass  ⟹  an explicit twin pair.

Twin-prime infinitude is NOT declared.
-/
import Mathlib
import RequestProject.NANC.V5.Controlling.Gate2Status

namespace NANC.V5.Controlling

open NANC.V4 NANC.V5

/-- All parameters the endgame package speaks about. -/
structure EndgamePackageData where
  /-- Comparison-regularity data for the candidate sequence. -/
  comparison : TwinComparisonData
  /-- The dyadic scale. -/
  X : ℕ
  /-- The shrinking parameter. -/
  eps : ℚ
  /-- Outer range of the Type-I estimate. -/
  mRange : Finset ℕ
  /-- Interval family of the Type-I estimate. -/
  intervals : Finset (Finset ℕ)
  /-- The outer divisor weight. -/
  tauWeight : ℕ → ℝ
  /-- The comparison sequence `w = a - b`. -/
  w : ℕ → ℝ
  /-- Type-I target. -/
  typeITarget : ℝ
  /-- Type-II block ranges, indexed by the exponent. -/
  mRangeOf : ℚ → Finset ℕ
  /-- Type-II inner ranges, indexed by the exponent. -/
  nRangeOf : ℚ → Finset ℕ
  /-- Divisor bound for the outer Type-II coefficients. -/
  dwM : ℕ → ℝ
  /-- Divisor bound for the inner Type-II coefficients. -/
  dwN : ℕ → ℝ
  /-- The complex weight entering the Type-II sums. -/
  wC : ℕ → ℂ
  /-- Type-II target. -/
  typeIITarget : ℝ
  /-- The `H₂` cell data of the exceptional region. -/
  cellData : N2CellData
  /-- The scale entering the `N₂` bound. -/
  n2x : ℝ
  /-- The logarithmic factor entering the `N₂` bound. -/
  n2logx : ℝ
  /-- The admissible error family of the `N₂` bound, indexed by `ε`. -/
  n2errOf : ℚ → ℝ
  /-- The geometric mass function of the exceptional region. -/
  mass : ℚ → ℝ
  /-- The constant of the Theorem-8.3 mass bound. -/
  C83 : ℝ
  /-- The positivity certificate of the sieve-conversion coefficient. -/
  fmPositiveCertificate : Prop
  /-- The finite window in which twin mass is measured. -/
  window : Finset ℕ

/-- **The shifted-prime Ford–Maynard endgame package (UNINHABITED).**

Every dependency is an explicit field; nothing is derived internally. -/
structure ShiftedPrimeFMEndgamePackage (E : EndgamePackageData) : Prop where
  /-- Gate-0 Type I. -/
  gate0TypeI : Gate0FMTypeI E.X E.mRange E.intervals E.tauWeight E.w E.typeITarget
  /-- Comparison regularity (b.1), (b.2), (w). -/
  comparisonRegularity : TwinComparisonRegularityPackage E.comparison
  /-- The full arbitrary-coefficient Type-II hypothesis on `[ε, 1/6 - ε]`. -/
  fullFMTypeII : FullFMTypeIIAtOneSixth E.X E.mRangeOf E.nRangeOf E.dwM E.dwN E.wC E.eps
    E.typeIITarget
  /-- The controlling `N₂` cell-sum upper bound. -/
  n2CellSumUpper : FMN2CellSumUpperAtScale E.cellData E.n2x E.n2logx (E.n2errOf E.eps)
  /-- ε-uniformity of the `N₂` error. -/
  epsilonUniformity : EpsilonUniformN2 E.n2errOf
  /-- The Theorem-8.3 geometric-mass bound. -/
  theorem83Mass : FMTheorem83H2Mass E.mass E.C83
  /-- The positivity certificate for the sieve-conversion coefficient. -/
  fmPositiveCertificate : E.fmPositiveCertificate
  /-- The conclusion the package is supposed to deliver. -/
  weightedTwinMassPositive : 0 < weightedTwinMass E.window

namespace ShiftedPrimeFMEndgamePackage

variable {E : EndgamePackageData}

theorem proj_gate0TypeI (P : ShiftedPrimeFMEndgamePackage E) :
    Gate0FMTypeI E.X E.mRange E.intervals E.tauWeight E.w E.typeITarget := P.gate0TypeI

theorem proj_comparisonRegularity (P : ShiftedPrimeFMEndgamePackage E) :
    TwinComparisonRegularityPackage E.comparison := P.comparisonRegularity

theorem proj_fullFMTypeII (P : ShiftedPrimeFMEndgamePackage E) :
    FullFMTypeIIAtOneSixth E.X E.mRangeOf E.nRangeOf E.dwM E.dwN E.wC E.eps E.typeIITarget :=
  P.fullFMTypeII

theorem proj_n2CellSumUpper (P : ShiftedPrimeFMEndgamePackage E) :
    FMN2CellSumUpperAtScale E.cellData E.n2x E.n2logx (E.n2errOf E.eps) := P.n2CellSumUpper

theorem proj_epsilonUniformity (P : ShiftedPrimeFMEndgamePackage E) :
    EpsilonUniformN2 E.n2errOf := P.epsilonUniformity

theorem proj_theorem83Mass (P : ShiftedPrimeFMEndgamePackage E) :
    FMTheorem83H2Mass E.mass E.C83 := P.theorem83Mass

theorem proj_twinMass (P : ShiftedPrimeFMEndgamePackage E) : 0 < weightedTwinMass E.window :=
  P.weightedTwinMassPositive

end ShiftedPrimeFMEndgamePackage

/-- **The conditional endgame conclusion.**  A package yields an explicit twin pair
in its window, by the finite V4 lemma alone. -/
theorem endgamePackage_gives_twin_pair {E : EndgamePackageData}
    (P : ShiftedPrimeFMEndgamePackage E) : ∃ p ∈ E.window, Nat.Prime p ∧ Nat.Prime (p + 2) :=
  positive_weightedTwinMass_exists_twin P.weightedTwinMassPositive

/-- **Firewall.**  The package is contentful: if the positivity certificate is
`False`, no package exists.  In particular no package can arise from bookkeeping. -/
theorem no_endgamePackage_from_nothing (E : EndgamePackageData)
    (h : E.fmPositiveCertificate = False) : ¬ ShiftedPrimeFMEndgamePackage E := by
  intro P
  have hc := P.fmPositiveCertificate
  rw [h] at hc
  exact hc

/-- Status entry: the endgame DAG is dependency bookkeeping, never a claim that
the dependencies hold. -/
def endgameDagEntry : ControlEntry where
  name := "shifted-prime Ford–Maynard endgame package (dependency DAG)"
  status := ControlStatus.uninhabitedInterface
  notes := "Twin-prime infinitude is NOT declared.  Only the finite twin-pair step is Lean."

theorem endgameDagEntry_not_leanEvidence :
    ControlEntry.IsLeanEvidence endgameDagEntry = false := rfl

/-- Status entry: twin-prime infinitude. -/
def twinInfinitudeEntry : ControlEntry where
  name := "twin-prime infinitude"
  status := ControlStatus.openStatus
  notes := "NOT DECLARED anywhere in this bank."

theorem twinInfinitudeEntry_not_leanEvidence :
    ControlEntry.IsLeanEvidence twinInfinitudeEntry = false := rfl

end NANC.V5.Controlling
