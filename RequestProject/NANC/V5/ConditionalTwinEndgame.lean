/-
NANC V5 — THE CONDITIONAL SHIFTED-PRIME TWIN ENDGAME.

The endgame package collects *all* inputs the shifted-prime route needs, and
carries its own conclusion (positivity of the weighted twin mass) as a field:
no deep analysis is hidden in a proof term.

What is genuinely proved here is only the last, finite step — already banked in
V4 — namely that positive weighted twin mass produces a twin-prime pair, and its
iteration to infinitude *conditional* on an uninhabited eventual-positivity
interface.  Twin-prime infinitude is NOT declared.
-/
import Mathlib
import RequestProject.NANC.V5.Gate2Interfaces

namespace NANC.V5

open NANC.V4

/-- The data of a shifted-prime endgame instance. -/
structure EndgameData where
  /-- The Theorem-8.2 splice parameters. -/
  splice : T82SpliceData
  /-- The geometric mass function of the exceptional region, indexed by `ε`. -/
  mass : ℚ → ℝ
  /-- The constant in the Theorem-8.3 mass bound. -/
  C83 : ℝ
  /-- Positivity of the sieve-conversion constant. -/
  positiveSieveConstant : Prop
  /-- The finite window in which twin mass is measured. -/
  window : Finset ℕ

/-- **The shifted-prime endgame package (UNINHABITED).**

Fields: comparison regularity, Gate-0 Type I, full Type II, the Theorem-8.2
splice, the Theorem-8.3 geometric mass, a positive sieve constant — and the
conclusion, positivity of the weighted twin mass in the window. -/
structure ShiftedPrimeEndgamePackage (E : EndgameData) : Prop where
  /-- Comparison regularity for the candidate sequence. -/
  comparisonRegularity : TwinComparisonRegularityPackage E.splice.comparison
  /-- The Gate-0 Type-I input. -/
  gate0TypeI : Gate0FMTypeI E.splice.X E.splice.mRange E.splice.intervals
    E.splice.tauWeight E.splice.w E.splice.typeITarget
  /-- The full arbitrary-coefficient Type-II input. -/
  fullTypeII : FullFMTypeIIAtOneSixth E.splice.X E.splice.mRangeOf E.splice.nRangeOf
    E.splice.dwM E.splice.dwN E.splice.wC E.splice.eps E.splice.typeIITarget
  /-- The Theorem-8.2 shifted-prime splice. -/
  theorem82Splice : FMShiftedPrimeT82Splice E.splice
  /-- The Theorem-8.3 geometric-mass bound. -/
  theorem83Mass : FMTheorem83H2Mass E.mass E.C83
  /-- Positivity of the sieve-conversion constant. -/
  positiveSieveConstant : E.positiveSieveConstant
  /-- The conclusion the package is supposed to deliver. -/
  weightedTwinMassPositive : 0 < weightedTwinMass E.window

namespace ShiftedPrimeEndgamePackage

variable {E : EndgameData}

theorem proj_splice (P : ShiftedPrimeEndgamePackage E) : FMShiftedPrimeT82Splice E.splice :=
  P.theorem82Splice

theorem proj_mass (P : ShiftedPrimeEndgamePackage E) : FMTheorem83H2Mass E.mass E.C83 :=
  P.theorem83Mass

theorem proj_twinMass (P : ShiftedPrimeEndgamePackage E) : 0 < weightedTwinMass E.window :=
  P.weightedTwinMassPositive

end ShiftedPrimeEndgamePackage

/-- **Conditional endgame conclusion.**  An endgame package yields an explicit
twin-prime pair inside its window.  Only the V4 finite lemma is used; every
analytic input is a field of the package. -/
theorem endgamePackage_gives_twin_pair {E : EndgameData} (P : ShiftedPrimeEndgamePackage E) :
    ∃ p ∈ E.window, Nat.Prime p ∧ Nat.Prime (p + 2) :=
  positive_weightedTwinMass_exists_twin P.weightedTwinMassPositive

/-- **Interface (UNINHABITED).**  Endgame packages exist with windows arbitrarily
far out.  This is precisely the eventual positivity that the analysis would have
to supply; it is never supplied here. -/
def EndgamePackagesAtAllScales : Prop :=
  ∀ N : ℕ, ∃ E : EndgameData, (∀ p ∈ E.window, N ≤ p) ∧ ShiftedPrimeEndgamePackage E

/-- **Conditional infinitude.**  If endgame packages existed at all scales, there
would be infinitely many twin primes.  The hypothesis is an uninhabited interface,
so nothing unconditional is claimed. -/
theorem endgamePackagesAtAllScales_imp_infinitely_many_twins
    (h : EndgamePackagesAtAllScales) :
    {p : ℕ | Nat.Prime p ∧ Nat.Prime (p + 2)}.Infinite := by
  refine eventuallyPositiveTwinMass_imp_infinite ?_
  intro N
  obtain ⟨E, hwin, P⟩ := h N
  exact ⟨E.window, hwin, P.weightedTwinMassPositive⟩

/-- Provenance: the endgame package is a dependency record, never an assertion
that the dependencies hold. -/
def endgameProvenance : Provenance where
  status := AuditStatus.uninhabited
  sourceName := "shifted-prime twin endgame package"
  sourceVersion := "NANC V5"
  scope := "dependency DAG only"
  notes := "Twin-prime infinitude is NOT declared; only a conditional implication is proved."

theorem endgameProvenance_not_leanEvidence :
    Provenance.IsLeanEvidence endgameProvenance = false := rfl

end NANC.V5
