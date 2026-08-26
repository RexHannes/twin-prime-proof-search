/-
NANC V5 — GATE-2 INTERFACES: THE THEOREM-8.2 SHIFTED-PRIME SPLICE AND THE
THEOREM-8.3 GEOMETRIC MASS.

NOTHING IN THIS FILE IS INHABITED, and in particular there is deliberately
**no** theorem called `gate2_closed`: such a theorem could only exist once every
field of the splice below has been supplied.
-/
import Mathlib
import RequestProject.NANC.V5.FullTypeIIInterface

namespace NANC.V5

open NANC.V4

/-- All the parameters the shifted-prime Theorem-8.2 splice speaks about. -/
structure T82SpliceData where
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
  /-- Outer divisor weight. -/
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
  /-- The exceptional region. -/
  region : N2RegionData
  /-- The `N₂` constant family, indexed by `ε`. -/
  n2Constants : N2ConstantFamily
  /-- Parameters of the `N₂` bound: constant, scale, log-scale, error. -/
  n2C : ℝ
  /-- The scale entering the `N₂` bound. -/
  n2x : ℝ
  /-- The logarithmic factor entering the `N₂` bound. -/
  n2logx : ℝ
  /-- The admissible error in the `N₂` bound. -/
  n2err : ℝ
  /-- The published Ford–Maynard analytic inputs outside the `N₂` region. -/
  externalNonN2Inputs : Prop
  /-- The assertion that the shifted-prime substitution is legal inside the
  source's Theorem-8.2 argument. -/
  substitutionLegal : Prop

/-- **The Theorem-8.2 shifted-prime splice (UNINHABITED).**

Every hypothesis the splice needs is a field: comparison regularity, Gate-0
Type I, full Type II on `[ε, 1/6-ε]`, the `N₂` shifted-prime upper bound, its
ε-uniformity, the published non-`N₂` analytic inputs, and the legality of the
substitution itself. -/
structure FMShiftedPrimeT82Splice (S : T82SpliceData) : Prop where
  /-- Comparison regularity (b.1), (b.2), (w). -/
  comparisonRegularity : TwinComparisonRegularityPackage S.comparison
  /-- The Gate-0 Type-I input. -/
  gate0TypeI : Gate0FMTypeI S.X S.mRange S.intervals S.tauWeight S.w S.typeITarget
  /-- The full arbitrary-coefficient Type-II input on the interval. -/
  fullTypeII : FullFMTypeIIAtOneSixth S.X S.mRangeOf S.nRangeOf S.dwM S.dwN S.wC S.eps
    S.typeIITarget
  /-- The `N₂` shifted-prime upper bound. -/
  n2Upper : ShiftedPrimeN2UpperAtScale S.region S.n2C S.n2x S.n2logx S.n2err
  /-- ε-uniformity of the `N₂` constant. -/
  n2Uniform : N2UniformInEpsilon S.n2Constants
  /-- The published Ford–Maynard inputs outside the `N₂` region. -/
  externalInputs : S.externalNonN2Inputs
  /-- Legality of the substitution inside the Theorem-8.2 argument. -/
  substitutionLegal : S.substitutionLegal

namespace FMShiftedPrimeT82Splice

variable {S : T82SpliceData}

theorem proj_gate0 (h : FMShiftedPrimeT82Splice S) :
    Gate0FMTypeI S.X S.mRange S.intervals S.tauWeight S.w S.typeITarget := h.gate0TypeI

theorem proj_fullTypeII (h : FMShiftedPrimeT82Splice S) :
    FullFMTypeIIAtOneSixth S.X S.mRangeOf S.nRangeOf S.dwM S.dwN S.wC S.eps S.typeIITarget :=
  h.fullTypeII

theorem proj_n2Upper (h : FMShiftedPrimeT82Splice S) :
    ShiftedPrimeN2UpperAtScale S.region S.n2C S.n2x S.n2logx S.n2err := h.n2Upper

theorem proj_n2Uniform (h : FMShiftedPrimeT82Splice S) :
    N2UniformInEpsilon S.n2Constants := h.n2Uniform

end FMShiftedPrimeT82Splice

/-- **Firewall.**  The splice is contentful: if the legality field is `False`, no
splice exists.  In particular it can never be produced by bookkeeping. -/
theorem no_t82_splice_from_nothing (S : T82SpliceData) (h : S.substitutionLegal = False) :
    ¬ FMShiftedPrimeT82Splice S := by
  intro hs
  have := hs.substitutionLegal
  rw [h] at this
  exact this

/-- **External published interface (UNINHABITED here): Theorem 8.3.**  The
geometric mass of the exceptional region `H₂` is `O(ε)` on the admissible range. -/
def FMTheorem83H2Mass (mass : ℚ → ℝ) (C : ℝ) : Prop :=
  ∀ eps : ℚ, EpsAdmissible eps → mass eps ≤ C * (eps : ℝ)

/-- Provenance of Theorem 8.3: published, not formalized. -/
def theorem83Provenance : Provenance :=
  provenanceExternalTheorem "Ford–Maynard Theorem 8.3 (geometric mass of H₂)"
    "arXiv:2407.14368" "cited; the 107-page geometric argument is not formalized"

theorem theorem83Provenance_not_leanEvidence :
    Provenance.IsLeanEvidence theorem83Provenance = false := rfl

/-- Provenance of the Theorem-8.2 splice: a research proposal, not a published
theorem, and certainly not a Lean proof. -/
def t82SpliceProvenance : Provenance where
  status := AuditStatus.researchClaim
  sourceName := "shifted-prime substitution inside Theorem 8.2"
  sourceVersion := "current research proposal"
  scope := "replacement of the bounded-sequence step in the exceptional region"
  notes := "Not published, not formalized; the corresponding Lean structure is never inhabited."

theorem t82SpliceProvenance_not_leanEvidence :
    Provenance.IsLeanEvidence t82SpliceProvenance = false := rfl

theorem t82Splice_researchClaim_ne_published :
    t82SpliceProvenance.status ≠ theorem83Provenance.status := by decide

end NANC.V5
