/-
NANC V4 — GATE-0 DETERMINISTIC TYPE-I COMPILER.

The two analytic inputs

    MaximalWeightedBVShiftedPrime   (prime side)
    ComparisonProgressionMean       (comparison side)

are DEFINED here but NOT INHABITED: they are external analytic inputs.

The theorem `shiftedPrime_inputs_imply_FMTypeI` is a genuine Lean theorem: it
only performs the deterministic bookkeeping `w = a - b`, triangle inequality,
finite sum bounds.

PERMANENT FIREWALL:
    GATE-0 COMPILER  ≠  ANALYTIC BOMBIERI–VINOGRADOV PROOF
-/
import Mathlib
import RequestProject.NANC.V4.FordMaynardPredicates
import RequestProject.NANC.V4.ShiftedPrimeModel

namespace NANC.V4

open scoped BigOperators

/-- **Analytic input (prime side).**  A maximal, `τ^B`-weighted Bombieri–Vinogradov
estimate for the shifted-prime sequence, in finite-at-scale form: the outer
`m`-sum weighted by `tauWeight`, the maximum over the interval family, and the
required saving all appear.  UNINHABITED. -/
def MaximalWeightedBVShiftedPrime (X : ℕ) (typeIRange : Finset ℕ)
    (intervals : Finset (Finset ℕ)) (tauWeight a : ℕ → ℝ) (targetA : ℝ) : Prop :=
  ∀ Isel : ℕ → Finset ℕ, IsSelection intervals Isel →
    typeISum X typeIRange tauWeight a Isel ≤ targetA

/-- **Analytic input (comparison side).**  The corresponding progression-mean
estimate for the comparison sequence `b`.  UNINHABITED. -/
def ComparisonProgressionMean (X : ℕ) (typeIRange : Finset ℕ)
    (intervals : Finset (Finset ℕ)) (tauWeight b : ℕ → ℝ) (targetB : ℝ) : Prop :=
  ∀ Isel : ℕ → Finset ℕ, IsSelection intervals Isel →
    typeISum X typeIRange tauWeight b Isel ≤ targetB

/-- **Gate-0 deterministic compiler.**

Given the two analytic inputs for `a` and `b`, and nonnegativity of the outer
weight, the Ford–Maynard Type-I hypothesis holds for `w = a - b` with target
`targetA + targetB`.

The proof uses only: `w = a - b`, the triangle inequality, and finite sum
bounds.  The deep analytic content stays in the explicit hypotheses. -/
theorem shiftedPrime_inputs_imply_FMTypeI {X : ℕ} {typeIRange : Finset ℕ}
    {intervals : Finset (Finset ℕ)} {tauWeight : ℕ → ℝ} {targetA targetB : ℝ}
    (M : ShiftedPrimeComparisonModel) (hTau : ∀ m, 0 ≤ tauWeight m)
    (hA : MaximalWeightedBVShiftedPrime X typeIRange intervals tauWeight M.a targetA)
    (hB : ComparisonProgressionMean X typeIRange intervals tauWeight M.b targetB) :
    FMTypeIAtScale X typeIRange intervals tauWeight M.w (targetA + targetB) := by
  intro Isel hsel
  have key : typeISum X typeIRange tauWeight M.w Isel ≤
      typeISum X typeIRange tauWeight M.a Isel + typeISum X typeIRange tauWeight M.b Isel := by
    unfold typeISum
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum ?_
    intro m _
    have hsplit : ∑ n ∈ dyadicPart X m (Isel m), M.w (m * n) =
        (∑ n ∈ dyadicPart X m (Isel m), M.a (m * n)) -
          ∑ n ∈ dyadicPart X m (Isel m), M.b (m * n) := by
      simp [M.w_eq, Finset.sum_sub_distrib]
    have htri : |∑ n ∈ dyadicPart X m (Isel m), M.w (m * n)| ≤
        |∑ n ∈ dyadicPart X m (Isel m), M.a (m * n)| +
          |∑ n ∈ dyadicPart X m (Isel m), M.b (m * n)| := by
      rw [hsplit]
      exact abs_sub _ _
    calc tauWeight m * |∑ n ∈ dyadicPart X m (Isel m), M.w (m * n)|
        ≤ tauWeight m * (|∑ n ∈ dyadicPart X m (Isel m), M.a (m * n)| +
            |∑ n ∈ dyadicPart X m (Isel m), M.b (m * n)|) := by
          exact mul_le_mul_of_nonneg_left htri (hTau m)
      _ = tauWeight m * |∑ n ∈ dyadicPart X m (Isel m), M.a (m * n)| +
            tauWeight m * |∑ n ∈ dyadicPart X m (Isel m), M.b (m * n)| := by ring
  exact key.trans (add_le_add (hA Isel hsel) (hB Isel hsel))

/-- Status of the Gate-0 compiler: proved in Lean. -/
def statusGate0Compiler : BankStatus := BankStatus.conditionalTheorem

/-- Status of the Gate-0 analytic input: external / open. -/
def statusGate0AnalyticInput : BankStatus := BankStatus.externalAnalyticInput

/-- The Gate-0 analytic input is not proof-bearing: it may never be reported as
"Gate 0 analytically proved". -/
theorem statusGate0Analytic_not_proofBearing :
    BankStatus.IsProofBearing statusGate0AnalyticInput = false := by decide

/-- The Gate-0 compiler is a conditional theorem, not an unconditional one. -/
theorem statusGate0Compiler_conditional :
    statusGate0Compiler ≠ BankStatus.leanBanked := by decide

end NANC.V4
