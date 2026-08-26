/-
NANC V5 — GATE-0 ANALYTIC INTERFACES AND THE DETERMINISTIC COMPILER.

The Type-I predicate is the V4 one (`FMTypeIAtScale`); it is not redefined.

UNINHABITED analytic interfaces introduced here:

* `WeightedMaximalBVShift2Residue` — the maximal, `τ^B`-weighted Bombieri–
  Vinogradov estimate for the shifted primes in the residue class `2 mod q`,
  with an arbitrary required saving;
* `Shift2ReindexingBridge` — the (standard but nontrivial) passage from the
  residue-class form to the multiplicative form `w(m·n)`;
* `TwinComparisonProgressionInput` — the corresponding input for the comparison
  sequence `b`.

PROVED here (deterministic bookkeeping only):

* `shift2_residue_bridge_imp_multiplicative`
* `weightedBV_and_comparison_imply_gate0TypeI`
* `shift2_bridge_imply_gate0TypeI`

PERMANENT FIREWALL:
    GATE-0 COMPILER  ≠  WEIGHTED MAXIMAL BV
and
    "τ^B is usually small"  ⇏  weighted BV.
-/
import Mathlib
import RequestProject.NANC.V5.ComparisonRegularity

namespace NANC.V5

open scoped BigOperators
open NANC.V4

/-- The Gate-0 Type-I conclusion: the V4 Ford–Maynard Type-I predicate at the
given scale, for the comparison sequence `w`. -/
def Gate0FMTypeI (X : ℕ) (mRange : Finset ℕ) (intervals : Finset (Finset ℕ))
    (tauWeight w : ℕ → ℝ) (target : ℝ) : Prop :=
  FMTypeIAtScale X mRange intervals tauWeight w target

/-! ### Residue-class form of the analytic prime-side input -/

/-- The part of an interval lying in the residue class `2 mod q`. -/
def residueTwoPart (q : ℕ) (I : Finset ℕ) : Finset ℕ := I.filter (fun n => n % q = 2 % q)

/-- The discrepancy of the shifted-prime weight against its main term, on the
residue class `2 mod q` inside the interval `I`. -/
noncomputable def shift2Discrepancy (a main : ℕ → ℝ) (q : ℕ) (I : Finset ℕ) : ℝ :=
  |∑ n ∈ residueTwoPart q I, (a n - main n)|

/-- **Analytic input (UNINHABITED): maximal weighted Bombieri–Vinogradov for the
shifted primes.**

`∑_{q ∈ moduli} τ^B(q) · max_{I ∈ intervals} |∑_{n ∈ I, n ≡ 2 (q)} (a n - main n)| ≤ target`,

with the maximum over the interval family encoded by universally quantified
interval selections, the outer `τ^B` weight explicit, the residue class `2 mod q`
explicit, and the required saving supplied as `target`.

NO INHABITANT is produced anywhere in this bank. -/
def WeightedMaximalBVShift2Residue (moduli : Finset ℕ) (intervals : Finset (Finset ℕ))
    (tauWeight a main : ℕ → ℝ) (target : ℝ) : Prop :=
  ∀ Isel : ℕ → Finset ℕ, IsSelection intervals Isel →
    ∑ q ∈ moduli, tauWeight q * shift2Discrepancy a main q (Isel q) ≤ target

/-- **Analytic input (UNINHABITED): the reindexing bridge.**  It asserts that the
multiplicative Type-I quantity for `a - main` at any interval selection is
dominated by the residue-class quantity at some interval selection.  This is the
divisor-switching step; it is external analytic content, not bookkeeping. -/
def Shift2ReindexingBridge (X : ℕ) (moduli : Finset ℕ) (intervals : Finset (Finset ℕ))
    (tauWeight a main : ℕ → ℝ) : Prop :=
  ∀ Isel : ℕ → Finset ℕ, IsSelection intervals Isel →
    ∃ Jsel : ℕ → Finset ℕ, IsSelection intervals Jsel ∧
      typeISum X moduli tauWeight (fun n => a n - main n) Isel ≤
        ∑ q ∈ moduli, tauWeight q * shift2Discrepancy a main q (Jsel q)

/-- **Analytic input (UNINHABITED): the comparison-side progression input.**  It is
the V4 comparison progression-mean interface for the sequence `b`. -/
def TwinComparisonProgressionInput (X : ℕ) (mRange : Finset ℕ)
    (intervals : Finset (Finset ℕ)) (tauWeight b : ℕ → ℝ) (target : ℝ) : Prop :=
  ComparisonProgressionMean X mRange intervals tauWeight b target

/-- **Analytic input (UNINHABITED): the prime-side input in multiplicative form.**
It is the V4 maximal weighted BV interface for the sequence `a`. -/
def WeightedMaximalBVShift2 (X : ℕ) (mRange : Finset ℕ) (intervals : Finset (Finset ℕ))
    (tauWeight a : ℕ → ℝ) (target : ℝ) : Prop :=
  MaximalWeightedBVShiftedPrime X mRange intervals tauWeight a target

/-! ### Deterministic compilers -/

/-- **Deterministic step.**  The residue-class BV input together with the
reindexing bridge give the multiplicative Type-I bound for `w = a - main`.
Only transitivity of `≤` is used. -/
theorem shift2_residue_bridge_imp_multiplicative {X : ℕ} {moduli : Finset ℕ}
    {intervals : Finset (Finset ℕ)} {tauWeight a main : ℕ → ℝ} {target : ℝ}
    (hbridge : Shift2ReindexingBridge X moduli intervals tauWeight a main)
    (hbv : WeightedMaximalBVShift2Residue moduli intervals tauWeight a main target) :
    Gate0FMTypeI X moduli intervals tauWeight (fun n => a n - main n) target := by
  intro Isel hsel
  obtain ⟨Jsel, hJ, hle⟩ := hbridge Isel hsel
  exact hle.trans (hbv Jsel hJ)

/-- **Gate-0 deterministic compiler (multiplicative form).**  The prime-side and
comparison-side analytic inputs give the Gate-0 Type-I conclusion for `w = a - b`.
This reuses the V4 compiler; no analytic content is added. -/
theorem weightedBV_and_comparison_imply_gate0TypeI {X : ℕ} {mRange : Finset ℕ}
    {intervals : Finset (Finset ℕ)} {tauWeight : ℕ → ℝ} {targetA targetB : ℝ}
    (M : ShiftedPrimeComparisonModel) (hTau : ∀ m, 0 ≤ tauWeight m)
    (hA : WeightedMaximalBVShift2 X mRange intervals tauWeight M.a targetA)
    (hB : TwinComparisonProgressionInput X mRange intervals tauWeight M.b targetB) :
    Gate0FMTypeI X mRange intervals tauWeight M.w (targetA + targetB) :=
  shiftedPrime_inputs_imply_FMTypeI M hTau hA hB

/-- **Gate-0 deterministic compiler (residue form).**  For the comparison model
`w = a - b`, the residue-class BV input for `a` against main term `b`, together
with the reindexing bridge, gives the Gate-0 Type-I conclusion. -/
theorem shift2_bridge_imply_gate0TypeI {X : ℕ} {moduli : Finset ℕ}
    {intervals : Finset (Finset ℕ)} {tauWeight : ℕ → ℝ} {target : ℝ}
    (M : ShiftedPrimeComparisonModel)
    (hbridge : Shift2ReindexingBridge X moduli intervals tauWeight M.a M.b)
    (hbv : WeightedMaximalBVShift2Residue moduli intervals tauWeight M.a M.b target) :
    Gate0FMTypeI X moduli intervals tauWeight M.w target := by
  have h := shift2_residue_bridge_imp_multiplicative hbridge hbv
  have hw : M.w = fun n => M.a n - M.b n := funext fun n => M.w_eq n
  rwa [hw]

/-! ### No fake `τ^B` absorption -/

/-- Smallness of the outer divisor weight, as a finite hypothesis. -/
def TauWeightBounded (moduli : Finset ℕ) (tauWeight : ℕ → ℝ) (B : ℝ) : Prop :=
  ∀ q ∈ moduli, tauWeight q ≤ B

/-- Status marker: the outer `τ^B` weight always needs a genuine analytic input;
smallness of `τ^B` is never a substitute. -/
def TauWeightNeedsAnalyticInput : Provenance where
  status := AuditStatus.uninhabited
  sourceName := "τ^B absorption"
  sourceVersion := "NANC V5 counterguard"
  scope := "the outer divisor weight"
  notes := "\"τ^B is usually small, hence weighted BV\" is NOT a theorem and is never banked."

theorem TauWeightNeedsAnalyticInput_not_leanEvidence :
    Provenance.IsLeanEvidence TauWeightNeedsAnalyticInput = false := rfl

/-- **Firewall (finite counterexample).**  Boundedness of the outer weight does not
imply the weighted BV input: here `τ ≡ 1` is bounded by `1`, yet the required
saving `target = -1` is not achieved. -/
theorem tauBounded_not_weightedBV :
    ∃ (moduli : Finset ℕ) (intervals : Finset (Finset ℕ)) (tauWeight a main : ℕ → ℝ)
      (B target : ℝ),
      TauWeightBounded moduli tauWeight B ∧
      ¬ WeightedMaximalBVShift2Residue moduli intervals tauWeight a main target := by
  refine ⟨{1}, {∅}, fun _ => 1, fun _ => 0, fun _ => 0, 1, -1, ?_, ?_⟩
  · intro q _; norm_num
  · intro h
    have := h (fun _ => ∅) (fun _ => by simp)
    simp [shift2Discrepancy, residueTwoPart] at this
    linarith

end NANC.V5
