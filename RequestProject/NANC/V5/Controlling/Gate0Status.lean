/-
NANC V5 CONTROLLING LAYER — GATE-0 STATUS AND ANALYTIC INTERFACES.

Two statuses are kept strictly apart:

    GATE0 RESEARCH STATUS : opusAuditedAnalyticPass   (external audit verdict)
    GATE0 LEAN STATUS     : analytic inputs EXTERNAL  (only the compiler is Lean)

The Type-I predicate and the deterministic Gate-0 compiler are the existing V4 /
V5 objects and are not duplicated.  What is added here are the three named
analytic input interfaces

    BombieriVinogradovShift2
    BrunTitchmarshShift2
    TwinComparisonProgressionMean

none of which is inhabited, plus the status bookkeeping.
-/
import Mathlib
import RequestProject.NANC.V5.Controlling.TwinComparison

namespace NANC.V5.Controlling

open scoped BigOperators
open NANC.V4 NANC.V5

/-! ### Analytic input interfaces -/

/-- **Analytic input (UNINHABITED): Bombieri–Vinogradov for the shift `+2`.**

The maximal, `τ^B`-weighted discrepancy bound in the residue class `2 mod q`,
summed over the moduli — the V5 residue-form interface, named for Gate 0. -/
def BombieriVinogradovShift2 (moduli : Finset ℕ) (intervals : Finset (Finset ℕ))
    (tauWeight a main : ℕ → ℝ) (target : ℝ) : Prop :=
  WeightedMaximalBVShift2Residue moduli intervals tauWeight a main target

/-- The number of shifted primes `n` in an interval with `n ≡ 2 (mod q)`. -/
def shift2ProgressionCount (q : ℕ) (I : Finset ℕ) : ℕ :=
  ((residueTwoPart q I).filter (fun n => Nat.Prime (n + 2))).card

/-- **Analytic input (UNINHABITED): Brun–Titchmarsh for the shift `+2`.**

A uniform upper bound, for each modulus in the range and each admissible
interval, on the number of shifted primes in the residue class `2 mod q`. -/
def BrunTitchmarshShift2 (moduli : Finset ℕ) (intervals : Finset (Finset ℕ))
    (bound : ℕ → Finset ℕ → ℝ) : Prop :=
  ∀ q ∈ moduli, ∀ I ∈ intervals, (shift2ProgressionCount q I : ℝ) ≤ bound q I

/-- **Analytic input (UNINHABITED): the comparison progression mean.**
The V4 interface for the comparison sequence `b`, named for Gate 0. -/
def TwinComparisonProgressionMean (X : ℕ) (mRange : Finset ℕ)
    (intervals : Finset (Finset ℕ)) (tauWeight b : ℕ → ℝ) (target : ℝ) : Prop :=
  ComparisonProgressionMean X mRange intervals tauWeight b target

/-! ### The deterministic Gate-0 compiler (reused, not duplicated) -/

/-- **Gate-0 compiler, residue form.**  The `+2` Bombieri–Vinogradov input together
with the (uninhabited) reindexing bridge gives the Gate-0 Type-I conclusion for the
comparison model `w = a - b`.  This is the V5 compiler applied to the renamed
interface: no analytic content is added. -/
theorem gate0_bv_bridge_compiler {X : ℕ} {moduli : Finset ℕ}
    {intervals : Finset (Finset ℕ)} {tauWeight : ℕ → ℝ} {target : ℝ}
    (M : ShiftedPrimeComparisonModel)
    (hbridge : Shift2ReindexingBridge X moduli intervals tauWeight M.a M.b)
    (hbv : BombieriVinogradovShift2 moduli intervals tauWeight M.a M.b target) :
    Gate0FMTypeI X moduli intervals tauWeight M.w target :=
  shift2_bridge_imply_gate0TypeI M hbridge hbv

/-- **Gate-0 compiler, multiplicative form.**  The prime-side and comparison-side
inputs give the Gate-0 Type-I conclusion with the summed target. -/
theorem gate0_multiplicative_compiler {X : ℕ} {mRange : Finset ℕ}
    {intervals : Finset (Finset ℕ)} {tauWeight : ℕ → ℝ} {targetA targetB : ℝ}
    (M : ShiftedPrimeComparisonModel) (hTau : ∀ m, 0 ≤ tauWeight m)
    (hA : WeightedMaximalBVShift2 X mRange intervals tauWeight M.a targetA)
    (hB : TwinComparisonProgressionMean X mRange intervals tauWeight M.b targetB) :
    Gate0FMTypeI X mRange intervals tauWeight M.w (targetA + targetB) :=
  weightedBV_and_comparison_imply_gate0TypeI M hTau hA hB

/-! ### Status bookkeeping -/

/-- The **research** status of the Gate-0 Type-I claim: an external audited
analytic pass.  This is a verdict about research, never a Lean proof. -/
def Gate0FMTypeIStatus : ControlStatus := ControlStatus.opusAuditedAnalyticPass

/-- The **Lean** status of Gate 0: only the deterministic compiler is Lean content;
the analytic inputs stay external. -/
def Gate0LeanStatus : ControlStatus := ControlStatus.conditionalCompiler

/-- Firewall: the Gate-0 research status is not a Lean proof. -/
theorem gate0ResearchStatus_ne_leanProved :
    Gate0FMTypeIStatus ≠ ControlStatus.leanProved := by decide

/-- Firewall: the Gate-0 Lean status is the compiler status, not an unconditional
Lean proof of Type I. -/
theorem gate0LeanStatus_ne_leanProved :
    Gate0LeanStatus ≠ ControlStatus.leanProved := by decide

/-- Status entry for the `+2` Bombieri–Vinogradov input. -/
def bvShift2Entry : ControlEntry where
  name := "Bombieri–Vinogradov for the shift +2 (weighted, maximal, residue 2 mod q)"
  status := ControlStatus.uninhabitedInterface
  notes := "External analytic input.  No inhabitant exists in this repository."

/-- Status entry for the `+2` Brun–Titchmarsh input. -/
def brunTitchmarshEntry : ControlEntry where
  name := "Brun–Titchmarsh for the shift +2"
  status := ControlStatus.uninhabitedInterface
  notes := "External analytic input.  No inhabitant exists in this repository."

/-- Status entry for the comparison progression mean. -/
def comparisonMeanEntry : ControlEntry where
  name := "comparison progression mean for b"
  status := ControlStatus.uninhabitedInterface
  notes := "External analytic input.  No inhabitant exists in this repository."

/-- Status entry for the Gate-0 research verdict. -/
def gate0ResearchEntry : ControlEntry where
  name := "GATE0 research status"
  status := Gate0FMTypeIStatus
  notes := "OPUS-AUDITED ANALYTIC PASS.  Not a Lean proof of Ford–Maynard Type I."

/-- Status entry for the Gate-0 Lean content. -/
def gate0LeanEntry : ControlEntry where
  name := "GATE0 Lean status"
  status := Gate0LeanStatus
  notes := "Deterministic compiler only; analytic inputs external."

theorem gate0Entries_not_leanEvidence :
    ControlEntry.IsLeanEvidence bvShift2Entry = false ∧
    ControlEntry.IsLeanEvidence brunTitchmarshEntry = false ∧
    ControlEntry.IsLeanEvidence comparisonMeanEntry = false ∧
    ControlEntry.IsLeanEvidence gate0ResearchEntry = false ∧
    ControlEntry.IsLeanEvidence gate0LeanEntry = false :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

end NANC.V5.Controlling
