/-
NANC V5 — PERMANENT COUNTERGUARDS.

Seven guards, each of which prevents a specific overclaim:

1. `width_arithmetic_not_fullTypeII`      : 1/6 > 0.1663  ≠  Full Type II
2. `auditPass_not_leanProof`              : external audit PASS  ≠  Lean proof
3. `n2Use_not_exclusive`                  : one explicit use of boundedness
                                            ≠  proof of no indirect uses
4. `pointwiseSieve_not_uniformIntegration`: pointwise sieve  ≠  uniform N₂
                                            geometric integration
5. `fixedEps_not_uniformEps`              : N₂ for fixed ε  ≠  ε-uniform splice
6. `gate0Compiler_not_weightedBV`         : Gate-0 compiler  ≠  weighted maximal BV
7. `gate0_gate2_not_twins_without_typeII` : Gate 0 + Gate 2  ≠  twin primes
                                            without full Type II
-/
import Mathlib
import RequestProject.NANC.V5.ConditionalTwinEndgame

namespace NANC.V5

open scoped BigOperators
open NANC.V4

/-- **Guard 1.**  The exact rational inequality `1/6 > 1663/10000` is true, and it
supplies no Type-II information whatsoever: there is data satisfying the width
arithmetic on which the full interval Type-II hypothesis fails. -/
theorem width_arithmetic_not_fullTypeII :
    fmThreshold < nu0 ∧
    ∃ (X : ℕ) (mRangeOf nRangeOf : ℚ → Finset ℕ) (dwM dwN : ℕ → ℝ) (w : ℕ → ℂ)
      (eps : ℚ) (target : ℝ),
      ¬ FullFMTypeIIAtOneSixth X mRangeOf nRangeOf dwM dwN w eps target := by
  refine ⟨one_sixth_gt_fm_threshold,
    1, fun _ => {1}, fun _ => {1}, fun _ => 1, fun _ => 1, fun _ => 1, 0, 0, ?_⟩
  intro h
  have h0 := h 0 (le_refl 0) (by norm_num)
  have h1 := h0 (fun _ => 1) (fun _ => 1) (fun m _ => by norm_num) (fun m _ => by norm_num)
  simp [typeIISum, dyadicSupport] at h1

/-- **Guard 2.**  An external audit verdict is a different status from a Lean
proof, and a provenance record carrying it is never Lean evidence. -/
theorem auditPass_not_leanProof :
    AuditStatus.opusAudited ≠ AuditStatus.leanProved ∧
    ∀ name : String, Provenance.IsLeanEvidence (provenanceOpusVerdict name) = false :=
  ⟨AuditStatus.opusAudited_ne_leanProved, provenanceOpusVerdict_not_leanEvidence⟩

/-- **Guard 3.**  Recording one explicit pointwise use of the boundedness
hypothesis in the `N₂` estimate does not establish that there are no further
(indirect) uses. -/
theorem n2Use_not_exclusive :
    ∃ A : FMTheorem82DependencyAudit, A.boundednessUsedInN2 ∧ A.boundednessUsedElsewhere :=
  n2Use_does_not_exclude_otherUses

/-- **Guard 4.**  A pointwise two-linear-form sieve bound is not the uniform `N₂`
geometric integration: the aggregate bound can fail while the region carries
positive mass. -/
theorem pointwiseSieve_not_uniformIntegration :
    ∃ (R : N2RegionData) (C x logx err : ℝ),
      0 < n2Weighted R ∧ ¬ ShiftedPrimeN2UpperAtScale R C x logx err :=
  pointwiseSieve_not_uniformN2

/-- **Guard 5.**  An `N₂` bound for each fixed admissible `ε` does not give the
`ε`-uniform statement required by the splice. -/
theorem fixedEps_not_uniformEps :
    ∃ (F : N2ConstantFamily) (Q : ℚ → ℝ),
      N2UpperForEachEpsilon F Q ∧ ¬ N2UniformInEpsilon F :=
  n2ForEachEpsilon_not_uniformInEpsilon

/-- **Guard 6.**  The Gate-0 compiler is deterministic bookkeeping and is *not*
the weighted maximal Bombieri–Vinogradov input: the compiler is available on data
where that input fails outright. -/
theorem gate0Compiler_not_weightedBV :
    ∃ (moduli : Finset ℕ) (intervals : Finset (Finset ℕ)) (tauWeight a main : ℕ → ℝ)
      (target : ℝ),
      TauWeightBounded moduli tauWeight 1 ∧
      ¬ WeightedMaximalBVShift2Residue moduli intervals tauWeight a main target := by
  exact ⟨{1}, {∅}, fun _ => 1, fun _ => 0, fun _ => 0, -1, fun q _ => by norm_num, by
    intro h
    have := h (fun _ => ∅) (fun _ => by simp)
    simp [shift2Discrepancy, residueTwoPart] at this
    linarith⟩

/-- **Guard 7.**  Gate-0 and Gate-2 material together do not give twin primes
without the full arbitrary-coefficient Type-II input: there is a node assignment
where everything except Type II holds and the conclusion fails. -/
theorem gate0_gate2_not_twins_without_typeII :
    ∃ N : EndgameNodes,
      N.Gate0FMTypeI ∧ N.FMComparisonRegularity ∧ N.FMPositiveSieveCertificate ∧
      N.FMShiftedPrimeEndgameSplice ∧ ¬ N.FullFMTypeII ∧ ¬ N.PositiveTwinMass := by
  refine ⟨{ Gate0FMTypeI := True, FullFMTypeII := False, FMComparisonRegularity := True,
            FMPositiveSieveCertificate := True, FMShiftedPrimeEndgameSplice := True,
            PositiveTwinMass := False }, trivial, trivial, trivial, trivial, id, id⟩

end NANC.V5
