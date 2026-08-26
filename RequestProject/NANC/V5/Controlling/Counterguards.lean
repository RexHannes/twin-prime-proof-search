/-
NANC V5 CONTROLLING LAYER — THE EIGHT PERMANENT COUNTERGUARDS.

1. `width_arithmetic_not_twin_primes`      : 1/6 > 0.1663              ≠ twin primes
2. `gate0AuditPass_not_leanProof`          : Gate-0 analytic pass      ≠ Lean proof
3. `gate0_and_gate2_not_fullTypeII`        : Gate 0 + Gate 2           ≠ full Type II
4. `fullTypeII_not_gate1AB`                : full Type II             ≠ Gate1A+Gate1B
                                             without a reassembly certificate
5. `pointwise_stronger_than_cellSum`       : pointwise short-cell estimate is
                                             STRICTLY STRONGER than the cell-summed
                                             source-minimal target
6. `fixedEpsilon_not_epsilonUniform`       : fixed-ε N₂ bound          ≠ ε-uniform splice
7. `ordinary_not_bounded_class`            : ordinary C⁻              ≠ bounded C⁻_bd
8. `sourceSpecificRepair_not_general`      : a source-specific Theorem-8.2 repair
                                             ≠ a theorem for arbitrary ordinary sequences
-/
import Mathlib
import RequestProject.NANC.V5.Controlling.ConditionalEndgame

namespace NANC.V5.Controlling

open scoped BigOperators
open NANC.V4 NANC.V5

/-- A trivial cell configuration: no cells, no mass. -/
def emptyCellData : N2CellData where
  eps := 0
  k := 0
  cells := ∅
  cellSet := fun _ => ∅
  prefixPrimes := fun _ => ∅
  J := fun _ => ∅
  a := fun _ => 0
  H := fun _ => 0
  geometricMass := 0
  a_nonneg := fun _ => le_refl 0
  geometricMass_nonneg := le_refl 0

/-- A cell configuration carrying unit mass but zero geometric mass. -/
def unitCellData : N2CellData where
  eps := 0
  k := 1
  cells := {0}
  cellSet := fun _ => {0}
  prefixPrimes := fun _ => ∅
  J := fun _ => ∅
  a := fun _ => 1
  H := fun _ => 1
  geometricMass := 0
  a_nonneg := fun _ => by norm_num
  geometricMass_nonneg := le_refl 0

theorem emptyCellData_cellSum : FMN2CellSumUpperAtScale emptyCellData 1 1 0 := by
  simp [FMN2CellSumUpperAtScale, totalN2Mass, emptyCellData]

theorem unitCellData_not_cellSum : ¬ FMN2CellSumUpperAtScale unitCellData 1 1 0 := by
  intro h
  simp [FMN2CellSumUpperAtScale, totalN2Mass, cellMass, unitCellData] at h
  linarith

/-- **Guard 1.**  The exact rational inequality `1/6 > 1663/10000` holds, and it
produces no twin pair: there are finite windows containing none. -/
theorem width_arithmetic_not_twin_primes :
    fmThresholdQ < nu0 ∧ ∃ S : Finset ℕ, ¬ ∃ p ∈ S, Nat.Prime p ∧ Nat.Prime (p + 2) := by
  refine ⟨control_one_sixth_gt_threshold, {1}, ?_⟩
  rintro ⟨p, hp, hprime, -⟩
  rw [Finset.mem_singleton] at hp
  subst hp
  exact absurd hprime (by norm_num)

/-- **Guard 2.**  The Gate-0 research verdict is an audited analytic pass, which is
a different status from a Lean proof, and the corresponding entry is never Lean
evidence. -/
theorem gate0AuditPass_not_leanProof :
    Gate0FMTypeIStatus ≠ ControlStatus.leanProved ∧
    ControlEntry.IsLeanEvidence gate0ResearchEntry = false :=
  ⟨gate0ResearchStatus_ne_leanProved, rfl⟩

/-- **Guard 3.**  Gate-0 Type-I material and a Gate-2 cell-sum bound can both hold
while the exact arbitrary-coefficient Type-II hypothesis fails.  Hence "Gate 0 +
Gate 2" never amounts to full Type II. -/
theorem gate0_and_gate2_not_fullTypeII :
    (∀ (X : ℕ) (intervals : Finset (Finset ℕ)) (tauWeight w : ℕ → ℝ),
      Gate0FMTypeI X ∅ intervals tauWeight w 0) ∧
    (∃ D : N2CellData, FMN2CellSumUpperAtScale D 1 1 0) ∧
    (∃ (X : ℕ) (theta nu : ℚ) (candidates nRange : Finset ℕ) (dwM dwN : ℕ → ℝ) (w : ℕ → ℂ)
      (target : ℝ),
      ¬ FMTypeIIExactAtScale X theta nu candidates nRange dwM dwN w target) := by
  refine ⟨?_, ?_, ?_⟩
  · intro X intervals tauWeight w Isel _
    simp [typeISum]
  · exact ⟨emptyCellData, emptyCellData_cellSum⟩
  · obtain ⟨X, theta, nu, candidates, nRange, dwM, dwN, w, -, -, target, -, -, -, hno⟩ :=
      sourceSpecific_not_FMTypeIIExact
    exact ⟨X, theta, nu, candidates, nRange, dwM, dwN, w, target, hno⟩

/-- **Guard 4.**  Gate-1A and Gate-1B source outputs do not give the full
arbitrary-coefficient Type-II hypothesis without a reassembly certificate. -/
theorem fullTypeII_not_gate1AB :
    ∃ (A : Gate1AOutput) (B : Gate1BOutput) (mRangeOf nRangeOf : ℚ → Finset ℕ)
      (dwM dwN : ℕ → ℝ) (eps : ℚ),
      A.X = B.X ∧ A.w = B.w ∧ A.target = B.target ∧
      ¬ FullFMTypeIIAtOneSixth A.X mRangeOf nRangeOf dwM dwN A.w eps A.target :=
  gate1AB_not_fullTypeIIAtOneSixth

/-- **Guard 5.**  The pointwise short-cell estimate is strictly stronger than the
cell-summed, source-minimal controlling target: the aggregate bound can hold while
a proposed pointwise bound fails. -/
theorem pointwise_stronger_than_cellSum :
    ∃ (D : N2CellData) (bound : ℕ → ℝ) (x logx err : ℝ),
      FMN2CellSumUpperAtScale D x logx err ∧ ¬ PointwiseCellUpper D bound :=
  cellSum_does_not_give_pointwise

/-- **Guard 6.**  An `N₂` bound for each fixed admissible `ε` is not the ε-uniform
statement the splice needs. -/
theorem fixedEpsilon_not_epsilonUniform :
    ∃ (F : N2ConstantFamily) (Q : ℚ → ℝ),
      N2UpperForEachEpsilon F Q ∧ ¬ EpsilonUniformN2 F :=
  n2ForEachEpsilon_not_uniformInEpsilon

/-- **Guard 7.**  The ordinary and bounded sequence classes are different, and
positivity of the bounded coefficient `C⁻_bd` does not give positivity of the
ordinary coefficient `C⁻`. -/
theorem ordinary_not_bounded_class :
    SequenceClass.ordinary ≠ SequenceClass.bounded ∧
    ∃ (Cminus CminusBd : SieveCoefficient) (gamma theta epsBound : ℚ),
      FMBoundedPositiveNearCentral CminusBd gamma theta epsBound ∧
      ¬ FMPositiveCentralWidth Cminus gamma theta :=
  ⟨ordinary_ne_bounded, ordinary_positive_ne_bounded_positive⟩

/-- **Guard 8.**  A source-specific repair — a cell-sum bound verified for one
particular configuration — is not a theorem for arbitrary ordinary sequences: the
same bound fails on other data. -/
theorem sourceSpecificRepair_not_general :
    ∃ D0 : N2CellData, FMN2CellSumUpperAtScale D0 1 1 0 ∧
      ¬ ∀ D : N2CellData, FMN2CellSumUpperAtScale D 1 1 0 := by
  refine ⟨emptyCellData, emptyCellData_cellSum, ?_⟩
  intro hall
  exact unitCellData_not_cellSum (hall unitCellData)

end NANC.V5.Controlling
