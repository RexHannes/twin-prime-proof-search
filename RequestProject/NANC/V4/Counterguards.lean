/-
NANC V4 — counterguards and no-overclaim theorems.

These are the permanent firewalls of the bank.  Where a genuine finite
counterexample is cheap it is given; otherwise the guard is a status-datatype
theorem.
-/
import Mathlib
import RequestProject.NANC.V4.TypeICompiler
import RequestProject.NANC.V4.TypeIICompiler
import RequestProject.NANC.V4.WidthLedger
import RequestProject.NANC.V4.ConditionalDAG

namespace NANC.V4

open scoped BigOperators

/-! ### C_bd normalization counterguard

Dividing both the true and comparison weights by a factor `L > 1` divides the
comparison prime mass by exactly `L`.  Consequently one may not silently rescale
a bounded-class comparison sequence and pretend the prime mass is unchanged. -/

/-- Rescaling a weight by `1/L`. -/
noncomputable def scaleWeight (L : ℝ) (f : ℕ → ℝ) : ℕ → ℝ := fun n => f n / L

/-- Prime mass of a weight over a finite set. -/
noncomputable def primeMass (S : Finset ℕ) (f : ℕ → ℝ) : ℝ := ∑ p ∈ S.filter Nat.Prime, f p

/-- **Scaling counterguard.**  `primeMass (b/L) = primeMass b / L`. -/
theorem scale_comparison_prime_mass (S : Finset ℕ) (b : ℕ → ℝ) (L : ℝ) :
    primeMass S (scaleWeight L b) = primeMass S b / L := by
  simp [primeMass, scaleWeight, Finset.sum_div]

/-- Quantitative form: for `L > 1` and strictly positive prime mass, rescaling
strictly decreases the prime mass. -/
theorem scale_comparison_prime_mass_lt {S : Finset ℕ} {b : ℕ → ℝ} {L : ℝ} (hL : 1 < L)
    (hpos : 0 < primeMass S b) : primeMass S (scaleWeight L b) < primeMass S b := by
  rw [scale_comparison_prime_mass]
  exact div_lt_self hpos hL

/-- Scaling both sides of a comparison model preserves the relation `w = a - b`
but divides every mass by `L`; nothing about the *class* of the sequence is
automatic. -/
theorem scale_comparison_difference (S : Finset ℕ) (a b : ℕ → ℝ) (L : ℝ) :
    primeMass S (scaleWeight L a) - primeMass S (scaleWeight L b) =
      (primeMass S a - primeMass S b) / L := by
  rw [scale_comparison_prime_mass, scale_comparison_prime_mass, sub_div]

/-! ### A. Type I alone is not Gate-2 closure -/

/-- Ford–Maynard Type I can hold while the Type-II hypothesis fails on the same
data; hence Type I alone is not Gate-2 closure. -/
theorem typeI_alone_not_gate2 :
    ∃ (X : ℕ) (R Rn : Finset ℕ) (intervals : Finset (Finset ℕ)) (tau wR : ℕ → ℝ)
      (dwM dwN : ℕ → ℝ) (wC : ℕ → ℂ) (target : ℝ),
      FMTypeIAtScale X R intervals tau wR target ∧
      ¬ FMTypeIIAtScale X R Rn dwM dwN wC target := by
  refine ⟨1, {1}, {1}, {({1} : Finset ℕ)}, fun _ => 0, fun _ => 0, fun _ => 1, fun _ => 1,
    fun _ => 1, 0, ?_, ?_⟩
  · intro Isel _
    simp [typeISum]
  · intro h
    have h1 := h (fun _ => 1) (fun _ => 1) (fun m _ => by norm_num) (fun m _ => by norm_num)
    simp [typeIISum, dyadicSupport] at h1

/-! ### B. Width arithmetic alone is not a Ford–Maynard application -/

/-- The rational inequality `1/6 > 1663/10000` holds no matter what the sieve
coefficient does: there is a coefficient for which central-width positivity
fails.  Hence the width ledger alone never yields positivity. -/
theorem width_arithmetic_alone_not_positivity :
    fmThreshold < nu0 ∧
      ∃ Cminus : SieveCoefficient, ¬ CentralWidthOneSixthPositive Cminus := by
  refine ⟨one_sixth_gt_fm_threshold, fun _ _ _ => -1, ?_⟩
  intro h
  rw [CentralWidthOneSixthPositive] at h
  norm_num at h

/-! ### C. Gate1A + Gate1B ≠ Full FM Type II -/

theorem gate1AB_not_full_typeII :
    ∃ (A : Gate1AOutput) (B : Gate1BOutput) (dwM dwN : ℕ → ℝ),
      ¬ FMTypeIIAtScale A.X A.mRange A.nRange dwM dwN A.w A.target ∧ B.target = A.target := by
  obtain ⟨A, B, dwM, dwN, _, _, _, _, hT, hneg⟩ := gate1A_gate1B_not_FMTypeII
  exact ⟨A, B, dwM, dwN, hneg, hT.symm⟩

/-! ### D. sourceFieldMissing ≠ failedRoute -/

theorem sourceMissing_not_failure : BankStatus.sourceFieldMissing ≠ BankStatus.failedRoute :=
  BankStatus.sourceMissing_ne_failedRoute

/-! ### E. C⁻_bd must not be substituted for C⁻ -/

theorem bounded_not_ordinary :
    ∃ (Cminus CminusBd : SieveCoefficient) (gamma theta epsBound : ℚ),
      FMBoundedPositiveNearCentral CminusBd gamma theta epsBound ∧
      ¬ FMPositiveCentralWidth Cminus gamma theta :=
  ordinary_positive_ne_bounded_positive

/-! ### F. An uninhabited interface is never a Lean-banked proof -/

theorem interface_never_banked :
    BankStatus.IsProofBearing BankStatus.uninhabitedInterface = false ∧
      BankStatus.IsProofBearing BankStatus.externalAnalyticInput = false := by
  constructor <;> decide

/-- Any status that is interface-only fails the proof-bearing test; combined with
the bank's status assignments, no analytic interface can be reported as proved. -/
theorem no_promotion (s : BankStatus) (h : BankStatus.IsInterfaceOnly s = true) :
    BankStatus.IsProofBearing s = false :=
  BankStatus.interfaceOnly_not_proofBearing h

end NANC.V4
