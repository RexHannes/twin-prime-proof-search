import RequestProject.AnalyticInterfaces
import RequestProject.TwinPrimeStatus

/-!
# Fixed-application perfect-power reduction

This module separates fixed source branches from universal majorants, records the
exact perfect-power support required from a source branch, and proves finite
counting inequalities.  Analytic closure is represented only by a proof-carrying
input; this module supplies no such input.
-/

namespace TwinPrimeProject

open scoped BigOperators

/-- The exact rational value used for the Fable parameter `ν₀`. -/
def fableNu0 : ℚ := 1663 / 10000

/-- The derived parameters, kept rational so their elementary arithmetic is
kernel-checkable. -/
def fableGamma (ε : ℚ) : ℚ := 1 / 2 - ε
def fableSigma (ε : ℚ) : ℚ := fableNu0 - 2 * ε

theorem fableNu0_pos : 0 < fableNu0 := by
  norm_num [fableNu0]

theorem fable_J_eq_four {ε : ℚ} (hε : 0 < ε) (hεmax : ε ≤ fableNu0 / 100) :
    2 * ⌈(1 / (1 - fableGamma ε) : ℚ)⌉ = 4 := by
  simp [fableGamma, fableNu0] at *
  -- Need to show ⌈(1/2 + ε)⁻¹⌉ = 2
  have h_bound : ε ≤ 1663 / 1000000 := by linarith
  have h_sum_pos : 0 < 1 / 2 + ε := by linarith
  have h_inv_lower : (1 / 2 + ε)⁻¹ ≥ 1000000 / 501663 := by
    rw [ge_iff_le, inv_eq_one_div, div_le_div_iff₀] <;> nlinarith
  have h_inv_upper : (1 / 2 + ε)⁻¹ < 2 := by
    rw [inv_eq_one_div, div_lt_iff₀] <;> nlinarith
  -- Show that the goal expression equals (1/2 + ε)⁻¹
  have h_simp : (1 - (2⁻¹ - ε))⁻¹ = (1 / 2 + ε)⁻¹ := by ring
  rw [h_simp]
  -- Now use that ceiling of a value in [1.993, 2) is 2
  have h_ceil : ⌈(1 / 2 + ε)⁻¹⌉ = 2 := by
    rw [Int.ceil_eq_iff]
    refine ⟨?_, ?_⟩
    · calc (2 : ℚ) - 1 = 1 := by norm_num
        _ < 1000000 / 501663 := by norm_num
        _ ≤ (1 / 2 + ε)⁻¹ := h_inv_lower
    · exact h_inv_upper.le
  rw [h_ceil]
  norm_num

theorem fable_ell_eq_twelve {ε : ℚ} (hε : 0 < ε) (hεmax : ε ≤ fableNu0 / 100) :
    3 * (2 * ⌈(1 / (1 - fableGamma ε) : ℚ)⌉) = 12 := by
  rw [fable_J_eq_four hε hεmax]
  norm_num

theorem fable_floor_inv_sigma_eq_six {ε : ℚ} (hε : 0 < ε)
    (hεmax : ε ≤ fableNu0 / 100) :
    ⌊(1 / fableSigma ε : ℚ)⌋ = 6 := by
  unfold fableSigma fableNu0 at *
  rw [Int.floor_eq_iff]
  have h1 : 0 < 1663 / 10000 - 2 * ε := by linarith
  have h2 : 1663 / 10000 - 2 * ε < 1663 / 10000 := by linarith
  have h3 : (1663 / 10000 : ℚ)⁻¹ > 6 := by norm_num
  have h4 : (1663 / 10000 - 2 * (1663 / 10000 / 100) : ℚ)⁻¹ < 7 := by norm_num
  constructor
  · have h5 : (1663 / 10000 : ℚ)⁻¹ > 6 := by norm_num
    have h6 : (1663 / 10000 - 2 * ε)⁻¹ ≥ (1663 / 10000)⁻¹ := inv_anti₀ h1 h2.le
    show (6 : ℚ) ≤ (1 / (1663 / 10000 - 2 * ε))
    simpa [one_div] using le_trans h5.le h6
  · have h5 : (1663 / 10000 - 2 * (1663 / 10000 / 100) : ℚ)⁻¹ < 7 := by norm_num
    have h6 : (1663 / 10000 - 2 * ε)⁻¹ ≤ (1663 / 10000 - 2 * (1663 / 10000 / 100))⁻¹ := by
      apply inv_anti₀
      · norm_num
      linarith
    norm_num at *
    linarith

/-- The advertised smooth-splitting upper bound `3/σ+2 ≤ 20` is not true for
these parameters.  This exact kernel check records the obstruction at the
largest allowed epsilon. -/
theorem fable_splitting_bound_twenty_false :
    ¬ (3 / fableSigma (fableNu0 / 100) + 2 ≤ (20 : ℚ)) := by
  norm_num [fableSigma, fableNu0]

/-- The corrected uniform integer bound is 21. -/
theorem fable_splitting_bound_le_twenty_one {ε : ℚ} (hε : 0 ≤ ε)
    (hεmax : ε ≤ fableNu0 / 100) :
    3 / fableSigma ε + 2 ≤ (21 : ℚ) := by
  unfold fableSigma fableNu0 at *
  have hpos : 0 < 1663 / 10000 - 2 * ε := by linarith
  have hle : 3 / (1663 / 10000 - 2 * ε) ≤ 19 := by
    rw [div_le_iff₀ hpos]
    norm_num
    linarith
  linarith

/-- The two ledgers must not be conflated. -/
inductive ApplicationLedger where
  | fixedApplication
  | universalMajorant
  deriving DecidableEq, Repr

/-- Data retained by an exact fixed-application term. -/
structure FixedApplicationLedgerData where
  uvNontrivialOrAtLeastTwoPrimes : Prop
  fixedApplicationCondition : uvNontrivialOrAtLeastTwoPrimes
  retainsExactMobiusFactors : Bool
  retainsOneLogPerOriginalPrime : Bool
  retainsCoefficientOneFactors : Bool
  retainsCanonicalUVBlocks : Bool
  retainsMellinPhases : Bool
  retainsExactSourceBranchCoefficients : Bool

/-- Operations that create a universal majorant rather than an exact source
term. -/
structure UniversalMajorantLedgerData where
  fixedApplicationConditionRemoved : Bool
  exactFactorsReplacedByBoundedFactors : Bool
  exactPowerRelationsFreed : Bool
  universalTriangleMajorantApplied : Bool

/-- A universal-majorant entry carries no implication that it is a binding
fixed-application core. -/
def UniversalMajorantLedgerData.bindingFixedApplicationCore
    (_ : UniversalMajorantLedgerData) : Bool := false

/-- Structural support supplied by an exact surviving Heath--Brown branch.
There is deliberately no global inhabitant. -/
structure PerfectPowerBranchSupport where
  X : ℝ
  sigma : ℝ
  r : ℕ
  c : ℕ
  m_h : ℕ
  n : ℕ
  exponent_at_least_two : 2 ≤ r
  root_positive : 1 ≤ c
  exact_power : m_h = c ^ r
  divides_source : m_h ∣ n
  large_divisor : (X / 2) ^ sigma < m_h
  source_range_lower : X / 2 < n
  source_range_upper : n ≤ X

/-- Finite fixed-exponent divisor mass.  It majorizes, by a union bound, the
number of integers `n ≤ X` divisible by one of the powers in the range. -/
def fixedExponentDivisorMass (X T r : ℕ) : ℕ :=
  ∑ c ∈ Finset.Ioc T X, X / c ^ r

theorem fixedExponent_mass_mono_exponent (X T r : ℕ) (hr : 2 ≤ r) :
    fixedExponentDivisorMass X T r ≤ fixedExponentDivisorMass X T 2 := by
  unfold fixedExponentDivisorMass
  apply Finset.sum_le_sum
  intro c hc
  apply Nat.div_le_div_left
  · exact Nat.pow_le_pow_right (by have := Finset.mem_Ioc.mp hc; omega) hr
  · have : 0 < c := by have := Finset.mem_Ioc.mp hc; omega
    exact pow_pos this 2

/-- A real-valued explicit square-tail estimate for the finite divisor mass.
This is the elementary power-saving counting core: choosing `T` near
`X^(σ/2)` gives size `O(X/T)`. -/
theorem fixedExponentDivisorMass_sq_tail (X T : ℕ) (hT : T ≠ 0) :
    (fixedExponentDivisorMass X T 2 : ℝ) ≤ X / T := by
  unfold fixedExponentDivisorMass
  have hT' : (0 : ℝ) < T := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hT)
  have key : ∀ c : ℕ, (X / c ^ 2 : ℕ) ≤ (X : ℝ) / (c : ℝ) ^ 2 := by
    intro c
    by_cases hc : c = 0
    · simp [hc]
    · have hc' : (0 : ℝ) < c := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hc)
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < (c : ℝ) ^ 2)]
      norm_cast
      exact Nat.div_mul_le_self X (c ^ 2)
  calc (↑(∑ c ∈ Finset.Ioc T X, X / c ^ 2) : ℝ)
      ≤ ∑ c ∈ Finset.Ioc T X, (X : ℝ) / (c : ℝ) ^ 2 := by
        push_cast
        exact Finset.sum_le_sum fun c _ => key c
      _ = (X : ℝ) * ∑ c ∈ Finset.Ioc T X, (1 : ℝ) / (c : ℝ) ^ 2 := by
        rw [Finset.mul_sum]
        simp [div_eq_mul_inv, mul_comm]
      _ ≤ (X : ℝ) * (1 / T) := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg X)
        -- Need to show: ∑ c ∈ Finset.Ioc T X, 1 / c^2 ≤ 1 / T
        by_cases hTX : T < X
        · -- c ∈ Ioc T X means T < c ≤ X, so c ≥ T + 1 ≥ 2
          have hsum_bound : ∑ c ∈ Finset.Ioc T X, (1 : ℝ) / (c : ℝ) ^ 2 ≤
                            ∑ c ∈ Finset.Ioc T X, (1 / (c - 1 : ℝ) - 1 / c) := by
            apply Finset.sum_le_sum
            intro c hc
            have hc_gt : T < c := Finset.mem_Ioc.mp hc |>.1
            have hc_ge : (c : ℝ) ≥ T + 1 := by exact_mod_cast hc_gt
            have hc_pos : (0 : ℝ) < c := by linarith
            have hc_minus_pos : (0 : ℝ) < c - 1 := by linarith
            rw [div_sub_div _ _ (ne_of_gt hc_minus_pos) (ne_of_gt hc_pos)]
            rw [div_le_div_iff₀ (by positivity) (mul_pos hc_minus_pos hc_pos)]
            ring_nf
            nlinarith
          -- The telescoping sum: ∑_{c=T+1}^{X} (1/(c-1) - 1/c) = 1/T - 1/X
          have htelescope : ∑ c ∈ Finset.Ioc T X, (1 / (c - 1 : ℝ) - 1 / c) = 1 / T - 1 / X := by
            have h_eq : X = T + (X - T) := by omega
            have key : ∀ k : ℕ, ∑ c ∈ Finset.Ioc T (T + k), (1 / (c - 1 : ℝ) - 1 / c) = 1 / T - 1 / (T + k) := by
              intro k
              induction k with
              | zero =>
                simp
              | succ n ih =>
                have heq1 : T + (n + 1) = T + n + 1 := by omega
                have hsplit : Finset.Ioc T (T + n + 1) = Finset.Ioc T (T + n) ∪ {T + n + 1} := by
                  ext x
                  simp [Finset.mem_Ioc, Finset.mem_union, Finset.mem_singleton]
                  omega
                rw [heq1, hsplit]
                have hdisj : Disjoint (Finset.Ioc T (T + n)) {T + n + 1} := by
                  simp [Finset.disjoint_singleton_right, Finset.mem_Ioc]
                rw [Finset.sum_union hdisj]
                rw [Finset.sum_singleton]
                simp only [Nat.cast_add, Nat.cast_one]
                rw [ih]
                field_simp [show (T : ℝ) ≠ 0 by positivity,
                           show (T + n : ℝ) ≠ 0 by positivity,
                           show (T + n + 1 : ℝ) ≠ 0 by positivity]
                ring
            rw [h_eq]
            exact_mod_cast key (X - T)
          exact le_trans hsum_bound (htelescope.symm ▸ sub_le_self _ (by positivity))
        · -- T ≥ X, so Ioc T X is empty
          have hle : X ≤ T := Nat.not_lt.mp hTX
          have hempty : Finset.Ioc T X = ∅ := Finset.Ioc_eq_empty_of_le (by linarith [hle])
          simp [hempty]
      _ = (X : ℝ) / T := by ring

/-- Fixed-exponent version, reduced transparently to the square tail. -/
theorem fixedExponentDivisorMass_bound (X T r : ℕ) (hr : 2 ≤ r) (hT : T ≠ 0) :
    (fixedExponentDivisorMass X T r : ℝ) ≤ X / T := by
  calc
    (fixedExponentDivisorMass X T r : ℝ) ≤ fixedExponentDivisorMass X T 2 := by
      exact_mod_cast fixedExponent_mass_mono_exponent X T r hr
    _ ≤ X / T := fixedExponentDivisorMass_sq_tail X T hT

/-- Summing over a finite range of exponents costs only its cardinality. -/
theorem summedExponentDivisorMass_bound (X T R : ℕ) (hT : T ≠ 0) :
    (∑ r ∈ Finset.Icc 2 R, (fixedExponentDivisorMass X T r : ℝ))
      ≤ ((R - 1 : ℕ) : ℝ) * ((X : ℝ) / T) := by
  calc
    (∑ r ∈ Finset.Icc 2 R, (fixedExponentDivisorMass X T r : ℝ))
        ≤ ∑ _r ∈ Finset.Icc 2 R, ((X : ℝ) / T) := by
          apply Finset.sum_le_sum
          intro r hr
          exact fixedExponentDivisorMass_bound X T r (Finset.mem_Icc.mp hr).1 hT
    _ = ((Finset.Icc 2 R).card : ℝ) * ((X : ℝ) / T) := by simp
    _ = ((R - 1 : ℕ) : ℝ) * ((X : ℝ) / T) := by
      congr 2
      simp

/-- Separately visible bound for an original branch coefficient. -/
structure HBBranchCoefficientBound (ι : Type*) (a : ι → ℂ) where
  bound : ℝ
  bound_nonnegative : 0 ≤ bound
  coefficient_bound : ∀ i, ‖a i‖ ≤ bound

/-- Separately visible factorisation-multiplicity input. -/
structure BranchFactorisationMultiplicity (ι : Type*) (multiplicity : ι → ℕ) where
  bound : ℕ
  multiplicity_bound : ∀ i, multiplicity i ≤ bound

/-- Separately visible crude centered-weight input. -/
structure CenteredWeightCrudeBound (ι : Type*) (w : ι → ℂ) where
  bound : ℝ
  bound_nonnegative : 0 ≤ bound
  weight_bound : ∀ i, ‖w i‖ ≤ bound

/-- Separately visible certificate/divisor-weight input. -/
structure CertificateDivisorBound (ι : Type*) (certificate : ι → ℂ) where
  bound : ℝ
  bound_nonnegative : 0 ≤ bound
  certificate_bound : ∀ i, ‖certificate i‖ ≤ bound

/-- Separately visible normalized logarithmic-coefficient input. -/
structure NormalizedLogCoefficientBound (ι : Type*) (a : ι → ℂ) where
  bound : ℝ
  bound_nonnegative : 0 ≤ bound
  log_coefficient_bound : ∀ i, ‖a i‖ ≤ bound

/-- Explicit proof-carrying analytic input for the assembled `r_h ≥ 2` closure.
Constructing this record requires all source support and coefficient packages,
and a proof of the claimed leakage statement. -/
structure RGeTwoFixedApplicationClosureInput
    (ι : Type*) (branchCoeff centeredWeight certificate logCoeff : ι → ℂ)
    (multiplicity : ι → ℕ) where
  support : PerfectPowerBranchSupport
  branchCoefficient : HBBranchCoefficientBound ι branchCoeff
  factorisationMultiplicity : BranchFactorisationMultiplicity ι multiplicity
  centeredWeightBound : CenteredWeightCrudeBound ι centeredWeight
  certificateBound : CertificateDivisorBound ι certificate
  normalizedLogBound : NormalizedLogCoefficientBound ι logCoeff
  arbitraryLogPowerLeakage : Prop
  proof : arbitraryLogPowerLeakage

/-- Transparent accessor for the assembled closure.  It proves only the
proposition explicitly proved inside the supplied record. -/
theorem R_GE_TWO_FIXED_APPLICATION_CLOSURE
    {ι : Type*} {branchCoeff centeredWeight certificate logCoeff : ι → ℂ}
    {multiplicity : ι → ℕ}
    (h : RGeTwoFixedApplicationClosureInput ι branchCoeff centeredWeight
      certificate logCoeff multiplicity) : h.arbitraryLogPowerLeakage :=
  h.proof

/-- Fable-derived ledger labels which are intentionally more precise than the
legacy project-wide status datatype. -/
inductive FableBankStatus where
  | leanProved
  | provedModuloSuppliedSource
  | conditionalInterface
  | fableDerivedPendingFormalAudit
  | rejectedAsUniversalisationSurrogate
  | rejectedAsMinimalFixedApplicationCore
  | falseBySourceGeometry
  | partialStatus
  | unresolvedInput
  deriving DecidableEq, Repr

structure FableStatusEntry where
  label : String
  status : FableBankStatus
  deriving Repr

def fableStatusLedger : List FableStatusEntry :=
  [ ⟨"PerfectPowerBranchSupport", .provedModuloSuppliedSource⟩
  , ⟨"PERFECT_POWER_DIVISOR_COUNT_CORE", .leanProved⟩
  , ⟨"HB_BRANCH_COEFFICIENT_BOUND", .conditionalInterface⟩
  , ⟨"BRANCH_FACTORISATION_MULTIPLICITY", .conditionalInterface⟩
  , ⟨"CENTERED_WEIGHT_CRUDE_BOUND", .conditionalInterface⟩
  , ⟨"CERTIFICATE_DIVISOR_BOUND", .conditionalInterface⟩
  , ⟨"R_GE_TWO_FIXED_APPLICATION_CLOSURE", .fableDerivedPendingFormalAudit⟩
  , ⟨"M0", .rejectedAsUniversalisationSurrogate⟩
  , ⟨"C2_MIN", .rejectedAsMinimalFixedApplicationCore⟩
  , ⟨"CU_NO_WINDOW_SUBSET", .falseBySourceGeometry⟩
  , ⟨"R1_PATTERN_SKELETON", .partialStatus⟩
  , ⟨"R1_EXACT_BINDING_CLASS", .unresolvedInput⟩
  , ⟨"UNIVERSAL_FORD_TYPE_II", .unresolvedInput⟩
  ]

end TwinPrimeProject
