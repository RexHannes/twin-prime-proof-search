import Mathlib

/-!
# Corrective finite arithmetic for certificate and packet ledgers

These are elementary implications only.  They contain no analytic distribution
or cancellation estimate.
-/

namespace TwinPrimeProject

open scoped BigOperators

/-- If an odd shifted integer is divisible by a modulus, that modulus is odd. -/
theorem oddNImpliesOddShiftedModulus {n q : ℕ} (hn : Odd n) (hq : q ∣ n + 2) : Odd q := by
  rcases hn with ⟨k, rfl⟩
  rcases hq with ⟨r, hr⟩
  have hodd : Odd (2 * k + 1 + 2) := ⟨k + 1, by omega⟩
  exact (Nat.odd_mul.mp (hr ▸ hodd)).1

/-- Exponent form of the long-free-block complement implication. -/
theorem longFreeBlockComplementExponent {s c Θ η : ℝ}
    (htotal : s + c ≤ 1) (hs : 1 - Θ + η ≤ s) : c ≤ Θ - η := by
  linarith

theorem r9LongBlockThresholdFourNinths : (1 : ℚ) - 5 / 9 = 4 / 9 := by norm_num

theorem r10LongBlockThresholdSixtySevenOverOneSixty :
    (1 : ℚ) - 93 / 160 = 67 / 160 := by norm_num

theorem r9SkeletonCandidateThresholdThirteenOverEighteen :
    (4 / 9 : ℚ) + 5 / 18 = 13 / 18 := by norm_num

/-- Vaughan routing arithmetic at the r=9 exponent lock. -/
theorem r9VaughanParameterLockArithmetic {u v d ell η : ℝ}
    (hu : u = (5 / 9 - η) / 2) (hv : v = (5 / 9 - η) / 2)
    (hd : d ≤ u) (hell : ell ≤ v) :
    u + v = 5 / 9 - η ∧ d + ell ≤ 5 / 9 - η := by
  constructor <;> linarith

theorem r9VaughanHighPacketArithmetic {u v d ell η : ℝ}
    (hu : u = (5 / 9 - η) / 2) (hv : v = (5 / 9 - η) / 2)
    (hd : u < d) (hell : v < ell) : 5 / 9 - η < d + ell := by
  linarith

/-- Pointwise obstruction to a lower sieve weight whose level lies below a
prime in the sifting range.  The divisor sum is represented by its two values
at the divisors `1,t` of a prime. -/
theorem noLowerSieveWeightWhenLevelBelowSiftingPrime
    {D t z : ℕ} (hDt : D < t) (_htz : t < z) (_ht : Nat.Prime t)
    (lambda : ℕ → ℤ) (hlambda1 : lambda 1 = 1)
    (hsupport : ∀ d, D < d → lambda d = 0)
    (hlowerAtT : lambda 1 + lambda t ≤ 0) : False := by
  have hzero : lambda t = 0 := hsupport t hDt
  omega

/-- Correct two-variable support predicate. -/
def PairCertificateSupport (aν h x y : ℝ) : Prop := aν < x + y ∧ x + y ≤ h

theorem pairCertificateSupportCorrected (aν h x y : ℝ) :
    PairCertificateSupport aν h x y ↔ aν < x + y ∧ x + y ≤ h := Iff.rfl

/-- Correct three-variable window. -/
def TripleCertificateWindow (ν₀ h x y z : ℝ) : Prop :=
  3 * ν₀ < x + y + z ∧ x + y + z ≤ h

theorem tripleCertificateWindowCorrected (ε : ℚ) :
    (0 : ℚ) < 11 / 10000 - 2 * ε ↔ ε < 55 / 100000 := by
  constructor <;> intro h <;> linarith

/-- Abstract sparse-coefficient packet transfer, including a coefficient sup
norm `C` and representation bound `R`. -/
theorem sparseCoefficientPacketTransfer
    {ι : Type*} (s : Finset ι) (coeff value : ι → ℝ) (R M : ℝ)
    (hrep : ∀ i ∈ s, |value i| ≤ R)
    (hmass : ∑ i ∈ s, |coeff i| ≤ M) (hR : 0 ≤ R) :
    |∑ i ∈ s, coeff i * value i| ≤ R * M := by
  calc
    |∑ i ∈ s, coeff i * value i| ≤ ∑ i ∈ s, |coeff i * value i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ s, R * |coeff i| := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul]
      calc
        |coeff i| * |value i| ≤ |coeff i| * R :=
          mul_le_mul_of_nonneg_left (hrep i hi) (abs_nonneg _)
        _ = R * |coeff i| := mul_comm _ _
    _ = R * ∑ i ∈ s, |coeff i| := by rw [Finset.mul_sum]
    _ ≤ R * M := mul_le_mul_of_nonneg_left hmass hR

end TwinPrimeProject
