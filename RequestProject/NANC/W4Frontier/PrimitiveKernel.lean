import RequestProject.NANC.W4Frontier.Exponents

namespace TwinPrimeProject.NANC.W4Frontier

/-- Symbolic centered divisibility discrepancy over rational values. -/
def rho (ell x : ℕ) : ℚ := (if ell ∣ x then 1 else 0) - 1 / ell

/-- The primitive pair discrepancy, with an abstract finite time set and weight. -/
noncomputable def pairDiscrepancy {ι : Type} [Fintype ι]
    (W : ι → ℂ) (p q : ℕ) (A B : ι → ℕ) : ℂ :=
  ∑ t, W t * rho p (A t) * rho q (B t)

/-- Exact formal normalization `K = H E`. -/
def fordPairKernel (H E : ℂ) : ℂ := H * E

theorem fordPairKernel_mul_conj (H E E' : ℂ) :
    fordPairKernel H E * star (fordPairKernel H E') =
      (H * star H) * (E * star E') := by
  simp [fordPairKernel]
  ring

/-- Exponent form of `KCov = H² ECov`. -/
theorem kernel_covariance_normalization :
    (Mexp + Hexp) - 2 * Hexp = CountScaleTargetExp := by
  norm_num [CountScaleTargetExp]

/-- The analytic Fourier formula and covariance estimate remain outside the
constructive bank; this record can carry a supplied formulation and proof. -/
structure PrimitiveFourierInterface extends ConditionalInterface

/-- Count-scale covariance `ECov ≪ M/H`: explicitly open. -/
def countScaleCovarianceStatus : BankStatus := .open

end TwinPrimeProject.NANC.W4Frontier
