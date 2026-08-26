import Gate04Root.GCD
import RequestProject.NANC.Gate01Root.AffineRoot

/-!
# Gate01Root: root gcd lemmas

From the affine relation `r α = m w₀ + 2` with `m` odd we get `gcd(α, m) = 1`,
and from `r β = m' w₀ + 2` with `m'` odd we get `gcd(β, m') = 1`.

The proofs use only: the congruence and the oddness of the modulus.  No
hypothesis on the size of `k` is used, and (as noted in the docstrings)
positivity of the modulus is not needed either.
-/

namespace RouteAFibreFrame
namespace Gate01Root

/-- **`gcd(α, m) = 1`** from `r α = m w₀ + 2` with `m` odd.

Positivity of `m` is not needed and is therefore not assumed. -/
theorem alpha_coprime_m_of_affine_odd {r alpha m w0 : ℤ} (hodd : Odd m)
    (haff : r * alpha = m * w0 + 2) : Int.gcd alpha m = 1 :=
  Gate04Root.alpha_coprime_m_of_odd (r := r) hodd ⟨w0, by linarith⟩

/-- **`gcd(β, m') = 1`** from `r β = m' w₀ + 2` with `m'` odd.

Positivity of `m'` is not needed and is therefore not assumed. -/
theorem beta_coprime_mPrime_of_affine_odd {r beta mPrime w0 : ℤ} (hodd : Odd mPrime)
    (haff : r * beta = mPrime * w0 + 2) : Int.gcd beta mPrime = 1 :=
  Gate04Root.beta_coprime_mPrime_of_odd (r := r) hodd ⟨w0, by linarith⟩

/-- Bézout form of `gcd(α, m) = 1`. -/
theorem isCoprime_alpha_m_of_affine_odd {r alpha m w0 : ℤ} (hodd : Odd m)
    (haff : r * alpha = m * w0 + 2) : IsCoprime alpha m :=
  Int.isCoprime_iff_gcd_eq_one.mpr (alpha_coprime_m_of_affine_odd (r := r) hodd haff)

/-- Bézout form of `gcd(β, m') = 1`. -/
theorem isCoprime_beta_mPrime_of_affine_odd {r beta mPrime w0 : ℤ} (hodd : Odd mPrime)
    (haff : r * beta = mPrime * w0 + 2) : IsCoprime beta mPrime :=
  Int.isCoprime_iff_gcd_eq_one.mpr (beta_coprime_mPrime_of_affine_odd (r := r) hodd haff)

namespace RootEdgeData

variable (e : RootEdgeData)

/-- For a root edge with odd `m`:  `gcd(α, m) = 1`. -/
theorem gcd_alpha_m_eq_one (hodd : Odd e.m) : Int.gcd e.alpha e.m = 1 :=
  alpha_coprime_m_of_affine_odd (r := e.r) (w0 := e.w0) hodd e.alpha_def

/-- For a root edge with odd `m'`:  `gcd(β, m') = 1`. -/
theorem gcd_beta_mPrime_eq_one (hodd : Odd e.mPrime) : Int.gcd e.beta e.mPrime = 1 :=
  beta_coprime_mPrime_of_affine_odd (r := e.r) (w0 := e.w0) hodd
    (root_beta_affine_relation e)

end RootEdgeData

end Gate01Root
end RouteAFibreFrame
