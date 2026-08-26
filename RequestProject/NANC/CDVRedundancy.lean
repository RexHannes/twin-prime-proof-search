import RequestProject.Options
namespace TwinPrimeProject.NANC

theorem cdv_M2_redundant_from_M1_M3
    (p₁ p₂ q₁ q₂ u₁ u₂ v₁ v₂ m m' z k : ℤ)
    (hm : m ≠ 0) (M1 : p₁*u₁-p₂*u₂=m*z)
    (M31 : m'*p₁*u₁-m*q₁*v₁=2*k) (M32 : m'*p₂*u₂-m*q₂*v₂=2*k) :
    q₁*v₁-q₂*v₂=m'*z := by
  apply (mul_left_cancel₀ hm)
  have h : m*(q₁*v₁-q₂*v₂) = m*(m'*z) := by
    linear_combination -(M31 - M32 - m' * M1)
  exact h

structure CDVMixedCovarianceTheorem where bound : Prop
end NANC
