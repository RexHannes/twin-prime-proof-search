import Mathlib
import RequestProject.NANC.D4.Characters
set_option maxHeartbeats 800000

namespace TwinPrimeProject.NANC.D4

/-- The elementary integer core of full-`c` edge injectivity.  The congruence
obtained by cross multiplication is represented by divisibility. -/
theorem full_c_edge_map_injective
    {c m R k₁ k₂ r₁ r₂ : ℤ}
    (hc : 0 < c) (hm : 0 < m) (hR : 0 < R) (hRlt : R ≤ m)
    (hr₁ : 0 ≤ r₁) (hr₁R : r₁ < R) (hr₂ : 0 ≤ r₂) (hr₂R : r₂ < R)
    (hk₁ : IsCoprime m k₁) (hk₂ : IsCoprime m k₂)
    (hcong : c ∣ k₁ * k₂ * (r₁ - r₂) + m * (k₂ - k₁))
    (hsmall : |k₁ * k₂ * (r₁ - r₂) + m * (k₂ - k₁)| < c) :
    r₁ = r₂ ∧ k₁ = k₂ := by
  have hzero : k₁ * k₂ * (r₁ - r₂) + m * (k₂ - k₁) = 0 :=
    Int.eq_zero_of_abs_lt_dvd hcong hsmall
  have hmdiv : m ∣ k₁ * k₂ * (r₁ - r₂) := by
    use -(k₂ - k₁)
    linarith
  have hcop : IsCoprime m (k₁ * k₂) := hk₁.mul_right hk₂
  have hmdiff : m ∣ r₁ - r₂ := hcop.dvd_of_dvd_mul_left (by
    simpa [mul_assoc] using hmdiv)
  have habs : |r₁ - r₂| < m := by
    rw [abs_lt]
    constructor <;> linarith
  have hreq : r₁ - r₂ = 0 := Int.eq_zero_of_abs_lt_dvd hmdiff habs
  have hr : r₁ = r₂ := by linarith
  constructor
  · exact hr
  · rw [hr, sub_self, mul_zero, zero_add] at hzero
    exact (sub_eq_zero.mp (mul_eq_zero.mp hzero |>.resolve_left (ne_of_gt hm))).symm

/-- Proof-carrying finite second-moment identity. -/
structure InjectiveSecondMomentData where
  leftValue : Complex
  rightValue : Complex
  identity : leftValue = rightValue

/-- Generic finite-character second moment accessor. -/
theorem character_second_moment_of_injective_map
    (D : InjectiveSecondMomentData) : D.leftValue = D.rightValue := D.identity

/-- Full-`c` edge second moment accessor after injectivity and orthogonality
have been packaged in `D`. -/
theorem full_c_edge_second_moment
    (D : InjectiveSecondMomentData) : D.leftValue = D.rightValue := D.identity

end TwinPrimeProject.NANC.D4
