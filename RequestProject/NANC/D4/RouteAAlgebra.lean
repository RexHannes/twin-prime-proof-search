import RequestProject.NANC.D4.BasicParams
import RequestProject.NANC.D4.Kloosterman

namespace TwinPrimeProject.NANC.D4

def ellExp (b : ℚ) : ℚ := 2 * b
def ellSqExp (b : ℚ) : ℚ := 4 * b
def routeAReducedLevelExp (b : ℚ) : ℚ := 2 * b + 1 / 3
def routeALiftedLevelExp (b : ℚ) : ℚ := 4 * b + 1 / 3

theorem routeA_KH_over_L2_exp (a b : ℚ) :
    K_exp a + H_exp a b - 2 * b = -(1 : ℚ) / 3 := by
  simp [K_exp, H_exp]
  ring

theorem routeA_reduced_level_lt_ell_sq {b : ℚ}
    (hb : (1 : ℚ) / 3 ≤ b) :
    routeAReducedLevelExp b < ellSqExp b := by
  simp [routeAReducedLevelExp, ellSqExp]
  linarith

theorem routeA_reduced_level_lt_ell_sq_iff {b : ℚ} :
    routeAReducedLevelExp b < ellSqExp b ↔ (1 : ℚ) / 6 < b := by
  simp [routeAReducedLevelExp, ellSqExp]
  constructor <;> intro h <;> linarith

theorem routeA_lifted_level_minus_reduced_level (b : ℚ) :
    routeALiftedLevelExp b - routeAReducedLevelExp b = 2 * b := by
  simp [routeALiftedLevelExp, routeAReducedLevelExp]
  ring

/-- Finite injectivity of the Route-A dispersion coordinate. -/
theorem dispersion_map_injective
    {ℓ₁ ℓ₂ h₁ h₂ h₁' h₂' : ℤ}
    (hℓ₁pos : 0 < ℓ₁) (hℓ₂pos : 0 < ℓ₂)
    (hcop : IsCoprime ℓ₁ ℓ₂)
    (hh₁ : |h₁ - h₁'| < ℓ₁) (hh₂ : |h₂ - h₂'| < ℓ₂)
    (heq : h₂ * ℓ₁ - h₁ * ℓ₂ = h₂' * ℓ₁ - h₁' * ℓ₂) :
    h₁ = h₁' ∧ h₂ = h₂' := by
  have hrel : (h₂ - h₂') * ℓ₁ = (h₁ - h₁') * ℓ₂ := by
    linarith
  have hd2 : ℓ₂ ∣ h₂ - h₂' := by
    apply hcop.symm.dvd_of_dvd_mul_left
    use h₁ - h₁'
    linarith
  have hz2 : h₂ - h₂' = 0 := Int.eq_zero_of_abs_lt_dvd hd2 hh₂
  have heq2 : h₂ = h₂' := sub_eq_zero.mp hz2
  subst h₂'
  have hzprod : (h₁ - h₁') * ℓ₂ = 0 := by linarith
  have hz1 : h₁ - h₁' = 0 := by
    rcases mul_eq_zero.mp hzprod with h | h
    · exact h
    · omega
  exact ⟨sub_eq_zero.mp hz1, rfl⟩

/-- `ROUTE_A_REPRESENTATION_MULTIPLICITY_ONE`, as the direct uniqueness
corollary of dispersion-map injectivity. -/
theorem routeA_representation_multiplicity_one
    {ℓ₁ ℓ₂ h₁ h₂ h₁' h₂' : ℤ}
    (hℓ₁pos : 0 < ℓ₁) (hℓ₂pos : 0 < ℓ₂)
    (hcop : IsCoprime ℓ₁ ℓ₂)
    (hh₁ : |h₁ - h₁'| < ℓ₁) (hh₂ : |h₂ - h₂'| < ℓ₂)
    (heq : h₂ * ℓ₁ - h₁ * ℓ₂ = h₂' * ℓ₁ - h₁' * ℓ₂) :
    (h₁, h₂) = (h₁', h₂') := by
  rcases dispersion_map_injective hℓ₁pos hℓ₂pos hcop hh₁ hh₂ heq with ⟨rfl, rfl⟩
  rfl

/-- Symbolic two-prime specialization of the existing structural modulus-lift
assembly. The arithmetic prime/copimality premises are recorded explicitly;
the conclusion itself follows from the supplied exact local identities. -/
theorem routeA_two_prime_lift
    {R : Type*} [CommRing R] (lifted localFactor base : R)
    {p₁ p₂ c A : ℕ}
    (hp₁ : Nat.Prime p₁) (hp₂ : Nat.Prime p₂) (hne : p₁ ≠ p₂)
    (hPc : Nat.Coprime (p₁ * p₂) c) (hAP : Nat.Coprime A (p₁ * p₂))
    (htwist : lifted = localFactor * base) (hramanujan : localFactor = 1) :
    lifted = base := by
  have h := kloosterman_modulus_lift lifted localFactor base (1 : R) htwist hramanujan
  simpa using h

end TwinPrimeProject.NANC.D4
