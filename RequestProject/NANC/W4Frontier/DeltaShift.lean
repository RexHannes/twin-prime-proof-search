import Mathlib.Data.Nat.Prime.Basic
import RequestProject.NANC.W4Frontier.Exponents

namespace TwinPrimeProject.NANC.W4Frontier

/-- Two distinct primes in the R-range cannot both divide a positive shift
smaller than M when `R² > M`. -/
theorem unique_large_prime_divisor
    (R M delta r₁ r₂ : ℕ)
    (hRM : M < R * R)
    (hdelta0 : 0 < delta) (hdeltaM : delta < M)
    (hr₁ : r₁.Prime) (hr₂ : r₂.Prime)
    (hR₁ : R ≤ r₁) (hR₂ : R ≤ r₂)
    (hd₁ : r₁ ∣ delta) (hd₂ : r₂ ∣ delta) :
    r₁ = r₂ := by
  by_contra hne
  have hcop : r₁.Coprime r₂ := hr₁.coprime_iff_not_dvd.mpr (by
    intro hd
    have heq : r₁ = r₂ := (Nat.dvd_prime hr₂).mp hd |>.resolve_left hr₁.ne_one
    exact hne heq)
  have hprod : r₁ * r₂ ∣ delta := hcop.mul_dvd_of_dvd_of_dvd hd₁ hd₂
  have hle : r₁ * r₂ ≤ delta := Nat.le_of_dvd hdelta0 hprod
  have hRR : R * R ≤ r₁ * r₂ := Nat.mul_le_mul hR₁ hR₂
  omega

/-- Once the R-prime factor is unique, equality of products forces equality of
both support coordinates. -/
theorem delta_product_injective
    (r₁ r₂ : ℕ) (k₁ k₂ : ℤ) (hr : r₁ = r₂)
    (hk0 : (r₁ : ℤ) ≠ 0)
    (heq : (r₁ : ℤ) * k₁ = (r₂ : ℤ) * k₂) : k₁ = k₂ := by
  subst r₂
  exact mul_left_cancel₀ hk0 heq

def deltaShiftInjectiveStatus : BankStatus := .provedAlgebraic
def shortKFramingStatus : BankStatus := .retired

end TwinPrimeProject.NANC.W4Frontier
