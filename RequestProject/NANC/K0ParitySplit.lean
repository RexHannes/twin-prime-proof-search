import RequestProject.Options
namespace TwinPrimeProject.NANC

theorem k0_even_parity_band (Aplus Aminus C μ : ℚ)
    (hadd : Aplus = Aminus + C) (hneg : Aminus = -μ * Aplus) (hμ : μ = 1) :
    Aminus = -C / 2 := by
  subst μ
  linarith

theorem k0_odd_parity_band_zero (Aplus Aminus C μ : ℚ)
    (hadd : Aplus = Aminus + C) (hneg : Aminus = -μ * Aplus) (hμ : μ = -1) :
    C = 0 := by
  subst μ
  linarith

theorem k0_parity_split (Aplus Aminus C μ : ℚ)
    (hadd : Aplus = Aminus + C) (hneg : Aminus = -μ * Aplus)
    (hμ : μ = 1 ∨ μ = -1) :
    Aminus = (1 - μ) / 2 * Aminus - (1 + μ) / 4 * C := by
  rcases hμ with rfl | rfl <;> norm_num at * <;> linarith

theorem k0_plus_sign_counterexample :
    let μ : ℚ := 1; let C : ℚ := 2; let Aminus : ℚ := -1
    Aminus ≠ (1 - μ) / 2 * Aminus + (1 + μ) / 4 * C := by norm_num
end NANC
