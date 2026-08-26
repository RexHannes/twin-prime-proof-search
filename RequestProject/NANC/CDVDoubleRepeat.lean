import RequestProject.Options
namespace TwinPrimeProject.NANC

theorem cdv_repeated_p_forces_p_div_tdiff (p m t₁ t₂ : ℤ)
    (hcop : IsCoprime p m) (h : p ∣ m*(t₁-t₂)) : p ∣ t₁-t₂ := hcop.dvd_of_dvd_mul_left h

theorem cdv_repeated_q_forces_q_div_tdiff (q m' t₁ t₂ : ℤ)
    (hcop : IsCoprime q m') (h : q ∣ m'*(t₁-t₂)) : q ∣ t₁-t₂ := hcop.dvd_of_dvd_mul_left h

theorem cdv_double_repeat_empty (p q d : ℤ) (hpq : IsCoprime p q)
    (hp : p ∣ d) (hq : q ∣ d) (hd0 : 0 < |d|) (hd : |d| < |p*q|) : False := by
  have hdvd : p*q ∣ d := hpq.mul_dvd hp hq
  have hn : d ≠ 0 := by intro h; subst d; simp at hd0
  have hle := Int.natAbs_le_of_dvd_ne_zero hdvd hn
  have habs : (|p*q|).natAbs ≤ (|d|).natAbs := by
    simpa only [Int.natAbs_abs] using hle
  have hcastd : ((|d|).natAbs : ℤ) = |d| := Int.natAbs_of_nonneg (abs_nonneg d)
  have hcastpq : ((|p*q|).natAbs : ℤ) = |p*q| := Int.natAbs_of_nonneg (abs_nonneg (p*q))
  have hlt : (|d|).natAbs < (|p*q|).natAbs := by
    apply (Nat.cast_lt (α := ℤ)).mp
    simpa [hcastd, hcastpq] using hd
  omega

theorem cdv_D_less_L2_highP3 (a b : ℚ) (ha : 5/18 ≤ a) (hb : a ≤ b) :
    2/3-a < 2*b := by linarith
end NANC
