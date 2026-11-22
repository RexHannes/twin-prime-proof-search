import RequestProject.REAL1B_20261122.H2Source

namespace REAL1B.H2
open ArithmeticFunction Filter Vaughan
noncomputable section
open Classical

private theorem sqrt_half {X : ℝ} (hx : 4 ≤ X) : Real.sqrt X ≤ X/2 := by
  apply (Real.sqrt_le_iff).2
  constructor
  · linarith
  · nlinarith [mul_nonneg (show 0 ≤ X by linarith) (show 0 ≤ X-4 by linarith)]

private theorem t_above {X : ℝ} {n : ℕ} (hx : 4 ≤ X) (hn : n ∈ interval X) :
    X/2 < ((n-2:ℕ):ℝ) := by
  have h := (Finset.mem_filter.mp hn).2
  have hk : 2 ≤ n := (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).1
  rw [Nat.cast_sub hk]
  norm_num at *
  linarith

theorem lowOutput_zero {X : ℝ} (hx : 4 ≤ X) : lowOutput X = 0 := by
  have hu : U X ≤ X/2 := calc
    X ^ (1/5:ℝ) ≤ X ^ (1/2:ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    _ ≤ X/2 := by rw [← Real.sqrt_eq_rpow]; exact sqrt_half hx
  unfold lowOutput op total
  apply Finset.sum_eq_zero
  intro n hn
  have ht := hu.trans_lt (t_above hx hn)
  simp [low,not_le.mpr ht]

theorem low_negligible : negligible lowOutput := by
  intro ε he
  filter_upwards [eventually_ge_atTop (4:ℝ)] with X hx
  rw [lowOutput_zero hx,abs_zero]
  exact mul_nonneg he.le (scale_pos (by linarith)).le

private theorem Z_small {X : ℝ} (hx : 4 ≤ X) (hl : 4 ≤ Real.log X) : Z X ≤ X/2 := by
  calc
    Z X ≤ Real.exp (Real.log X / 2) := by
      apply Real.exp_le_exp.mpr
      calc
        Real.log X ^ (0.24:ℝ) ≤ Real.log X ^ (1/2:ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
        _ ≤ _ := by rw [← Real.sqrt_eq_rpow]; exact sqrt_half hl
    _ = Real.sqrt X := by rw [Real.sqrt_eq_rpow,Real.rpow_def_of_pos (by linarith : 0<X)]; congr 1; ring
    _ ≤ X/2 := sqrt_half hx

private theorem fixed_abs (X : ℝ) (n : ℕ) : |fixed X n| ≤ 1 := by
  unfold fixed
  split_ifs
  · unfold mu
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := n))
  · norm_num

/-- Absolute correction on the actual dyadic source, dominated by all proper
prime powers through 2X. The presieve may only delete nonnegative Λ mass. -/
theorem correction_bound {X : ℝ} (hx : 4 ≤ X) (hl : 4 ≤ Real.log X) :
    |primeCorrection X| ≤ 2 * Real.sqrt (2*X) * Real.log (2*X) := by
  let s := interval X
  let g := fun t : ℕ => if t.Prime then 0 else lam t
  have hg (t : ℕ) : 0 ≤ g t := by dsimp [g]; split_ifs <;> first | rfl | exact vonMangoldt_nonneg
  have hb (n : ℕ) (hn : n ∈ s) :
      |fixed X n * (theta (n-2) - sieve (Z X) (n-2) * lam (n-2))| ≤ g (n-2) := by
    rw [abs_mul]
    by_cases h : (n-2).Prime
    · have hz := (Z_small hx hl).trans_lt (t_above hx hn)
      have hs : Sifted (Z X) (n-2) := by
        intro p hp hd
        rcases (Nat.dvd_prime h).mp hd with rfl | rfl
        · exact (hp.ne_one rfl).elim
        · exact hz
      simp [g,theta,h,sieve,hs,lam,vonMangoldt_apply_prime h]
    · have hΛ : 0 ≤ lam (n-2) := vonMangoldt_nonneg
      by_cases hR : Sifted (Z X) (n-2)
      · simpa [g,theta,h,sieve,hR,abs_of_nonneg hΛ] using
          (mul_le_mul_of_nonneg_right (fixed_abs X n) hΛ)
      · simp [g,theta,h,sieve,hR,hΛ]
  have hinj : Set.InjOn (fun n : ℕ => n-2) (↑s : Set ℕ) := by
    intro a ha b hb he
    have hlo (k : ℕ) (hk : k ∈ s) : 2 ≤ k :=
      (Finset.mem_Icc.mp (Finset.mem_filter.mp hk).1).1
    have := hlo a ha
    have := hlo b hb
    change a-2=b-2 at he
    omega
  have hsub : s.image (fun n : ℕ => n-2) ⊆ Finset.Ioc 0 ⌊2*X⌋₊ := by
    intro t ht
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp ht
    have hk := Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1
    have ht := t_above hx hn
    have hp : 0 < ((n-2:ℕ):ℝ) := by linarith
    exact Finset.mem_Ioc.mpr ⟨by exact_mod_cast hp, by omega⟩
  calc
    |primeCorrection X| ≤ _ := by unfold primeCorrection total; exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ s, g (n-2) := Finset.sum_le_sum hb
    _ = ∑ t ∈ s.image (fun n : ℕ => n-2), g t := (Finset.sum_image hinj).symm
    _ ≤ ∑ t ∈ Finset.Ioc 0 ⌊2*X⌋₊, g t := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => hg i)
    _ = Chebyshev.psi (2*X) - Chebyshev.theta (2*X) := by
      rw [Chebyshev.psi_sub_theta_eq_sum_not_prime, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro t _
      by_cases h : t.Prime <;> simp [g,h,lam]
    _ ≤ _ := (le_abs_self _).trans (Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log (by linarith))

private theorem error_small (ε : ℝ) (he : 0 < ε) :
    ∀ᶠ X : ℝ in atTop, 2 * Real.sqrt (2*X) * Real.log (2*X) ≤ ε * N0 X := by
  have hc := mul_pos he series_pos
  have ht : Tendsto (fun X : ℝ => (2*X)^(1/8:ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/8)).comp
      (Filter.tendsto_id.const_mul_atTop (by norm_num : (0:ℝ)<2))
  filter_upwards [ht.eventually_ge_atTop (max 1 (256/(ε*series))), eventually_gt_atTop (1:ℝ)]
    with X hbig hx
  let s := (2*X)^(1/8:ℝ)
  have h1 : 1 ≤ s := (le_max_left _ _).trans hbig
  have hh : 256 ≤ ε*series*s := by
    have h := (div_le_iff₀ hc).mp ((le_max_right _ _).trans hbig)
    linarith
  have hsq : Real.sqrt (2*X) = s^4 := by
    dsimp [s]
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast (by linarith : 0 ≤ 2*X)]
    norm_num
  have h8 : s^8 = 2*X := by
    dsimp [s]
    rw [← Real.rpow_mul_natCast (by linarith : 0 ≤ 2*X)]
    norm_num
  have hlog : Real.log (2*X) ≤ 8*s := by
    have h := Real.log_le_rpow_div (x := 2*X) (ε := 1/8) (by linarith) (by norm_num)
    linarith
  have hlogX := Real.log_le_log (by linarith : 0<X) (by linarith : X ≤ 2*X)
  have hlog0 := Real.log_pos hx
  rw [N0, ← mul_div_assoc, le_div_iff₀ hlog0, hsq]
  have hXs : Real.log X ≤ 8*s := hlogX.trans hlog
  have hprod := mul_le_mul hlog hXs hlog0.le (by positivity : 0 ≤ 8*s)
  have hc' : 256 ≤ (ε*series)*s^2 := by
    nlinarith [mul_nonneg (show 0 ≤ ε*series*s by positivity) (sub_nonneg.mpr h1)]
  calc
    2*s^4*Real.log (2*X)*Real.log X ≤ 2*s^4*((8*s)*(8*s)) := by
      rw [mul_assoc (2*s^4)]
      exact mul_le_mul_of_nonneg_left hprod (by positivity)
    _ ≤ ε*(series*X) := by
      have hh := mul_le_mul_of_nonneg_right hc' (show 0 ≤ s^6 by positivity)
      linear_combination hh/2 + (ε*series/2)*h8

theorem correction_negligible : negligible primeCorrection := by
  intro ε he
  filter_upwards [eventually_ge_atTop (4:ℝ), Real.tendsto_log_atTop.eventually_ge_atTop 4,
    error_small ε he] with X hx hl h
  exact (correction_bound hx hl).trans h

end
end REAL1B.H2

#print axioms REAL1B.H2.lowOutput_zero
#print axioms REAL1B.H2.low_negligible
#print axioms REAL1B.H2.correction_bound
#print axioms REAL1B.H2.correction_negligible
