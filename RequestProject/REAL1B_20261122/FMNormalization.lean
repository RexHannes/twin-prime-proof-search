import RequestProject.REAL1B_20261122.FMProfileTransfer

/-! The comparator's Euler main term and the raw shifted-prime count. -/
namespace REAL1B.FM.Normalization
open Filter Vaughan Source Analytic Profile Finset
noncomputable section
open Classical

def productUpTo (N : ℕ) (f : ℕ → ℝ) := ∏ p ∈ (range (N+1)).filter Nat.Prime, f p
def usual (p : ℕ) : ℝ := 1-1/(p:ℝ)
def shifted (p : ℕ) : ℝ := if p=2 then 1 else 1-1/((p:ℝ)-1)
def singular (N : ℕ) := 2 * ∏ k ∈ range (N-2), (1+H2.offset k)

theorem odd_factor {p : ℕ} (hp : 2<p) : shifted p/usual p = 1-1/((p:ℝ)-1)^2 := by
  have h : (2:ℝ)<p := by exact_mod_cast hp
  rw [shifted,if_neg (by omega),usual]
  apply (div_eq_iff (ne_of_gt (show 0<1-1/(p:ℝ) by apply sub_pos.mpr; apply (div_lt_one (by linarith)).mpr; linarith))).mpr
  field_simp [show (p:ℝ) ≠ 0 by linarith,show (p:ℝ)-1 ≠ 0 by linarith]
  ring

theorem usual_pos (N : ℕ) : 0 < productUpTo N usual := by
  apply prod_pos
  intro p hp
  have h : (1:ℝ)<p := by exact_mod_cast (mem_filter.mp hp).2.one_lt
  unfold usual
  exact sub_pos.mpr ((div_lt_one (by linarith)).mpr h)

private theorem step (N : ℕ) (f : ℕ → ℝ) : productUpTo (N+1) f = productUpTo N f *
    (if (N+1).Prime then f (N+1) else 1) := by
  simp [productUpTo,Finset.prod_filter,Finset.prod_range_succ]

theorem euler_ratio {N : ℕ} (hN : 2≤N) : productUpTo N shifted / productUpTo N usual = singular N := by
  induction N, hN using Nat.le_induction with
  | base => norm_num [productUpTo,shifted,usual,singular,Finset.prod_filter,Finset.prod_range_succ,Nat.prime_two]
  | succ n hn ih =>
    rw [step,step,mul_div_mul_comm,ih]
    have hsize : n+1-2 = (n-2)+1 := by omega
    simp only [singular,hsize,prod_range_succ,← mul_assoc]
    congr 1
    have he : n-2+3 = n+1 := by omega
    have hcast : (↑(n-2):ℝ)+2 = (↑(n+1):ℝ)-1 := by push_cast [Nat.cast_sub hn]; ring
    unfold H2.offset
    rw [he,hcast]
    by_cases hp : (n+1).Prime
    · simp only [hp,if_true,odd_factor (by omega : 2<n+1)]; ring
    · simp [hp]

theorem singular_limit : Tendsto (fun x : ℝ => singular ⌊y x⌋₊) atTop (nhds H2.series) := by
  have hy := Real.tendsto_exp_atTop.comp ((tendsto_rpow_atTop (by norm_num : 0<(1/20:ℝ))).comp Real.tendsto_log_atTop)
  have hfloor : Tendsto (fun x : ℝ => ⌊y x⌋₊) atTop atTop := tendsto_nat_floor_atTop.comp hy
  have hindex : Tendsto (fun x : ℝ => ⌊y x⌋₊-2) atTop atTop := by
    apply tendsto_atTop.2
    intro n
    filter_upwards [hfloor.eventually_ge_atTop (n+2)] with x hx
    omega
  exact tendsto_const_nhds.mul (H2.euler_converges.hasProd.tendsto_prod_nat.comp hindex)

def rawCount (x : ℝ) := total (x/2) (fun n => sieve (y x) (n-2) * primeMask n)

/-- The input sieve remains on n-2. The output sieve is one on the genuine prime n. -/
theorem comparator_count : ∀ᶠ x : ℝ in atTop, Sb x = rawCount x / density x := by
  filter_upwards [Closing.log_power_lt_linear (a:=1/20) (b:=1/2) (by norm_num) (by norm_num),
    small_power (by norm_num : (1/2:ℝ) ≤ 1/2),eventually_gt_atTop (1:ℝ)] with x hl hpow hx
  have hy : y x < x^(1/2:ℝ) := by
    rw [y,Real.rpow_def_of_pos (by linarith : 0<x),Real.exp_lt_exp]
    linarith only [hl]
  unfold Sb rawCount total
  rw [Finset.sum_div]
  apply sum_congr rfl
  intro n hn
  by_cases hp : n.Prime
  · have hs : Sifted (y x) n := by
      intro p hprime hd
      rw [(Nat.prime_dvd_prime_iff_eq hprime hp).mp hd]
      exact ((hy.trans (hpow n hn)).trans_le (by exact_mod_cast Nat.sub_le n 2))
    simp [Source.compare,sieve,hs,primeMask,hp]
  · simp [primeMask,hp]

/-- The presieve error is measured before dividing by its thinning density. -/
def ShiftedPrimeEstimate : Prop := ∀ e : ℝ, 0<e → ∀ᶠ x : ℝ in atTop,
    |rawCount x - productUpTo ⌊y x⌋₊ shifted * (scale x/2)| ≤ e * density x * scale x

theorem normalized_of_shifted_primes (h : ShiftedPrimeEstimate) : Profile.Normalization := by
  intro e he
  have ht : 0<e/2 := by linarith
  have hc := (Metric.tendsto_nhds.mp singular_limit e he)
  have hy := Real.tendsto_exp_atTop.comp ((tendsto_rpow_atTop (by norm_num : 0<(1/20:ℝ))).comp Real.tendsto_log_atTop)
  filter_upwards [hc,h _ ht,comparator_count,hy.eventually_ge_atTop 2,eventually_gt_atTop (1:ℝ)]
    with x hc hraw hs hy hx
  have hn : 2 ≤ ⌊y x⌋₊ := Nat.le_floor (by exact hy)
  have hd : 0 < density x := usual_pos _
  have heq : productUpTo ⌊y x⌋₊ shifted = singular ⌊y x⌋₊ * density x :=
    (div_eq_iff (ne_of_gt hd)).mp (euler_ratio hn)
  have hsc : 0 < scale x := div_pos (by linarith) (Real.log_pos hx)
  change |Sb x - (H2.series/2)*scale x| ≤ _
  rw [hs]
  rw [Real.dist_eq] at hc
  rw [heq] at hraw
  have hbound : |rawCount x/density x - singular ⌊y x⌋₊*(scale x/2)| ≤ e/2 * scale x := by
    rw [show rawCount x/density x - singular ⌊y x⌋₊*(scale x/2) =
      (rawCount x-singular ⌊y x⌋₊*density x*(scale x/2))/density x by field_simp]
    rw [abs_div,abs_of_pos hd]
    exact (div_le_iff₀ hd).mpr (by linarith only [hraw])
  have hdiff := mul_le_mul_of_nonneg_right (abs_le.mp hc.le).1 (show 0≤scale x/2 by positivity)
  have hdiff' := mul_le_mul_of_nonneg_right (abs_le.mp hc.le).2 (show 0≤scale x/2 by positivity)
  exact abs_le.mpr ⟨by linarith only [(abs_le.mp hbound).1,hdiff],by linarith only [(abs_le.mp hbound).2,hdiff']⟩

end
end REAL1B.FM.Normalization
#print axioms REAL1B.FM.Normalization.euler_ratio
#print axioms REAL1B.FM.Normalization.singular_limit
#print axioms REAL1B.FM.Normalization.comparator_count
#print axioms REAL1B.FM.Normalization.normalized_of_shifted_primes
