import RequestProject.REAL1B_20261122.FMAnalyticWeights

/-! Gold 4.58 Part II (4.2): changing the input presieve on the original
von Mangoldt source costs o(x/log x). The source bound is proved internally. -/
namespace REAL1B.FM.Analytic
open Filter Vaughan Source Closing ArithmeticFunction
noncomputable section
open Classical

def negligible (f s : ℝ → ℝ) : Prop :=
  ∀ e : ℝ, 0 < e → ∀ᶠ x : ℝ in atTop, |f x| ≤ e * s x

def scale (x : ℝ) := x / Real.log x
def ScaleLower : Prop := ∃ c : ℝ, 0 < c ∧ ∀ᶠ x : ℝ in atTop, c * scale x ≤ Sb x

theorem comparator_pos (h : ScaleLower) : ∀ᶠ x : ℝ in atTop, 0 < Sb x := by
  obtain ⟨c,hc,h⟩ := h
  filter_upwards [eventually_gt_atTop (1:ℝ), h] with x hx hh
  exact (mul_pos hc (div_pos (by linarith) (Real.log_pos hx))).trans_le hh

theorem negligible_comparator {f : ℝ → ℝ} (hf : negligible f scale) (hs : ScaleLower) :
    negligible f Sb := by
  obtain ⟨c,hc,h⟩ := hs
  intro e he
  filter_upwards [hf (e*c) (mul_pos he hc),h] with x hx hs
  linarith only [hx, mul_le_mul_of_nonneg_left hs he.le]

def powerMass (f : ℝ → ℕ → ℝ) (x : ℝ) := total (x/2) (fun n =>
  (if (n-2).Prime then 0 else lam (n-2)) * |f x n|)

theorem window {x : ℝ} {n : ℕ} (hn : n ∈ interval (x/2)) :
    x/2 < (n:ℝ) ∧ (n:ℝ) ≤ x ∧ 2 ≤ n := by
  obtain ⟨hm,hx⟩ := Finset.mem_filter.mp hn
  obtain ⟨hn₀,hh⟩ := Finset.mem_Icc.mp hm
  have hh' : n ≤ ⌊x⌋₊ := by simpa only [show 2*(x/2)=x by ring] using hh
  have hpos : 0 ≤ x := by
    by_contra! h
    rw [Nat.floor_of_nonpos h.le] at hh'
    omega
  exact ⟨hx,(Nat.le_floor_iff hpos).mp hh',hn₀⟩

private theorem power_population {x : ℝ} (hx : 8 ≤ x) :
    (∑ n ∈ interval (x/2), if (n-2).Prime then 0 else lam (n-2)) ≤
      2 * Real.sqrt x * Real.log x := by
  let I := (interval (x/2)).image (fun n : ℕ => n-2)
  have inj : Set.InjOn (fun n : ℕ => n-2) (interval (x/2) : Set ℕ) := by
    intro m hm n hn h
    have := (window hm).2.2
    have := (window hn).2.2
    change m-2 = n-2 at h
    omega
  have hsub : I ⊆ Finset.Ioc 0 ⌊x⌋₊ := by
    intro k hk
    obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hk
    obtain ⟨hn₁,hn₂,_⟩ := window hn
    have hn' : 4 < n := by exact_mod_cast (show (4:ℝ) < n by linarith)
    exact Finset.mem_Ioc.mpr ⟨by omega, (Nat.sub_le _ _).trans (Nat.le_floor hn₂)⟩
  calc
    _ = ∑ k ∈ I, if k.Prime then 0 else lam k := (Finset.sum_image inj).symm
    _ ≤ ∑ k ∈ Finset.Ioc 0 ⌊x⌋₊, if k.Prime then 0 else lam k :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => by split_ifs <;> first | exact le_refl _ | exact vonMangoldt_nonneg)
    _ = Chebyshev.psi x - Chebyshev.theta x := by
      rw [Chebyshev.psi_sub_theta_eq_sum_not_prime, Finset.sum_filter]
      simp [lam, ite_not]
    _ ≤ _ := (le_abs_self _).trans (Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log (by linarith))

theorem power_mass_bound {x : ℝ} (hx : 8 ≤ x) {f : ℝ → ℕ → ℝ}
    {B : ℝ} (hB : 0 ≤ B) (hf : ∀ n ∈ interval (x/2), |f x n| ≤ B) :
    powerMass f x ≤ B * (2 * Real.sqrt x * Real.log x) := by
  unfold powerMass total
  calc
    _ ≤ ∑ n ∈ interval (x/2), (if (n-2).Prime then 0 else lam (n-2)) * B := by
      apply Finset.sum_le_sum
      intro n hn
      exact mul_le_mul_of_nonneg_left (hf n hn) (by split_ifs <;> first | exact le_refl _ | exact vonMangoldt_nonneg)
    _ ≤ _ := by rw [← Finset.sum_mul, mul_comm]; exact mul_le_mul_of_nonneg_left (power_population hx) hB

theorem power_mass_negligible {f : ℝ → ℕ → ℝ}
    (hf : ∀ᶠ x : ℝ in atTop, ∀ n ∈ interval (x/2), |f x n| ≤ envelope * x^(1/4:ℝ)) :
    negligible (powerMass f) scale := by
  have hC : 0 < envelope := by unfold envelope; positivity
  intro e he
  have hη : 0 < e / (2*envelope) := div_pos he (by positivity)
  have hlog := (isLittleO_log_rpow_rpow_atTop (2:ℝ) (by norm_num : (0:ℝ)<1/4)).bound hη
  filter_upwards [hf,hlog,eventually_ge_atTop (8:ℝ)] with x hx hl h₈
  have hpos : 0 < x := by linarith
  have hL : 0 < Real.log x := Real.log_pos (by linarith)
  have hQ := Real.rpow_pos_of_pos hpos (1/4:ℝ)
  have h1 := power_mass_bound h₈ (mul_nonneg hC.le hQ.le) hx
  have h2 : 0 ≤ powerMass f x := by
    unfold powerMass total
    apply Finset.sum_nonneg
    intro n _
    apply mul_nonneg _ (abs_nonneg _)
    split_ifs <;> first | exact le_refl _ | exact vonMangoldt_nonneg
  have hh : (Real.log x)^2 ≤ (e/(2*envelope))*x^(1/4:ℝ) := by
    simpa only [Real.norm_eq_abs, Real.rpow_two, abs_of_nonneg (sq_nonneg (Real.log x)), abs_of_pos hQ] using hl
  have hpow : (x^(1/4:ℝ)*Real.sqrt x)*x^(1/4:ℝ) = x := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hpos, ← Real.rpow_add hpos]
    norm_num
  rw [abs_of_nonneg h2, scale, ← mul_div_assoc, le_div_iff₀ hL]
  have hcost := (le_div_iff₀ (by positivity : 0 < 2*envelope)).mp
    (show (Real.log x)^2 ≤ e*x^(1/4:ℝ)/(2*envelope) by convert hh using 1; ring)
  nlinarith only [mul_le_mul_of_nonneg_right h1 hL.le,
    mul_le_mul_of_nonneg_right hcost (mul_nonneg hQ.le (Real.sqrt_nonneg x)), congrArg (fun t => e*t) hpow]

theorem native_power_mass : negligible (powerMass Direct.phi) scale := by
  apply power_mass_negligible
  filter_upwards [eventually_ge_atTop (8:ℝ)] with x hx n hn
  obtain ⟨_,hu,hl⟩ := window hn
  exact (phi_envelope x (by omega : 1<n)).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (Nat.cast_nonneg _) hu (by norm_num)) (by unfold envelope; positivity))

end
end REAL1B.FM.Analytic
#print axioms REAL1B.FM.Analytic.comparator_pos
#print axioms REAL1B.FM.Analytic.negligible_comparator
#print axioms REAL1B.FM.Analytic.power_mass_bound
#print axioms REAL1B.FM.Analytic.native_power_mass
