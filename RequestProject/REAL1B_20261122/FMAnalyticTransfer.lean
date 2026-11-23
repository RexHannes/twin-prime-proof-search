import RequestProject.REAL1B_20261122.FMAnalyticReduction

/-! Full and five-prime restricted sources require their own distribution estimates. -/
namespace REAL1B.FM.Analytic
open Filter Vaughan Source Closing
noncomputable section
open Classical

def mean (f : ℝ → ℕ → ℝ) (x : ℝ) := H2.series * total (x/2) (f x)

/-- Three distinct estimates at the original presieve. The unsigned charge includes
all nonsquarefree inputs, including those with internal proper powers. -/
structure VaughanEstimates (a : ℝ) (f : ℝ → ℕ → ℝ) : Prop where
  typeI_centered : negligible (fun x => typeI a x (f x) - mean f x) Sb
  short : negligible (fun x => shortProduct a x (f x)) Sb
  squareful : negligible (fun x => squarefulMass a x (f x)) Sb

theorem presieved_transfer {a : ℝ} {f : ℝ → ℕ → ℝ} (h : VaughanEstimates a f) :
    negligible (fun x => lambdaSum (roughW a x) x (f x) - mean f x - Direct.largeSum a x (f x)) Sb := by
  intro e he
  have ht : 0 < e/3 := by linarith
  filter_upwards [small_power (by norm_num : (0.24:ℝ) ≤ 1/2), h.typeI_centered _ ht,
    h.short _ ht,h.squareful _ ht,eventually_ge_atTop (8:ℝ)] with x hu hI hS hQ hx
  have hk (n : ℕ) (hn : n ∈ interval (x/2)) : 0 < n-2 := by
    have hn' := (window hn).1
    have : (2:ℝ) < n := by linarith
    exact Nat.sub_pos_of_lt (by exact_mod_cast this)
  have hv := physical_vaughan a x (f x) hu hk
  apply abs_le.mpr
  dsimp only at hI hS hQ ⊢
  constructor <;> linarith only [(abs_le.mp hv).1,(abs_le.mp hv).2,(abs_le.mp hI).1,
    (abs_le.mp hI).2,(abs_le.mp hS).1,(abs_le.mp hS).2,(le_abs_self _).trans hQ]

theorem native_covariance (x : ℝ) :
    covariance x = lambdaSum (intrinsicCut x) x (Direct.phi x) - mean Direct.phi x := by
  unfold covariance lambdaSum mean total
  rw [Finset.mul_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Direct.phi_eq_legacy hn]
  unfold intrinsicCut
  ring

theorem reduction_of_estimates {a : ℝ} (ha : a < 1) (hs : ScaleLower)
    (h : VaughanEstimates a Direct.phi) : Reduction a := by
  intro e he
  have ht : 0 < e/2 := by linarith
  filter_upwards [negligible_comparator (native_presieve ha) hs _ ht,presieved_transfer h _ ht]
    with x h₁ h₂
  rw [native_covariance,← Direct.whole_eq_legacy]
  unfold Direct.whole
  apply abs_le.mpr
  constructor <;> linarith only [(abs_le.mp h₁).1,(abs_le.mp h₁).2,(abs_le.mp h₂).1,(abs_le.mp h₂).2]

theorem box_power_mass : negligible (powerMass Direct.psi) scale := by
  apply power_mass_negligible
  filter_upwards [eventually_ge_atTop (8:ℝ)] with x _ n hn
  obtain ⟨_,hu,hl⟩ := window hn
  unfold Direct.psi
  split_ifs
  · exact (phi_envelope x (by omega : 1<n)).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _) hu (by norm_num)) (by unfold envelope; positivity))
  · rw [abs_zero]
    unfold envelope; positivity

theorem box_prime_source : ∀ᶠ x : ℝ in atTop, Direct.primeBox x = primeSum x (Direct.psi x) := by
  filter_upwards [boxes_sifted] with x hx
  unfold Direct.primeBox primeSum total
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hb : boxes n
  · simp [Direct.psi,hb,actual,sieve,hx n hn hb]
  · simp [Direct.psi,hb]

theorem calibration_of_estimates {a : ℝ} (ha : a < 1) (hs : ScaleLower)
    (h : VaughanEstimates a Direct.psi)
    (hm : negligible (fun x => mean Direct.psi x - Direct.J * Sb x) Sb) : Direct.Calibration a := by
  intro e he
  have ht : 0 < e/3 := by linarith
  filter_upwards [presieved_transfer h _ ht,negligible_comparator
    (prime_replacement (small_roughW ha) box_power_mass) hs _ ht,hm _ ht,box_prime_source] with x hv hp hJ hsource
  rw [hsource]
  unfold Direct.box
  apply abs_le.mpr
  constructor <;> linarith only [(abs_le.mp hv).1,(abs_le.mp hv).2,(abs_le.mp hp).1,(abs_le.mp hp).2,
    (abs_le.mp hJ).1,(abs_le.mp hJ).2]

end
end REAL1B.FM.Analytic
#print axioms REAL1B.FM.Analytic.presieved_transfer
#print axioms REAL1B.FM.Analytic.native_covariance
#print axioms REAL1B.FM.Analytic.reduction_of_estimates
#print axioms REAL1B.FM.Analytic.box_power_mass
#print axioms REAL1B.FM.Analytic.box_prime_source
#print axioms REAL1B.FM.Analytic.calibration_of_estimates
