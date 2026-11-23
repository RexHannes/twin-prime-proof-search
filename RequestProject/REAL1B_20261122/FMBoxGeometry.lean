import RequestProject.REAL1B_20261122.FMAnalyticTransfer

namespace REAL1B.FM.Analytic
open Filter Vaughan Source Closing ArithmeticFunction
noncomputable section
open Classical

theorem rank_gap {N : ℕ} {t : Fin N → ℝ} (hp : ∀ i, 0 ≤ t i) {i : Fin N}
    (hi : ε ≤ t i) (hl : t i ≤ Direct.lowerEdge) : ¬ Direct.rankTest t := by
  rintro ⟨r,_,hbig,ht⟩
  by_cases hz : r i = 0
  · have nn (j : Fin N) : 0 ≤ Direct.tinyCost (t j) (r j) := by
      unfold Direct.tinyCost
      split_ifs
      · exact hp j
      · exact le_max_right _ _
    have h := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin N))) => nn j) (Finset.mem_univ i)
    rw [Direct.tinyCost,if_pos hz] at h
    exact (not_lt.mpr hi) (h.trans_lt ht)
  · have hr : (1:ℝ) ≤ r i := by exact_mod_cast (show 1 ≤ r i by omega)
    have he : 0 ≤ Direct.lowerEdge := by norm_num [Direct.lowerEdge,ε]
    have h := hbig i (by omega)
    nlinarith only [hl,h,mul_le_mul_of_nonneg_right hr he]

theorem boxes_not_good {n : ℕ} (hb : boxes n) : ¬ Direct.good n := by
  obtain ⟨_,p,q,r,s,t,i,j,k,l,hf,had,hcell,_⟩ := hb
  rintro ⟨_,_,hr⟩
  let i₀ : Fin n.primeFactorsList.length := ⟨0,by simp [hf]⟩
  have hget : n.primeFactorsList.get i₀ = p := by simp [i₀,List.get_eq_getElem,hf]
  have hi := first_index_lower had
  have hu : i+1 ≤ 19 := had.2.2.2.2.2.1
  have ha : (4:ℝ) ≤ i := by exact_mod_cast hi
  have hc : (i:ℝ)+1 ≤ 19 := by exact_mod_cast hu
  apply rank_gap (i:=i₀) (t:=fun j => Real.log (n.primeFactorsList.get j)/Real.log n) _ _ _ hr
  · exact fun j => div_nonneg (Real.log_natCast_nonneg _) (Real.log_natCast_nonneg _)
  · dsimp only; rw [hget]; unfold ε; linarith only [hcell.1,ha]
  · dsimp only; rw [hget]; unfold Direct.lowerEdge ε; linarith only [hcell.2,hc]

private theorem box_prime_lower {x : ℝ} (hx : 4 ≤ x) {n p : ℕ} (hn : n ∈ interval (x/2))
    (hb : boxes n) (hp : p.Prime) (hd : p ∣ n) : x^(1/50:ℝ) < (p:ℝ) := by
  obtain ⟨h₁,_,h₂⟩ := window hn
  have hn' : (1:ℝ)<n := by exact_mod_cast (show 1<n by omega)
  have h2 := Real.log_le_log (by norm_num : (0:ℝ)<2) (by exact_mod_cast h₂ : (2:ℝ) ≤ n)
  have h3 := Real.log_le_log (by linarith : 0<x) (by linarith : x ≤ 2*(n:ℝ))
  rw [Real.log_mul (by norm_num) (by linarith)] at h3
  rw [Real.rpow_def_of_pos (by linarith : 0<x),← Real.exp_log (by exact_mod_cast hp.pos : (0:ℝ)<p),Real.exp_lt_exp]
  linarith only [h2,h3,boxes_prime_size hn' hb hp hd]

theorem boxes_Z {x : ℝ} (hx : 4 ≤ x) {n : ℕ} (hn : n ∈ interval (x/2))
    (hb : boxes n) : Sifted (z x) n := by
  intro p hp hd
  exact (Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ x)
    (by norm_num : (1/400000000000:ℝ) ≤ 1/50)).trans_lt (box_prime_lower hx hn hb hp hd)

theorem boxes_K_zero {x : ℝ} (hx : 4 ≤ x) {n : ℕ} (hn : n ∈ interval (x/2))
    (hb : boxes n) : kernelK (x/2) n = 0 := by
  have hX : 1 < x/2 := by linarith
  have hn₁ := (window hn).1
  have hn₂ : (1:ℝ)<n := by linarith
  have hlog := Real.log_le_log (by linarith : 0 < x/2) hn₁.le
  have hlabel (d : ℕ) (hd : d ∈ n.divisors) : labels (x/2) d = 0 := by
    unfold labels
    apply Finset.sum_eq_zero
    intro u hu
    apply Finset.sum_eq_zero
    intro v _
    apply Finset.sum_eq_zero
    intro w _
    apply if_neg
    rintro ⟨hp,_,_,hu',_⟩
    have hq := boxes_prime_size hn₂ hb hp ((Nat.mem_divisors.mp hu).1.trans (Nat.mem_divisors.mp hd).1)
    have hbank := Real.log_le_log (by exact_mod_cast hp.pos : (0:ℝ)<u) hu'.2
    rw [Real.log_rpow (by linarith : 0<x/2)] at hbank
    linarith only [hq,hbank,hlog,Real.log_pos hn₂]
  unfold kernelK
  rw [Finset.sum_eq_zero (fun d hd => by simp [hlabel d hd]),mul_zero]

theorem box_phi_eq_H {x : ℝ} (hx : 4 ≤ x) {n : ℕ} (hn : n ∈ interval (x/2)) (hb : boxes n) :
    Direct.psi x n = kernelH n := by
  have hsf := hb.1
  have hcard : cardFactors n = 5 := by
    obtain ⟨_,_,_,_,_,_,_,_,_,_,hf,_⟩ := hb
    simp [cardFactors_apply,hf]
  have hret : retained n := Or.inr ⟨by omega,by omega⟩
  simp [Direct.psi,hb,Direct.phi,Direct.F,Direct.G,hn,hsf,boxes_not_good hb,boxes_Z hx hn hb,hret,boxes_K_zero hx hn hb]

end
end REAL1B.FM.Analytic
#print axioms REAL1B.FM.Analytic.rank_gap
#print axioms REAL1B.FM.Analytic.boxes_not_good
#print axioms REAL1B.FM.Analytic.boxes_Z
#print axioms REAL1B.FM.Analytic.boxes_K_zero
#print axioms REAL1B.FM.Analytic.box_phi_eq_H
