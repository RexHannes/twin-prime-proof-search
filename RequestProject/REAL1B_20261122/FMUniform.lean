import RequestProject.REAL1B_20261122.FMGoodSupport

namespace REAL1B.FM.GoodSupport
open Source Analytic Box ArithmeticFunction Vaughan
noncomputable section
open Classical

/-- All active good-set prime coordinates exceed or meet ν, so at most five fit. -/
theorem active_rank {n : ℕ} (hs : Squarefree n) (hg : Direct.good n) (hH : kernelH n ≠ 0) :
    cardFactors n ≤ 5 := by
  have point (p : ℕ) (hp : p ∈ n.primeFactorsList) : ν ≤ coord n p := by
    obtain ⟨hprime,hd⟩ := (Nat.mem_primeFactorsList hs.ne_zero).mp hp
    exact (cutoff_iff hg.1 hprime).mp (le_of_not_gt (fun h => hH (small_prime_cancels hs hg hprime hd h)))
  have lower (l : List ℕ) (hl : l.Sublist n.primeFactorsList) : (l.length:ℝ)*ν ≤ Box.mass n l := by
    induction l with
    | nil => simp [Box.mass]
    | cons p l ih =>
      have hh := point p (hl.subset List.mem_cons_self)
      have ht := ih ((List.sublist_cons_self p l).trans hl)
      simp only [Box.mass,List.map_cons,List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one] at ht ⊢
      linarith only [hh,ht]
  have hh := lower _ (.refl _)
  rw [log_mass (.refl _),Nat.prod_primeFactorsList hs.ne_zero,div_self (Real.log_pos (by exact_mod_cast hg.1)).ne'] at hh
  by_contra hn
  have hl : (6:ℝ) ≤ n.primeFactorsList.length := by exact_mod_cast (show 6 ≤ cardFactors n by omega)
  norm_num [ν,ε] at hh
  linarith

private theorem divisors_cap {n : ℕ} (hs : Squarefree n) (h : cardFactors n ≤ 255) :
    (n.divisors.card:ℝ) ≤ 2^(255:ℕ) := by
  have hc : n.primeFactors.card ≤ n.primeFactorsList.length := List.toFinset_card_le _
  have hd : n.divisors.card = 2^n.primeFactors.card := by
    rw [Nat.card_divisors hs.ne_zero]
    calc
      _ = ∏ _ ∈ n.primeFactors, 2 := Finset.prod_congr rfl (fun p hp => by
        rw [Nat.factorization_eq_one_of_squarefree hs (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)])
      _ = _ := by simp
  rw [hd,Nat.cast_pow,Nat.cast_ofNat]
  exact pow_le_pow_right₀ (by norm_num) (hc.trans h)

/-- An absolute coefficient bound for the entire signed native source.
The retained sectors have rank at most 255 and all active good outputs have rank at most five. -/
theorem uniform_phi (x : ℝ) (n : ℕ) : |Direct.phi x n| ≤ 2 * ((2:ℝ)^255)^4 := by
  let C : ℝ := (2:ℝ)^255
  have hC : 1 ≤ C := one_le_pow₀ (by norm_num)
  have hc₄ : C ≤ C^4 := by simpa using pow_le_pow_right₀ hC (show 1 ≤ 4 by decide)
  have hnn : 0 ≤ C^4 := by positivity
  change _ ≤ 2*C^4
  unfold Direct.phi Direct.F Direct.G
  by_cases hF : n ∈ interval (x/2) ∧ Squarefree n ∧ ¬Direct.good n ∧ Sifted (z x) n ∧ retained n
  · rw [if_pos hF,if_neg (fun h => hF.2.2.1 h.2.2),sub_zero]
    have hr : cardFactors n ≤ 255 := by rcases hF.2.2.2.2 with h | h <;> omega
    have hd : (n.divisors.card:ℝ) ≤ C := divisors_cap hF.2.1 hr
    have hH := (H_abs n).trans (hd.trans hc₄)
    have hK := (K_abs (x/2) (window hF.1).2.2).trans (pow_le_pow_left₀ (Nat.cast_nonneg _) hd 4)
    linarith only [abs_sub (kernelH n) (kernelK (x/2) n),hH,hK]
  · rw [if_neg hF]
    split_ifs with hg
    · by_cases hH : kernelH n = 0
      · simp [hH]; linarith only [hnn]
      · have hd := divisors_cap hg.2.1 ((active_rank hg.2.1 hg.2.2 hH).trans (by decide))
        have hh : |kernelH n| ≤ C^4 := (H_abs n).trans (hd.trans hc₄)
        rw [zero_sub,abs_neg,abs_of_nonneg (le_max_right _ _)]
        exact (max_le ((neg_le_abs _).trans hh) hnn).trans (by linarith only [hnn])
    · simp only [sub_zero,abs_zero]; linarith only [hnn]

theorem uniform_psi (x : ℝ) (n : ℕ) : |Direct.psi x n| ≤ 2 * ((2:ℝ)^255)^4 := by
  unfold Direct.psi
  split_ifs
  · exact uniform_phi x n
  · rw [abs_zero]; positivity

end
end REAL1B.FM.GoodSupport
#print axioms REAL1B.FM.GoodSupport.active_rank
#print axioms REAL1B.FM.GoodSupport.uniform_phi
#print axioms REAL1B.FM.GoodSupport.uniform_psi
