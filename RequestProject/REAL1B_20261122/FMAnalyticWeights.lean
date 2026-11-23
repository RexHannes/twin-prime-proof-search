import RequestProject.REAL1B_20261122.FMSemantics

/-! A coarse pointwise envelope for the actual FM output, sufficient to discard
proper prime powers. No boundedness or sign hypothesis on the output is used. -/
namespace REAL1B.FM.Analytic
open ArithmeticFunction Source Vaughan
noncomputable section
open Classical

private theorem mu_abs (n : ℕ) : |mu n| ≤ 1 := by
  unfold mu
  exact_mod_cast abs_moebius_le_one (n := n)

private theorem g0_abs (v : List ℝ) : |g0 v| ≤ 1 := by
  unfold g0
  split <;> (try split_ifs) <;> norm_num

theorem H_abs (n : ℕ) : |kernelH n| ≤ n.divisors.card := by
  apply (Finset.abs_sum_le_sum_abs ..).trans
  calc
    _ ≤ ∑ _ ∈ n.divisors, (1:ℝ) := by
      apply Finset.sum_le_sum
      intro d _
      dsimp only [divisorCoefficient]
      split_ifs
      · rw [abs_mul]
        exact mul_le_one₀ (mu_abs _) (abs_nonneg _) (g0_abs _)
      · norm_num
    _ = _ := by simp

private theorem label_bound {n d : ℕ} (hn : n ≠ 0) (hd : d ∣ n) (X : ℝ) :
    labels X d ≤ n.divisors.card^3 := by
  let D := n.divisors.card
  have card {t : ℕ} (ht : t ∣ n) : t.divisors.card ≤ D :=
    Finset.card_le_card (Nat.divisors_subset_of_dvd hn ht)
  unfold labels
  calc
    _ ≤ ∑ _ ∈ d.divisors, D^2 := by
      apply Finset.sum_le_sum
      intro u hu
      have h₁ := (Nat.div_dvd_of_dvd (Nat.mem_divisors.mp hu).1).trans hd
      calc
        _ ≤ ∑ _ ∈ (d/u).divisors, D := by
          apply Finset.sum_le_sum
          intro v hv
          calc
            _ ≤ ∑ _ ∈ (d/u/v).divisors, 1 := Finset.sum_le_sum (fun w _ => by split_ifs <;> omega)
            _ ≤ D := by simpa using card ((Nat.div_dvd_of_dvd (Nat.mem_divisors.mp hv).1).trans h₁)
        _ ≤ D^2 := by simpa [pow_two] using Nat.mul_le_mul_right D (card h₁)
    _ = d.divisors.card * D^2 := by simp
    _ ≤ D * D^2 := Nat.mul_le_mul_right _ (card hd)
    _ = _ := by change D * D^2 = D^3; ring

theorem K_abs (X : ℝ) {n : ℕ} (hn : 1 < n) : |kernelK X n| ≤ (n.divisors.card:ℝ)^4 := by
  have hsum : |∑ d ∈ n.divisors, mu d * ((labels X d:ℝ)/64^3) *
      (1-(Real.log d)^2/(Real.log n)^2)| ≤ (n.divisors.card:ℝ)^4 := by
    apply (Finset.abs_sum_le_sum_abs ..).trans
    calc
      _ ≤ ∑ _ ∈ n.divisors, (n.divisors.card:ℝ)^3 := by
        apply Finset.sum_le_sum
        intro d hd
        obtain ⟨hdiv,hn₀⟩ := Nat.mem_divisors.mp hd
        have hd₀ := Nat.pos_of_dvd_of_pos hdiv (Nat.zero_lt_of_lt hn)
        have hlog : Real.log d ≤ Real.log n := Real.log_le_log (by exact_mod_cast hd₀) (by exact_mod_cast Nat.le_of_dvd (by omega) hdiv)
        have hnl : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn)
        have hdl := Real.log_natCast_nonneg d
        have hq : 0 ≤ (Real.log d)^2/(Real.log n)^2 := by positivity
        have hu : (Real.log d)^2/(Real.log n)^2 ≤ 1 :=
          (div_le_one (by positivity)).mpr (by nlinarith)
        have hlabel : (labels X d:ℝ) ≤ (n.divisors.card:ℝ)^3 := by exact_mod_cast label_bound hn₀ hdiv X
        rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (labels X d:ℝ)/64^3),
          abs_of_nonneg (sub_nonneg.mpr hu)]
        calc
          _ ≤ (1 * ((n.divisors.card:ℝ)^3)) * 1 := by
            apply mul_le_mul _ (by linarith only [hq]) (sub_nonneg.mpr hu) (by positivity)
            exact mul_le_mul (mu_abs _) ((div_le_self (by positivity : (0:ℝ) ≤ labels X d) (by norm_num : (1:ℝ) ≤ 64^3)).trans hlabel)
              (by positivity) zero_le_one
          _ = _ := by ring
      _ = _ := by simp [pow_succ, mul_comm]
  unfold kernelK
  rw [abs_mul, abs_mul, abs_pow]
  have hμ := pow_le_one₀ (abs_nonneg (mu n)) (mu_abs n) (n:=2)
  have hR : |sieve (markCut X) n| ≤ 1 := by unfold sieve; split_ifs <;> norm_num
  exact (mul_le_of_le_one_left (abs_nonneg _) (mul_le_one₀ hμ (abs_nonneg _) hR)).trans hsum

/-- For squarefree n the sixteen units contributed by every prime to τ(n)^4
are absorbed in p^(1/4) once p≥16^4. The small-prime factor is absolute. -/
theorem divisor_fourth {n : ℕ} (hn : Squarefree n) :
    (n.divisors.card:ℝ)^4 ≤ (16:ℝ)^65536 * (n:ℝ)^(1/4:ℝ) := by
  have hτ : n.divisors.card = 2^n.primeFactors.card := by
    rw [Nat.card_divisors hn.ne_zero]
    calc
      _ = ∏ _ ∈ n.primeFactors, 2 := Finset.prod_congr rfl (fun p hp => by
        rw [Nat.factorization_eq_one_of_squarefree hn (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)])
      _ = _ := by simp
  let S := n.primeFactors.filter (· < 65536)
  have hsub : S ⊆ Finset.range 65536 := fun _ hx => Finset.mem_range.mpr (Finset.mem_filter.mp hx).2
  have hcard : S.card ≤ 65536 := (Finset.card_le_card hsub).trans_eq (Finset.card_range _)
  have pow16 : (65536:ℝ)^(1/4:ℝ) = 16 := by
    rw [show (65536:ℝ) = 16^ (4:ℕ) by norm_num, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 16)]
    norm_num
  have small : (∏ p ∈ n.primeFactors, (if p < 65536 then (16:ℝ) else 1)) = 16^S.card := by
    rw [← Finset.prod_filter]; simp [S]
  calc
    _ = ∏ _ ∈ n.primeFactors, (16:ℝ) := by
      rw [hτ, Nat.cast_pow, Finset.prod_const, ← pow_mul, Nat.mul_comm, pow_mul]
      norm_num
    _ ≤ ∏ p ∈ n.primeFactors, (if p < 65536 then (16:ℝ) else 1) * (p:ℝ)^(1/4:ℝ) := by
      apply Finset.prod_le_prod (by intros; norm_num)
      intro p hp
      by_cases h : p < 65536
      · rw [if_pos h]
        exact le_mul_of_one_le_right (by norm_num) (Real.one_le_rpow (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_le) (by norm_num))
      · rw [if_neg h, one_mul, ← pow16]
        exact Real.rpow_le_rpow (by norm_num) (by exact_mod_cast le_of_not_gt h) (by norm_num)
    _ = 16^S.card * (n:ℝ)^(1/4:ℝ) := by
      rw [Finset.prod_mul_distrib, small, Real.finset_prod_rpow _ (fun p : ℕ => (p:ℝ)) (fun _ _ => Nat.cast_nonneg _) _,
        ← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hn]
    _ ≤ _ := by gcongr; norm_num

def envelope : ℝ := 3 * (16:ℝ)^65536

theorem phi_envelope (x : ℝ) {n : ℕ} (hn : 1 < n) :
    |Direct.phi x n| ≤ envelope * (n:ℝ)^(1/4:ℝ) := by
  have hc : 1 ≤ n.divisors.card := Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr (by omega)⟩
  have hpow : (n.divisors.card:ℝ) ≤ (n.divisors.card:ℝ)^4 := by
    simpa using pow_le_pow_right₀ (by exact_mod_cast hc : 1 ≤ (n.divisors.card:ℝ)) (show 1 ≤ 4 by decide)
  have hH := (H_abs n).trans hpow
  have hK := K_abs (x/2) hn
  by_cases hs : Squarefree n
  · have h := divisor_fourth hs
    have hG : |max (-kernelH n) 0| ≤ (n.divisors.card:ℝ)^4 := by
      rw [abs_of_nonneg (le_max_right _ _)]
      exact max_le ((neg_le_abs _).trans hH) (by positivity)
    have hF := (abs_sub (kernelH n) (kernelK (x/2) n)).trans (add_le_add hH hK)
    have hb : |Direct.phi x n| ≤ 3*(n.divisors.card:ℝ)^4 := by
      apply (abs_sub ..).trans
      unfold Direct.F Direct.G
      split_ifs <;> (try simp only [abs_zero, zero_add, add_zero]) <;>
        linarith only [hF, hG, show (0:ℝ) ≤ (n.divisors.card:ℝ)^4 by positivity]
    exact hb.trans ((mul_le_mul_of_nonneg_left h (by norm_num : (0:ℝ) ≤ 3)).trans_eq
      (mul_assoc _ _ _).symm)
  · have hE : 0 ≤ envelope := by unfold envelope; positivity
    simpa [Direct.phi, Direct.F, Direct.G, hs] using mul_nonneg hE (Real.rpow_nonneg (Nat.cast_nonneg n) (1/4:ℝ))


end
end REAL1B.FM.Analytic
#print axioms REAL1B.FM.Analytic.H_abs
#print axioms REAL1B.FM.Analytic.K_abs
#print axioms REAL1B.FM.Analytic.divisor_fourth
#print axioms REAL1B.FM.Analytic.phi_envelope
