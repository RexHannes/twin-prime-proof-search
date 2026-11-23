import RequestProject.REAL1B_20261122.FMLowerLedger

/-! The growing odd-prime presieve in Gold 4.58 B1/B3. The truncation is taken
on the actual divisors of each input before the signed coefficients are summed. -/
namespace REAL1B.FM.Presieve
open Source Vaughan Analytic Finset
noncomputable section
open Classical

def smallOdds (w : ℝ) (k : ℕ) : Finset ℕ := k.primeFactors.filter (fun p : ℕ => p ≠ 2 ∧ (p:ℝ) ≤ w)

def alternating (R : ℕ) (P : Finset ℕ) : ℝ :=
  ∑ i ∈ range (R+1), (-1:ℝ)^i * (P.powersetCard i).card

theorem truncation (w : ℝ) {k : ℕ} (hk : k ≠ 0) (hodd : ¬2 ∣ k) (R : ℕ) :
    |sieve w k - alternating R (smallOdds w k)| ≤ ((smallOdds w k).powersetCard (R+1)).card := by
  let P := smallOdds w k
  have hz : Sifted w k ↔ P.card = 0 := by
    rw [card_eq_zero]
    constructor
    · intro hs; apply eq_empty_iff_forall_notMem.mpr; intro p hp
      obtain ⟨hd,_,h⟩ := mem_filter.mp hp
      exact (not_le.mpr (hs p (Nat.prime_of_mem_primeFactors hd) (Nat.dvd_of_mem_primeFactors hd))) h
    · intro he p hp hd
      apply lt_of_not_ge; intro h
      have hh : p ∈ P := mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hp,hd,hk⟩,fun h₂ => hodd (h₂ ▸ hd),h⟩
      simp [he] at hh
  change |sieve w k-alternating R P| ≤ _
  simp only [sieve,hz,alternating,card_powersetCard]
  change |(if P.card=0 then 1 else 0) - ∑ i ∈ range (R+1), (-1:ℝ)^i*P.card.choose i| ≤ P.card.choose (R+1)
  cases hsize : P.card with
  | zero =>
    simp [Finset.sum_range_succ']
  | succ j =>
    have hsum : (∑ i ∈ range (R+1), (-1:ℝ)^i*(j+1).choose i) = (-1:ℝ)^R*j.choose R := by
      exact_mod_cast (Int.alternating_sum_range_choose_eq_choose (n:=j) (m:=R))
    rw [if_neg (by omega),zero_sub,abs_neg,hsum,abs_mul,abs_pow]
    simp [Nat.choose_succ_succ]

/-- Native Φ and its boxed part keep every odd input divisor. This bound also
applies verbatim to each signed Vaughan coefficient, including the short block. -/
theorem weighted_truncation {a x : ℝ} (R : ℕ) (f c : ℕ → ℝ)
    (hodd : ∀ n ∈ interval (x/2), f n ≠ 0 → n-2 ≠ 0 ∧ ¬2 ∣ (n-2)) :
    |weightedInput a x f c - total (x/2) (fun n => alternating R (smallOdds (Closing.roughW a x) (n-2))*c (n-2)*f n)| ≤
    total (x/2) (fun n => (((smallOdds (Closing.roughW a x) (n-2)).powersetCard (R+1)).card:ℝ)*|c (n-2)| * |f n|) := by
  unfold weightedInput total
  rw [← sum_sub_distrib]
  apply (abs_sum_le_sum_abs ..).trans
  apply sum_le_sum
  intro n hn
  by_cases hf : f n=0
  · simp [hf]
  · obtain ⟨hk,ho⟩ := hodd n hn hf
    rw [← sub_mul,← sub_mul,abs_mul,abs_mul]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (truncation _ hk ho R) (abs_nonneg _)) (abs_nonneg _)

def Smooth (w : ℝ) (q : ℕ) := ∀ p, p.Prime → p ∣ q → (p:ℝ) ≤ w

theorem fold_injective {w : ℝ} {e q e' q' : ℕ} (he : e ≠ 0)
    (hre : Sifted w e) (hrf : Sifted w e') (hq : Smooth w q) (hr : Smooth w q')
    (h : e*q = e'*q') : e=e' ∧ q=q' := by
  have cop {u v : ℕ} (hu : Sifted w u) (hv : Smooth w v) : u.Coprime v := by
    by_contra hn
    obtain ⟨p,hp,hd⟩ := Nat.exists_prime_and_dvd (show u.gcd v ≠ 1 from hn)
    exact (not_le.mpr (hu p hp (hd.trans (Nat.gcd_dvd_left _ _)))) (hv p hp (hd.trans (Nat.gcd_dvd_right _ _)))
  have h₁ : e ∣ e' := (cop hre hr).dvd_of_dvd_mul_right (h ▸ dvd_mul_right e q)
  have h₂ : e' ∣ e := (cop hrf hq).dvd_of_dvd_mul_right (h.symm ▸ dvd_mul_right e' q')
  obtain rfl := Nat.dvd_antisymm h₁ h₂
  exact ⟨rfl,Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero he) h⟩


def oddInputs (x : ℝ) (f : ℕ → ℝ) : Prop := ∀ n ∈ interval (x/2),
  f n ≠ 0 → n-2 ≠ 0 ∧ ¬ 2 ∣ (n-2)

theorem native_odd : ∀ᶠ x : ℝ in Filter.atTop, oddInputs x (Direct.phi x) ∧ oddInputs x (Direct.psi x) := by
  have hy := Real.tendsto_exp_atTop.comp ((tendsto_rpow_atTop (by norm_num : 0<(1/20:ℝ))).comp Real.tendsto_log_atTop)
  filter_upwards [Ledger.output_support Ledger.geometry,hy.eventually_ge_atTop 2,Filter.eventually_ge_atTop (8:ℝ)] with x hout hy hx
  have hphi : oddInputs x (Direct.phi x) := by
    intro n hn hne
    have hh := (window hn).1
    have hnum : 4<n := by exact_mod_cast (show (4:ℝ)<n by linarith)
    have hodd : ¬ 2 ∣ n := fun hd => (not_lt.mpr (show 2 ≤ y x from hy)) (hout n hn hne 2 Nat.prime_two hd)
    omega
  refine ⟨hphi,?_⟩
  intro n hn hne
  apply hphi n hn
  exact fun h => hne (by simp [Direct.psi,h])

theorem native_truncation {a : ℝ} : ∀ᶠ x : ℝ in Filter.atTop,
    ∀ f ∈ [Direct.phi x, Direct.psi x], ∀ (R : ℕ) (c : ℕ → ℝ),
    |weightedInput a x f c - total (x/2) (fun n => alternating R (smallOdds (Closing.roughW a x) (n-2))*c (n-2)*f n)| ≤
    total (x/2) (fun n => (((smallOdds (Closing.roughW a x) (n-2)).powersetCard (R+1)).card:ℝ)*|c (n-2)| * |f n|) := by
  filter_upwards [native_odd] with x ho f hf R c
  apply weighted_truncation R f c
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
  rcases hf with rfl | rfl
  · exact ho.1
  · exact ho.2

end
end REAL1B.FM.Presieve
#print axioms REAL1B.FM.Presieve.truncation
#print axioms REAL1B.FM.Presieve.weighted_truncation
#print axioms REAL1B.FM.Presieve.fold_injective
#print axioms REAL1B.FM.Presieve.native_truncation
