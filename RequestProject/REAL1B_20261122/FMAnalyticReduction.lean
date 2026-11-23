import RequestProject.REAL1B_20261122.FMPrimePower

/-! Gold 4.58 (U3)–(U5) on a specified output profile. The comparator and
short product have separate estimates; the nonsquarefree error is absolute. -/
namespace REAL1B.FM.Analytic
open Filter Vaughan Source Closing ArithmeticFunction
noncomputable section
open Classical

def lambdaSum (z x : ℝ) (f : ℕ → ℝ) := total (x/2) (fun n => sieve z (n-2) * lam (n-2) * f n)
def primeSum (x : ℝ) (f : ℕ → ℝ) := total (x/2) (fun n => theta (n-2) * f n)
def intrinsicCut (x : ℝ) := x^(1/800000000000:ℝ)
def SmallCut (z : ℝ → ℝ) : Prop := ∀ᶠ x : ℝ in atTop, ∀ n ∈ interval (x/2), z x < (n-2:ℕ)

private theorem small_sqrt : SmallCut Real.sqrt := by
  filter_upwards [eventually_ge_atTop (36:ℝ)] with x hx n hn
  obtain ⟨hn',_,h₂⟩ := window hn
  rw [Nat.cast_sub h₂, Nat.cast_ofNat]
  nlinarith only [hx,hn',Real.sq_sqrt (by linarith : 0 ≤ x),sq_nonneg (Real.sqrt x-2)]

theorem small_power {s : ℝ} (hs : s ≤ 1/2) : SmallCut (fun x : ℝ => x^s) := by
  filter_upwards [small_sqrt, eventually_ge_atTop (1:ℝ)] with x h hx n hn
  rw [Real.sqrt_eq_rpow] at h
  exact (Real.rpow_le_rpow_of_exponent_le hx hs).trans_lt (h n hn)

theorem small_roughW {a : ℝ} (ha : a < 1) : SmallCut (roughW a) := by
  filter_upwards [small_sqrt, log_power_lt_linear (a:=a) (b:=1/2) ha (by norm_num),
    eventually_gt_atTop (1:ℝ)] with x h hlog hx n hn
  calc
    roughW a x < Real.exp (Real.log x * (1/2)) := Real.exp_lt_exp.mpr (by linarith)
    _ = Real.sqrt x := by rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by linarith : 0 < x)]
    _ < _ := h n hn

private theorem sieve_prime {p : ℕ} (hp : p.Prime) {z : ℝ} (hz : z < p) : sieve z p = 1 := by
  apply if_pos
  intro q hq hd
  exact (Nat.prime_dvd_prime_iff_eq hq hp).mp hd ▸ hz

theorem lambda_prime_error {x z : ℝ} {f : ℝ → ℕ → ℝ}
    (hz : ∀ n ∈ interval (x/2), z < (n-2:ℕ)) :
    |lambdaSum z x (f x) - primeSum x (f x)| ≤ powerMass f x := by
  unfold lambdaSum primeSum powerMass total
  rw [← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs ..).trans
  apply Finset.sum_le_sum
  intro n hn
  by_cases hp : (n-2).Prime
  · simp [sieve_prime hp (hz n hn),lam,theta,hp,vonMangoldt_apply_prime hp]
  · simp only [theta,if_neg hp,zero_mul,sub_zero,abs_mul]
    have hL : 0 ≤ lam (n-2) := vonMangoldt_nonneg
    rw [abs_of_nonneg hL]
    unfold sieve
    split_ifs <;> simp [mul_nonneg hL (abs_nonneg _)]

theorem prime_replacement {z : ℝ → ℝ} (hz : SmallCut z) {f : ℝ → ℕ → ℝ}
    (hf : negligible (powerMass f) scale) :
    negligible (fun x => lambdaSum (z x) x (f x) - primeSum x (f x)) scale := by
  intro e he
  filter_upwards [hz,hf e he] with x h hh
  exact (lambda_prime_error h).trans ((le_abs_self _).trans hh)

theorem native_presieve {a : ℝ} (ha : a < 1) :
    negligible (fun x => lambdaSum (intrinsicCut x) x (Direct.phi x) -
      lambdaSum (roughW a x) x (Direct.phi x)) scale := by
  intro e he
  have hε : 0 < e/2 := by linarith
  have h₁ := prime_replacement (small_power (by norm_num : (1/800000000000:ℝ) ≤ 1/2)) native_power_mass
  have h₂ := prime_replacement (small_roughW ha) native_power_mass
  filter_upwards [h₁ _ hε,h₂ _ hε] with x h₁ h₂
  apply abs_le.mpr
  change |lambdaSum (intrinsicCut x) x _ - primeSum x _| ≤ _ at h₁
  constructor <;> linarith only [(abs_le.mp h₁).1,(abs_le.mp h₁).2,(abs_le.mp h₂).1,(abs_le.mp h₂).2]

def shortCoeff (u D : ℝ) (k : ℕ) := ∑ l ∈ k.divisors, if l.Prime ∧ u < (l:ℝ) then
  Real.log l * ∑ m ∈ (k/l).divisors, if u < (m:ℝ) ∧ (m*l:ℕ) ≤ D then mu m else 0 else 0

private theorem coeffII_rows (u : ℝ) (k : ℕ) : coeffII u u k =
    ∑ l ∈ k.divisors, (if u < (l:ℝ) then lam l else 0) *
      ∑ m ∈ (k/l).divisors, if u < (m:ℝ) then mu m else 0 := by
  have h : coeffII u u = high u lam * (high u mob * zetaR) := by unfold coeffII cV; ac_rfl
  rw [h, ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal (fun l r => high u lam l * (high u mob * zetaR) r)]
  apply Finset.sum_congr rfl
  intro l _
  simp only [high_apply, zetaR, coe_mul_zeta_apply]
  rfl

theorem squarefree_owner_split {k : ℕ} (hk : Squarefree k) (u D : ℝ) :
    coeffII u u k = shortCoeff u D k + coeff u D k := by
  rw [coeffII_rows,shortCoeff,coeff,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro l hl
  by_cases hp : l.Prime
  · by_cases hu : u < (l:ℝ)
    · simp only [hu,hp,and_self,if_true,primeRow,lam,vonMangoldt_apply_prime hp,← mul_add,← Finset.sum_add_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro m _
      push_cast
      by_cases h : u < (m:ℝ) <;> by_cases hd : D < (m:ℝ)*l <;> simp [h,hd,le_of_not_gt,not_le.mpr]
    · simp [hu,hp]
  · have hsf := hk.squarefree_of_dvd (Nat.mem_divisors.mp hl).1
    have hL : lam l = 0 := vonMangoldt_eq_zero_iff.mpr (fun h =>
      hp (Nat.squarefree_and_prime_pow_iff_prime.mp ⟨hsf,h⟩))
    simp [hp,hL]

theorem coeffII_abs (u : ℝ) {k : ℕ} (hk : 0 < k) :
    |coeffII u u k| ≤ k.divisors.card * Real.log k := by
  rw [coeffII, ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal (fun m r => high u mob m * cV u r)]
  apply (Finset.abs_sum_le_sum_abs ..).trans
  calc
    _ ≤ ∑ _ ∈ k.divisors, Real.log k := by
      apply Finset.sum_le_sum
      intro m hm
      have hq := Nat.div_pos (Nat.le_of_dvd hk (Nat.mem_divisors.mp hm).1) (Nat.pos_of_mem_divisors hm)
      have hL : 0 ≤ cV u (k/m) := by rw [cV_divisors]; exact Finset.sum_nonneg (fun i _ => by
        split_ifs <;> first | exact vonMangoldt_nonneg | rfl)
      have hle : cV u (k/m) ≤ Real.log (k/m:ℕ) := by
        rw [cV_divisors,← vonMangoldt_sum]
        apply Finset.sum_le_sum
        intro p _
        split_ifs <;> first | exact le_refl _ | exact vonMangoldt_nonneg
      have hmu : |high u mob m| ≤ 1 := by
        rw [high_apply]; split_ifs
        · change |mu m| ≤ 1
          unfold mu
          exact_mod_cast abs_moebius_le_one (n:=m)
        · norm_num
      rw [abs_mul,abs_of_nonneg hL]
      exact (mul_le_of_le_one_left hL hmu).trans (hle.trans (Real.log_le_log
        (by exact_mod_cast hq) (by exact_mod_cast Nat.div_le_self k m)))
    _ = _ := by simp

theorem mu_sq {k : ℕ} (hk : Squarefree k) : mu k ^ 2 = 1 := by
  unfold mu
  exact_mod_cast moebius_sq_eq_one_of_squarefree hk

theorem shortCoeff_abs (u D : ℝ) {k : ℕ} (hk : 0 < k) :
    |shortCoeff u D k| ≤ k.divisors.card * Real.log k := by
  unfold shortCoeff
  apply (Finset.abs_sum_le_sum_abs ..).trans
  rw [← vonMangoldt_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro l hl
  split_ifs with h
  · obtain ⟨hp,_⟩ := h
    rw [vonMangoldt_apply_prime hp,abs_mul,abs_of_nonneg (Real.log_natCast_nonneg _),mul_comm]
    apply mul_le_mul_of_nonneg_right _ (Real.log_natCast_nonneg _)
    apply (Finset.abs_sum_le_sum_abs ..).trans
    calc
      _ ≤ ∑ _ ∈ (k/l).divisors, (1:ℝ) := Finset.sum_le_sum (fun m _ => by
        split_ifs
        · unfold mu
          exact_mod_cast abs_moebius_le_one (n:=m)
        · norm_num)
      _ ≤ _ := by
        simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
        exact_mod_cast Finset.card_le_card (Nat.divisors_subset_of_dvd hk.ne' (Nat.div_dvd_of_dvd (Nat.mem_divisors.mp hl).1))
  · rw [abs_zero]
    exact mul_nonneg (by positivity) vonMangoldt_nonneg

def weightedInput (a x : ℝ) (f : ℕ → ℝ) (c : ℕ → ℝ) := total (x/2) (fun n =>
  sieve (roughW a x) (n-2) * c (n-2) * f n)
def typeI (a x : ℝ) (f : ℕ → ℝ) := weightedInput a x f (coeffI (cutU x) (cutU x))
def shortProduct (a x : ℝ) (f : ℕ → ℝ) := weightedInput a x f (shortCoeff (cutU x) (cutD x))
def squarefulMass (a x : ℝ) (f : ℕ → ℝ) := weightedInput a x (fun n => |f n|) (fun k =>
  if Squarefree k then 0 else 2 * k.divisors.card * Real.log k)

/-- Finite (U4)–(U5), valid for signed profiles, with every discarded input charged absolutely. -/
theorem physical_vaughan (a x : ℝ) (f : ℕ → ℝ)
    (hcut : ∀ n ∈ interval (x/2), cutU x < (n-2:ℕ))
    (hpos : ∀ n ∈ interval (x/2), 0 < n-2) :
    |lambdaSum (roughW a x) x f - typeI a x f - shortProduct a x f - Direct.largeSum a x f| ≤
      squarefulMass a x f := by
  unfold lambdaSum typeI shortProduct Direct.largeSum squarefulMass weightedInput total
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs ..).trans
  apply Finset.sum_le_sum
  intro n hn
  let k := n-2
  have hv := DFunLike.congr_fun (vaughan_identity (cutU x) (cutU x)) k
  have hlam : lam k = coeffI (cutU x) (cutU x) k + coeffII (cutU x) (cutU x) k := by
    simpa [low,not_le.mpr (hcut n hn),k] using hv
  change |sieve _ k * lam k * f n - _ - _ - _| ≤ _
  rw [hlam]
  by_cases hs : Squarefree k
  · simp only [show n-2=k from rfl,hs,if_true,mu_sq hs,squarefree_owner_split hs (cutU x) (cutD x),mul_one,mul_zero,zero_mul]
    ring_nf
    simp
  · have hμ : mu k = 0 := by simp [mu,moebius_eq_zero_of_not_squarefree hs]
    simp only [show n-2=k from rfl,hs,if_false,hμ,zero_pow (by decide : 2 ≠ 0),mul_zero,zero_mul,sub_zero]
    rw [show sieve (roughW a x) k * (_ + _) * f n - _ - _ =
      sieve (roughW a x) k * (coeffII (cutU x) (cutU x) k - shortCoeff (cutU x) (cutD x) k) * f n by ring,
      abs_mul,abs_mul,abs_of_nonneg (show 0 ≤ sieve (roughW a x) k by unfold sieve; split_ifs <;> norm_num)]
    apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
    apply mul_le_mul_of_nonneg_left _ (by unfold sieve; split_ifs <;> norm_num)
    linarith only [abs_sub (coeffII (cutU x) (cutU x) k) (shortCoeff (cutU x) (cutD x) k),
      coeffII_abs (cutU x) (hpos n hn),shortCoeff_abs (cutU x) (cutD x) (hpos n hn)]

end
end REAL1B.FM.Analytic
#print axioms REAL1B.FM.Analytic.native_presieve
#print axioms REAL1B.FM.Analytic.prime_replacement
#print axioms REAL1B.FM.Analytic.squarefree_owner_split
#print axioms REAL1B.FM.Analytic.coeffII_abs
#print axioms REAL1B.FM.Analytic.shortCoeff_abs
#print axioms REAL1B.FM.Analytic.physical_vaughan
