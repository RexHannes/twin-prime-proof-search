import Mathlib

/-!
# Rankin's radical estimate, proved unconditionally

`∑_{n ≤ T} 1/rad(n) ≪_ε T^ε` (Rankin's trick), with a fully explicit
constant `exp(∑_{n ≥ 2} 1/(n(n^ε−1)))`.  The proof is the classical one:
the Rankin-twisted density `f_ε(n) = 1/(rad(n) n^ε)` is multiplicative, its
Euler factors are `1 + 1/(p(p^ε−1))`, and the partial sums over `N`-smooth
numbers are bounded by the corresponding finite Euler product, uniformly in `N`.

Nothing here is conditional on an external analytic input.
-/

namespace ShiftedMobiusBank

open Finset


/-- The radical (squarefree kernel) `rad n = ∏_{p ∣ n} p`. -/
def radNat (n : ℕ) : ℕ := ∏ p ∈ n.primeFactors, p

lemma radNat_pos (n : ℕ) : 0 < radNat n :=
  Finset.prod_pos (fun _ hp => (Nat.prime_of_mem_primeFactors hp).pos)

@[simp] lemma radNat_one : radNat 1 = 1 := by simp [radNat]

lemma radNat_mul_of_coprime {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (h : Nat.Coprime m n) :
    radNat (m * n) = radNat m * radNat n := by
  unfold radNat
  rw [Nat.primeFactors_mul hm hn, Finset.prod_union h.disjoint_primeFactors]

lemma radNat_prime_pow {p a : ℕ} (hp : p.Prime) (ha : a ≠ 0) : radNat (p ^ a) = p := by
  unfold radNat
  rw [Nat.primeFactors_prime_pow ha hp, Finset.prod_singleton]

/-- `f_ε(n) = 1/(rad(n) · n^ε)`, the Rankin-twisted radical density. -/
noncomputable def rankinF (ε : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else 1 / ((radNat n : ℝ) * (n : ℝ) ^ ε)

lemma rankinF_nonneg (ε : ℝ) (n : ℕ) : 0 ≤ rankinF ε n := by
  unfold rankinF
  split
  · exact le_rfl
  · positivity

@[simp] lemma rankinF_zero (ε : ℝ) : rankinF ε 0 = 0 := by simp [rankinF]

@[simp] lemma rankinF_one (ε : ℝ) : rankinF ε 1 = 1 := by simp [rankinF]

lemma rankinF_mul {ε : ℝ} {m n : ℕ} (h : Nat.Coprime m n) :
    rankinF ε (m * n) = rankinF ε m * rankinF ε n := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  have hmn : m * n ≠ 0 := Nat.mul_ne_zero hm hn
  unfold rankinF
  rw [if_neg hm, if_neg hn, if_neg hmn, radNat_mul_of_coprime hm hn h]
  push_cast
  rw [Real.mul_rpow (by positivity) (by positivity)]
  field_simp

lemma rankinF_prime_pow {ε : ℝ} {p : ℕ} (hp : p.Prime) (a : ℕ) :
    rankinF ε (p ^ a) =
      (1 / (p:ℝ)) * (1 / ((p:ℝ) ^ ε)) ^ a + (if a = 0 then 1 - 1 / (p:ℝ) else 0) := by
  have hp0 : (0:ℝ) < (p:ℝ) := by exact_mod_cast hp.pos
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  have hpa : (p:ℝ) ^ ε ≠ 0 := by positivity
  have h1 : rankinF ε (p ^ a) = 1 / ((p:ℝ) * ((p:ℝ) ^ ε) ^ a) := by
    unfold rankinF
    rw [if_neg (pow_ne_zero a hp.pos.ne'), radNat_prime_pow hp ha]
    congr 1
    push_cast
    rw [← Real.rpow_natCast (p:ℝ) a, ← Real.rpow_mul hp0.le, mul_comm (a:ℝ) ε,
      Real.rpow_mul hp0.le, Real.rpow_natCast]
  rw [h1, if_neg ha, add_zero, div_pow, one_pow, one_div_mul_one_div]


lemma one_lt_rpow_prime {ε : ℝ} (hε : 0 < ε) {p : ℕ} (hp : p.Prime) : (1:ℝ) < (p:ℝ) ^ ε := by
  have h : (1:ℝ) < (p:ℝ) := by exact_mod_cast hp.one_lt
  exact (Real.one_lt_rpow_iff_of_pos (by linarith)).mpr (Or.inl ⟨h, hε⟩)

lemma rankinF_prime_pow_summable {ε : ℝ} (hε : 0 < ε) {p : ℕ} (hp : p.Prime) :
    Summable (fun a : ℕ => ‖rankinF ε (p ^ a)‖) := by
  have hs : (1:ℝ) < (p:ℝ) ^ ε := one_lt_rpow_prime hε hp
  have hr0 : (0:ℝ) ≤ 1 / ((p:ℝ) ^ ε) := by positivity
  have hr1 : 1 / ((p:ℝ) ^ ε) < 1 := by
    rw [div_lt_one (by linarith)]; linarith
  have hsum : Summable (fun a : ℕ =>
      (1 / (p:ℝ)) * (1 / ((p:ℝ) ^ ε)) ^ a + (if a = 0 then 1 - 1 / (p:ℝ) else 0)) :=
    ((summable_geometric_of_lt_one hr0 hr1).mul_left _).add
      (hasSum_ite_eq (0:ℕ) (1 - 1 / (p:ℝ))).summable
  have heq : ∀ a : ℕ, ‖rankinF ε (p ^ a)‖ =
      (1 / (p:ℝ)) * (1 / ((p:ℝ) ^ ε)) ^ a + (if a = 0 then 1 - 1 / (p:ℝ) else 0) := by
    intro a
    rw [Real.norm_of_nonneg (rankinF_nonneg ε _), rankinF_prime_pow hp a]
  exact hsum.congr (fun a => (heq a).symm)

lemma rankinF_prime_pow_tsum {ε : ℝ} (hε : 0 < ε) {p : ℕ} (hp : p.Prime) :
    ∑' a : ℕ, rankinF ε (p ^ a) = 1 + 1 / ((p:ℝ) * ((p:ℝ) ^ ε - 1)) := by
  have hp0 : (0:ℝ) < (p:ℝ) := by exact_mod_cast hp.pos
  have hs : (1:ℝ) < (p:ℝ) ^ ε := one_lt_rpow_prime hε hp
  have hr0 : (0:ℝ) ≤ 1 / ((p:ℝ) ^ ε) := by positivity
  have hr1 : 1 / ((p:ℝ) ^ ε) < 1 := by
    rw [div_lt_one (by linarith)]; linarith
  have hgeo : Summable (fun a : ℕ => (1 / (p:ℝ)) * (1 / ((p:ℝ) ^ ε)) ^ a) :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left _
  have hind : Summable (fun a : ℕ => (if a = 0 then 1 - 1 / (p:ℝ) else 0)) :=
    (hasSum_ite_eq (0:ℕ) (1 - 1 / (p:ℝ))).summable
  have hcongr : ∑' a : ℕ, rankinF ε (p ^ a)
      = ∑' a : ℕ, ((1 / (p:ℝ)) * (1 / ((p:ℝ) ^ ε)) ^ a + (if a = 0 then 1 - 1 / (p:ℝ) else 0)) :=
    tsum_congr (fun a => rankinF_prime_pow hp a)
  rw [hcongr, hgeo.tsum_add hind, tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1,
    tsum_ite_eq]
  have hne : (1:ℝ) - 1 / ((p:ℝ) ^ ε) ≠ 0 := by
    have : 1 / ((p:ℝ) ^ ε) < 1 := hr1
    linarith
  have hsne : (p:ℝ) ^ ε - 1 ≠ 0 := by linarith
  field_simp
  ring



noncomputable def cser (ε : ℝ) (n : ℕ) : ℝ :=
  if 2 ≤ n then 1 / ((n:ℝ) * ((n:ℝ) ^ ε - 1)) else 0

lemma two_le_rpow {ε : ℝ} (hε : 0 < ε) {n : ℕ} (hn : ⌈(2:ℝ) ^ (1/ε)⌉₊ ≤ n) :
    (2:ℝ) ≤ (n:ℝ) ^ ε := by
  have h1 : (2:ℝ) ^ (1/ε) ≤ (n:ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hn)
  have h2 : ((2:ℝ) ^ (1/ε)) ^ ε ≤ (n:ℝ) ^ ε :=
    Real.rpow_le_rpow (by positivity) h1 hε.le
  rwa [← Real.rpow_mul (by norm_num), one_div, inv_mul_cancel₀ (ne_of_gt hε), Real.rpow_one] at h2

lemma one_lt_rpow_nat {ε : ℝ} (hε : 0 < ε) {n : ℕ} (hn : 2 ≤ n) : (1:ℝ) < (n:ℝ) ^ ε := by
  have h1 : (1:ℝ) < (n:ℝ) := by exact_mod_cast hn
  exact (Real.one_lt_rpow_iff_of_pos (by linarith)).mpr (Or.inl ⟨h1, hε⟩)

lemma cser_nonneg {ε : ℝ} (hε : 0 < ε) (n : ℕ) : 0 ≤ cser ε n := by
  unfold cser
  split_ifs with h
  · have h2 : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast h
    have hg := one_lt_rpow_nat hε h
    have hpos : (0:ℝ) < (n:ℝ) * ((n:ℝ) ^ ε - 1) := by nlinarith
    exact le_of_lt (one_div_pos.mpr hpos)
  · exact le_rfl

lemma cser_summable {ε : ℝ} (hε : 0 < ε) : Summable (cser ε) := by
  obtain ⟨n0, hn0a, hn0b⟩ : ∃ n0 : ℕ, 2 ≤ n0 ∧ ⌈(2:ℝ) ^ (1/ε)⌉₊ ≤ n0 :=
    ⟨max 2 (⌈(2:ℝ) ^ (1/ε)⌉₊), le_max_left _ _, le_max_right _ _⟩
  rw [← summable_nat_add_iff n0]
  have hbase : Summable (fun n : ℕ => 1 / (n:ℝ) ^ (1 + ε)) :=
    Real.summable_one_div_nat_rpow.mpr (by linarith)
  have hcomp : Summable (fun n : ℕ => 2 * (1 / (((n + n0 : ℕ)):ℝ) ^ (1 + ε))) :=
    Summable.mul_left 2 ((summable_nat_add_iff n0).mpr hbase)
  refine Summable.of_nonneg_of_le (fun n => cser_nonneg hε _) (fun n => ?_) hcomp
  have hge : ⌈(2:ℝ) ^ (1/ε)⌉₊ ≤ n + n0 := le_trans hn0b (Nat.le_add_left _ _)
  have h2 : (2:ℝ) ≤ ((n + n0 : ℕ):ℝ) ^ ε := two_le_rpow hε hge
  have hn2 : 2 ≤ n + n0 := le_trans hn0a (Nat.le_add_left _ _)
  have hx : (2:ℝ) ≤ ((n + n0 : ℕ):ℝ) := by exact_mod_cast hn2
  have hx0 : (0:ℝ) < ((n + n0 : ℕ):ℝ) := by linarith
  unfold cser
  rw [if_pos hn2]
  have hsplit : ((n + n0 : ℕ):ℝ) ^ (1 + ε) = ((n + n0 : ℕ):ℝ) * ((n + n0 : ℕ):ℝ) ^ ε := by
    rw [Real.rpow_add hx0, Real.rpow_one]
  rw [hsplit, mul_one_div, div_le_div_iff₀ (by nlinarith) (by positivity)]
  nlinarith [Real.rpow_nonneg hx0.le ε]

/-- The Rankin constant `C(ε) = exp(∑_{n≥2} 1/(n(n^ε−1)))`. -/
noncomputable def rankinConst (ε : ℝ) : ℝ := Real.exp (∑' n : ℕ, cser ε n)

lemma one_le_rankinConst {ε : ℝ} (hε : 0 < ε) : 1 ≤ rankinConst ε := by
  unfold rankinConst
  exact Real.one_le_exp (tsum_nonneg (fun n => cser_nonneg hε n))

/-- The finite Euler product over primes below `N` is bounded, uniformly in `N`,
by the Rankin constant. -/
lemma prod_euler_factors_le {ε : ℝ} (hε : 0 < ε) (N : ℕ) :
    ∏ p ∈ N.primesBelow, (1 + 1 / ((p:ℝ) * ((p:ℝ) ^ ε - 1))) ≤ rankinConst ε := by
  have hfac : ∀ p ∈ N.primesBelow,
      (1 + 1 / ((p:ℝ) * ((p:ℝ) ^ ε - 1))) ≤ Real.exp (cser ε p) := by
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primesBelow hp
    have hp2 : 2 ≤ p := hpp.two_le
    have : cser ε p = 1 / ((p:ℝ) * ((p:ℝ) ^ ε - 1)) := by
      unfold cser; rw [if_pos hp2]
    rw [this]
    have := Real.add_one_le_exp (1 / ((p:ℝ) * ((p:ℝ) ^ ε - 1)))
    linarith
  have hnonneg : ∀ p ∈ N.primesBelow, (0:ℝ) ≤ 1 + 1 / ((p:ℝ) * ((p:ℝ) ^ ε - 1)) := by
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primesBelow hp
    have hc : cser ε p = 1 / ((p:ℝ) * ((p:ℝ) ^ ε - 1)) := by
      unfold cser; rw [if_pos hpp.two_le]
    have := cser_nonneg hε p
    rw [hc] at this
    linarith
  have hstep : ∏ p ∈ N.primesBelow, (1 + 1 / ((p:ℝ) * ((p:ℝ) ^ ε - 1)))
      ≤ ∏ p ∈ N.primesBelow, Real.exp (cser ε p) :=
    Finset.prod_le_prod hnonneg hfac
  have hexp : ∏ p ∈ N.primesBelow, Real.exp (cser ε p)
      = Real.exp (∑ p ∈ N.primesBelow, cser ε p) := (Real.exp_sum _ _).symm
  have hsub : N.primesBelow ⊆ Finset.range N := by
    intro p hp
    exact Finset.mem_range.mpr (Nat.lt_of_mem_primesBelow hp)
  have hsum1 : ∑ p ∈ N.primesBelow, cser ε p ≤ ∑ n ∈ Finset.range N, cser ε n :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => cser_nonneg hε n)
  have hsum2 : ∑ n ∈ Finset.range N, cser ε n ≤ ∑' n : ℕ, cser ε n :=
    (cser_summable hε).sum_le_tsum _ (fun n _ => cser_nonneg hε n)
  calc ∏ p ∈ N.primesBelow, (1 + 1 / ((p:ℝ) * ((p:ℝ) ^ ε - 1)))
      ≤ Real.exp (∑ p ∈ N.primesBelow, cser ε p) := by rw [← hexp]; exact hstep
    _ ≤ rankinConst ε := by
        unfold rankinConst
        exact Real.exp_le_exp.mpr (le_trans hsum1 hsum2)

/-- Uniform bound for the partial sums of the Rankin-twisted density. -/
lemma rankinF_partial_sum_le {ε : ℝ} (hε : 0 < ε) (N : ℕ) :
    ∑ n ∈ Finset.range N, rankinF ε n ≤ rankinConst ε := by
  classical
  obtain ⟨-, hHasSum⟩ :=
    EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum
      (f := rankinF ε) (rankinF_one ε) (fun {m n} h => rankinF_mul h)
      (fun {p} hp => rankinF_prime_pow_summable hε hp) N
  have hprod : (∏ p ∈ N.primesBelow, ∑' a : ℕ, rankinF ε (p ^ a))
      = ∏ p ∈ N.primesBelow, (1 + 1 / ((p:ℝ) * ((p:ℝ) ^ ε - 1))) :=
    Finset.prod_congr rfl (fun p hp =>
      rankinF_prime_pow_tsum hε (Nat.prime_of_mem_primesBelow hp))
  rw [hprod] at hHasSum
  set s : Finset N.smoothNumbers :=
    Finset.subtype (fun n => n ∈ N.smoothNumbers) (Finset.range N) with hs
  have hle : ∑ x ∈ s, rankinF ε (x : ℕ)
      ≤ ∏ p ∈ N.primesBelow, (1 + 1 / ((p:ℝ) * ((p:ℝ) ^ ε - 1))) :=
    sum_le_hasSum s (fun i _ => rankinF_nonneg ε _) hHasSum
  have hsum_eq : ∑ x ∈ s, rankinF ε (x : ℕ) = ∑ n ∈ Finset.range N, rankinF ε n := by
    rw [hs, Finset.sum_subtype_eq_sum_filter]
    refine Finset.sum_subset (Finset.filter_subset _ _) (fun n hn hnot => ?_)
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · exact rankinF_zero ε
    · exact absurd (Finset.mem_filter.mpr
        ⟨hn, Nat.mem_smoothNumbers_of_lt hpos (Finset.mem_range.mp hn)⟩) hnot
  rw [hsum_eq] at hle
  exact le_trans hle (prod_euler_factors_le hε N)

/-- **Rankin's radical estimate, unconditional.**  For every `ε > 0`,
`∑_{1 ≤ n ≤ T} 1/rad(n) ≤ C(ε) · T^ε` for all `T`, with the explicit constant
`C(ε) = exp(∑_{n ≥ 2} 1/(n(n^ε − 1))) ≥ 1`. -/
theorem sum_one_div_radical_le (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ T : ℕ,
      ∑ n ∈ Finset.Icc 1 T, 1 / (radNat n : ℝ) ≤ C * (T:ℝ) ^ ε := by
  refine ⟨rankinConst ε, one_le_rankinConst hε, fun T => ?_⟩
  rcases Nat.eq_zero_or_pos T with rfl | hT
  · simp only [Nat.cast_zero]
    rw [Real.zero_rpow (ne_of_gt hε), mul_zero]
    simp
  have hT0 : (0:ℝ) < (T:ℝ) := by exact_mod_cast hT
  have hpt : ∀ n ∈ Finset.Icc 1 T,
      1 / (radNat n : ℝ) ≤ (T:ℝ) ^ ε * rankinF ε n := by
    intro n hn
    rcases Finset.mem_Icc.mp hn with ⟨hn1, hnT⟩
    have hn0 : n ≠ 0 := by omega
    have hnpos : (0:ℝ) < (n:ℝ) := by
      have : 0 < n := hn1
      exact_mod_cast this
    have hrad : (0:ℝ) < (radNat n : ℝ) := by exact_mod_cast radNat_pos n
    have hfn : rankinF ε n = 1 / ((radNat n : ℝ) * (n:ℝ) ^ ε) := by
      unfold rankinF; rw [if_neg hn0]
    have hmono : (n:ℝ) ^ ε ≤ (T:ℝ) ^ ε :=
      Real.rpow_le_rpow hnpos.le (by exact_mod_cast hnT) hε.le
    have hne : (0:ℝ) < (n:ℝ) ^ ε := Real.rpow_pos_of_pos hnpos ε
    rw [hfn]
    rw [div_le_iff₀ hrad]
    have : (T:ℝ) ^ ε * (1 / ((radNat n : ℝ) * (n:ℝ) ^ ε)) * (radNat n : ℝ)
        = (T:ℝ) ^ ε / (n:ℝ) ^ ε := by field_simp
    rw [mul_assoc] at this ⊢
    rw [this]
    rw [le_div_iff₀ hne]
    simpa using hmono
  have h1 : ∑ n ∈ Finset.Icc 1 T, 1 / (radNat n : ℝ)
      ≤ ∑ n ∈ Finset.Icc 1 T, (T:ℝ) ^ ε * rankinF ε n :=
    Finset.sum_le_sum hpt
  have h2 : ∑ n ∈ Finset.Icc 1 T, (T:ℝ) ^ ε * rankinF ε n
      = (T:ℝ) ^ ε * ∑ n ∈ Finset.Icc 1 T, rankinF ε n := by
    rw [Finset.mul_sum]
  have hsub : Finset.Icc 1 T ⊆ Finset.range (T + 1) := by
    intro n hn
    rcases Finset.mem_Icc.mp hn with ⟨-, hnT⟩
    exact Finset.mem_range.mpr (by omega)
  have h3 : ∑ n ∈ Finset.Icc 1 T, rankinF ε n ≤ ∑ n ∈ Finset.range (T + 1), rankinF ε n :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => rankinF_nonneg ε n)
  have h4 : ∑ n ∈ Finset.range (T + 1), rankinF ε n ≤ rankinConst ε :=
    rankinF_partial_sum_le hε (T + 1)
  have hTe : (0:ℝ) ≤ (T:ℝ) ^ ε := (Real.rpow_pos_of_pos hT0 ε).le
  calc ∑ n ∈ Finset.Icc 1 T, 1 / (radNat n : ℝ)
      ≤ (T:ℝ) ^ ε * ∑ n ∈ Finset.Icc 1 T, rankinF ε n := by rw [← h2]; exact h1
    _ ≤ (T:ℝ) ^ ε * rankinConst ε := by
        exact mul_le_mul_of_nonneg_left (le_trans h3 h4) hTe
    _ = rankinConst ε * (T:ℝ) ^ ε := by ring

/-- Any finite sum of the Rankin-twisted density is bounded by the Rankin constant. -/
lemma rankinF_finset_sum_le {ε : ℝ} (hε : 0 < ε) (A : Finset ℕ) :
    ∑ n ∈ A, rankinF ε n ≤ rankinConst ε := by
  obtain ⟨N, hN⟩ := Finset.exists_nat_subset_range A
  exact le_trans
    (Finset.sum_le_sum_of_subset_of_nonneg hN (fun n _ _ => rankinF_nonneg ε n))
    (rankinF_partial_sum_le hε N)

/-- **Rankin tail estimate, unconditional.**  With `g(s) = 1/(s · rad(s))`,
for every `0 < ε < 1` there is `C` such that every finite family of pairs
`(s₁, s₂)` of positive integers with `s₁ s₂ > T` satisfies
`∑ g(s₁) g(s₂) ≤ C · T^{-1+ε}`.

This is the `∑_{s₁s₂ > T} 1/(s₁ rad(s₁) s₂ rad(s₂)) ≪_ε T^{-1+ε}` input of the
double-cross sector, in a form uniform over all finite subfamilies (so it also
bounds the corresponding infinite sum). -/
theorem rankin_tail_bound (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℕ, 1 ≤ T → ∀ F : Finset (ℕ × ℕ),
      (∀ x ∈ F, 1 ≤ x.1 ∧ 1 ≤ x.2 ∧ T < x.1 * x.2) →
      ∑ x ∈ F, (1:ℝ) / (((x.1 : ℝ) * (radNat x.1 : ℝ)) * ((x.2 : ℝ) * (radNat x.2 : ℝ)))
        ≤ C * (T:ℝ) ^ (-1 + ε) := by
  have hCpos : (0:ℝ) < rankinConst ε * rankinConst ε := by
    have h := one_le_rankinConst hε; nlinarith
  refine ⟨rankinConst ε * rankinConst ε, hCpos, ?_⟩
  intro T hT F hF
  have hT0 : (0:ℝ) < (T:ℝ) := by exact_mod_cast hT
  -- pointwise Rankin twist
  have hpt : ∀ x ∈ F,
      (1:ℝ) / (((x.1 : ℝ) * (radNat x.1 : ℝ)) * ((x.2 : ℝ) * (radNat x.2 : ℝ)))
        ≤ (T:ℝ) ^ (-1 + ε) * (rankinF ε x.1 * rankinF ε x.2) := by
    intro x hx
    obtain ⟨h1, h2, hgt⟩ := hF x hx
    have hx1 : (1:ℝ) ≤ (x.1 : ℝ) := by exact_mod_cast h1
    have hx2 : (1:ℝ) ≤ (x.2 : ℝ) := by exact_mod_cast h2
    have hr1 : (0:ℝ) < (radNat x.1 : ℝ) := by exact_mod_cast radNat_pos x.1
    have hr2 : (0:ℝ) < (radNat x.2 : ℝ) := by exact_mod_cast radNat_pos x.2
    have hne1 : x.1 ≠ 0 := by omega
    have hne2 : x.2 ≠ 0 := by omega
    have hf1 : rankinF ε x.1 = 1 / ((radNat x.1 : ℝ) * (x.1 : ℝ) ^ ε) := by
      unfold rankinF; rw [if_neg hne1]
    have hf2 : rankinF ε x.2 = 1 / ((radNat x.2 : ℝ) * (x.2 : ℝ) ^ ε) := by
      unfold rankinF; rw [if_neg hne2]
    -- `T^{1-ε} ≤ (x.1 x.2)^{1-ε}`
    have hprod : (T:ℝ) ≤ (x.1 : ℝ) * (x.2 : ℝ) := by
      have : (T:ℝ) ≤ ((x.1 * x.2 : ℕ) : ℝ) := by exact_mod_cast hgt.le
      push_cast at this
      exact this
    have hpow : (T:ℝ) ^ (1 - ε) ≤ ((x.1 : ℝ) * (x.2 : ℝ)) ^ (1 - ε) :=
      Real.rpow_le_rpow hT0.le hprod (by linarith)
    have hxpos : (0:ℝ) < (x.1 : ℝ) * (x.2 : ℝ) := by nlinarith
    have hsplit : ((x.1 : ℝ) * (x.2 : ℝ))
        = ((x.1 : ℝ) * (x.2 : ℝ)) ^ (1 - ε) * ((x.1 : ℝ) ^ ε * (x.2 : ℝ) ^ ε) := by
      rw [← Real.mul_rpow (by linarith) (by linarith),
        ← Real.rpow_add hxpos, sub_add_cancel, Real.rpow_one]
    have hTsplit : (T:ℝ) ^ (-1 + ε) = 1 / (T:ℝ) ^ (1 - ε) := by
      rw [eq_div_iff (by positivity), ← Real.rpow_add hT0]
      norm_num
    rw [hf1, hf2, hTsplit]
    rw [div_le_iff₀ (by positivity)]
    have hkey : (1:ℝ) / (T:ℝ) ^ (1 - ε) * (1 / ((radNat x.1 : ℝ) * (x.1:ℝ) ^ ε)
        * (1 / ((radNat x.2 : ℝ) * (x.2:ℝ) ^ ε)))
        * ((x.1:ℝ) * (radNat x.1 : ℝ) * ((x.2:ℝ) * (radNat x.2 : ℝ)))
        = ((x.1:ℝ) * (x.2:ℝ)) / ((T:ℝ) ^ (1 - ε) * ((x.1:ℝ) ^ ε * (x.2:ℝ) ^ ε)) := by
      field_simp
    rw [hkey, le_div_iff₀ (by positivity)]
    rw [hsplit]
    have hxe : (0:ℝ) < (x.1:ℝ) ^ ε * (x.2:ℝ) ^ ε := by positivity
    nlinarith [hpow, hxe]
  have hstep1 : ∑ x ∈ F, (1:ℝ) / (((x.1 : ℝ) * (radNat x.1 : ℝ)) * ((x.2 : ℝ) * (radNat x.2 : ℝ)))
      ≤ ∑ x ∈ F, (T:ℝ) ^ (-1 + ε) * (rankinF ε x.1 * rankinF ε x.2) :=
    Finset.sum_le_sum hpt
  have hfactor : ∑ x ∈ F, (T:ℝ) ^ (-1 + ε) * (rankinF ε x.1 * rankinF ε x.2)
      = (T:ℝ) ^ (-1 + ε) * ∑ x ∈ F, (rankinF ε x.1 * rankinF ε x.2) := by
    rw [Finset.mul_sum]
  -- bound the double sum by the square of the Rankin constant
  have hsubset : F ⊆ (F.image Prod.fst) ×ˢ (F.image Prod.snd) := by
    intro x hx
    exact Finset.mem_product.mpr
      ⟨Finset.mem_image.mpr ⟨x, hx, rfl⟩, Finset.mem_image.mpr ⟨x, hx, rfl⟩⟩
  have hdouble : ∑ x ∈ F, (rankinF ε x.1 * rankinF ε x.2)
      ≤ rankinConst ε * rankinConst ε := by
    have h1 : ∑ x ∈ F, (rankinF ε x.1 * rankinF ε x.2)
        ≤ ∑ x ∈ (F.image Prod.fst) ×ˢ (F.image Prod.snd), (rankinF ε x.1 * rankinF ε x.2) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun x _ _ => mul_nonneg (rankinF_nonneg ε _) (rankinF_nonneg ε _))
    have h2 : ∑ x ∈ (F.image Prod.fst) ×ˢ (F.image Prod.snd), (rankinF ε x.1 * rankinF ε x.2)
        = (∑ a ∈ F.image Prod.fst, rankinF ε a) * (∑ b ∈ F.image Prod.snd, rankinF ε b) := by
      rw [Finset.sum_product, Finset.sum_mul]
      exact Finset.sum_congr rfl (fun a _ => by rw [Finset.mul_sum])
    rw [h2] at h1
    refine le_trans h1 (mul_le_mul (rankinF_finset_sum_le hε _) (rankinF_finset_sum_le hε _)
      (Finset.sum_nonneg (fun n _ => rankinF_nonneg ε n)) ?_)
    exact le_trans zero_le_one (one_le_rankinConst hε)
  have hTe : (0:ℝ) ≤ (T:ℝ) ^ (-1 + ε) := (Real.rpow_pos_of_pos hT0 _).le
  calc ∑ x ∈ F, (1:ℝ) / (((x.1 : ℝ) * (radNat x.1 : ℝ)) * ((x.2 : ℝ) * (radNat x.2 : ℝ)))
      ≤ (T:ℝ) ^ (-1 + ε) * ∑ x ∈ F, (rankinF ε x.1 * rankinF ε x.2) := by
        rw [← hfactor]; exact hstep1
    _ ≤ (T:ℝ) ^ (-1 + ε) * (rankinConst ε * rankinConst ε) :=
        mul_le_mul_of_nonneg_left hdouble hTe
    _ = rankinConst ε * rankinConst ε * (T:ℝ) ^ (-1 + ε) := by ring

end ShiftedMobiusBank
