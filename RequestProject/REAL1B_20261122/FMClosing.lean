import RequestProject.REAL1B_20261122.FMSource
import RequestProject.REAL1B_20261122.H2Source

/-! Gold 4.57–4.60, joint signed route. All finite sums use the larger member
in the physical window (x/2,x]. The FM twin mass uses that same window. -/
namespace REAL1B.FM.Closing
open Filter Vaughan Source
noncomputable section
open Classical

def F (x : ℝ) (n : ℕ) : ℝ :=
  if Squarefree n ∧ ¬ good n ∧ Sifted (z x) n ∧ retained n
  then kernelH n - kernelK (x/2) n else 0
def G (n : ℕ) : ℝ := if Squarefree n ∧ good n then max (-kernelH n) 0 else 0
def phi (x : ℝ) (n : ℕ) := F x n - G n

/-- Gold 4.58 (U1), after exact owner counting. -/
def covariance (x : ℝ) :=
  total (x/2) (fun n =>
    (sieve (x ^ (1/800000000000 : ℝ)) (n-2) * lam (n-2) - H2.series) * phi x n)

def primeRow (u d : ℝ) (k l : ℕ) : ℝ :=
  Real.log l * ∑ m ∈ (k/l).divisors,
    if u < (m:ℝ) ∧ d < (m*l:ℕ) then mu m else 0

def coeff (u d : ℝ) (k : ℕ) :=
  ∑ l ∈ k.divisors, if l.Prime ∧ u < (l:ℝ) then primeRow u d k l else 0

/-- Only the distinguished prime can survive the outer sum. -/
theorem one_large_switch {u d : ℝ} {k p : ℕ} (hpk : p ∈ k.divisors)
    (hp : p.Prime) (hu : u < (p:ℝ))
    (honly : ∀ l ∈ k.divisors, l.Prime → u < (l:ℝ) → l = p) :
    coeff u d k = primeRow u d k p := by
  unfold coeff
  rw [Finset.sum_eq_single p]
  · simp [hp, hu]
  · intro l hl hne
    apply if_neg
    rintro ⟨hlp,hlu⟩
    exact hne (honly l hl hlp hlu)
  · simp [hpk]

theorem coeff_prime {u d : ℝ} {p : ℕ} (hp : p.Prime) (hu : 1 ≤ u) :
    coeff u d p = 0 := by
  unfold coeff
  rw [Nat.Prime.divisors hp]
  simp [hp, primeRow, Nat.div_self hp.pos, not_lt.mpr hu]

private theorem semiprime_row {u d : ℝ} {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hu : 1 ≤ u) (hq' : u < (q:ℝ)) (hd : d < (p*q:ℕ)) :
    primeRow u d (p*q) p = - Real.log p := by
  have hd' : d < (q:ℝ)*p := by simpa [Nat.cast_mul, mul_comm] using hd
  have h1 : (1:ℕ) ≠ q := Ne.symm hq.ne_one
  simp [primeRow, Nat.mul_div_cancel_left _ hp.pos, hq.divisors, h1,
    not_lt.mpr hu, hq', hd', mu, ArithmeticFunction.moebius_apply_prime hq]

/-- When both prime divisors survive the cutoffs, their full signed
coefficient is exactly minus log k. Every cofactor choice is retained. -/
theorem coeff_semiprime {u d : ℝ} {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hne : p ≠ q) (hu : 1 ≤ u) (hup : u < (p:ℝ)) (huq : u < (q:ℝ))
    (hd : d < (p*q:ℕ)) : coeff u d (p*q) = - Real.log (p*q:ℕ) := by
  have hdiv : (p*q).divisors.filter (fun l : ℕ => l.Prime ∧ u < (l:ℝ)) = {p,q} := by
    ext l
    simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨h,_⟩, hl,_⟩
      exact (hl.dvd_mul.mp h).imp (Nat.prime_dvd_prime_iff_eq hl hp).mp
        (Nat.prime_dvd_prime_iff_eq hl hq).mp
    · rintro (rfl | rfl)
      · exact ⟨⟨dvd_mul_right .., Nat.mul_ne_zero hp.ne_zero hq.ne_zero⟩,hp,hup⟩
      · exact ⟨⟨dvd_mul_left .., Nat.mul_ne_zero hp.ne_zero hq.ne_zero⟩,hq,huq⟩
  have hr := semiprime_row hp hq hu huq hd
  have hd' : d < (q*p:ℕ) := by simpa [Nat.mul_comm] using hd
  have hs := semiprime_row hq hp hu hup hd'
  rw [Nat.mul_comm q p] at hs
  rw [coeff, ← Finset.sum_filter, hdiv, Finset.sum_insert (by simpa using hne),
    Finset.sum_singleton, hr, hs, Nat.cast_mul, Real.log_mul (by exact_mod_cast hp.ne_zero) (by exact_mod_cast hq.ne_zero)]
  ring

def cutU (x : ℝ) := x ^ (0.24 : ℝ)
def cutD (x : ℝ) := x ^ (0.49 : ℝ)
def roughW (a x : ℝ) := Real.exp (Real.log x ^ a)

def term (a x : ℝ) (n : ℕ) :=
  let k := n-2
  sieve (roughW a x) k * mu k ^ 2 * coeff (cutU x) (cutD x) k * phi x n
def largeProduct (a x : ℝ) := total (x/2) (term a x)

/-- Gold 4.59 Joint Signed, Part A (2.1). Bounds involving 96-s or
100-s are written additively to avoid truncated natural subtraction. -/
def admissible (i j k l : ℕ) : Prop :=
  let s := i+j+k+l
  3 ≤ i ∧ i < j ∧ j < k ∧ k < l ∧ l ≤ 48 ∧ i+1 ≤ 19 ∧
    (i+1 ≤ 19 ∨ 21 ≤ i) ∧ (j+1 ≤ 19 ∨ 21 ≤ j) ∧
    (k+1 ≤ 19 ∨ 21 ≤ k) ∧ (l+1 ≤ 19 ∨ 21 ≤ l) ∧
    l+1+s ≤ 96 ∧ s+21 ≤ 96 ∧ 100 ≤ 49+s ∧
    51 ≤ i+k+l ∧ k+l+2 ≤ 49

theorem first_index_lower {i j k l : ℕ} (h : admissible i j k l) : 4 ≤ i := by
  unfold admissible at h
  omega

def inCell (n p i : ℕ) : Prop :=
  (i:ℝ)/100 < Real.log p / Real.log n ∧ Real.log p / Real.log n < ((i:ℝ)+1)/100

/-- The total supplies the physical window. primeFactorsList is ordered with
multiplicity; the fifth coordinate is determined by the full factorization. -/
def boxes (n : ℕ) : Prop := Squarefree n ∧
  ∃ p q r s t i j k l : ℕ, n.primeFactorsList = [p,q,r,s,t] ∧ admissible i j k l ∧
    inCell n p i ∧ inCell n q j ∧ inCell n r k ∧ inCell n s l

/-- The two input-side conditions apply to k=n-2. -/
def inE (x : ℝ) (n : ℕ) :=
  boxes n ∧ Squarefree (n-2) ∧ Sifted (cutU x) (n-2)
def selected (a x : ℝ) :=
  total (x/2) (fun n => if inE x n then term a x n else 0)
def complement (a x : ℝ) :=
  total (x/2) (fun n => if inE x n then 0 else term a x n)
def primeCompanion (x : ℝ) :=
  total (x/2) (fun n => actual x n * (if boxes n then phi x n else 0))
def QE (a x : ℝ) :=
  complement a x + 0.02 * primeCompanion x

theorem source_split (a x : ℝ) :
    largeProduct a x = selected a x + complement a x := by
  unfold largeProduct selected complement total
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  by_cases h : inE x n <;> simp [h]

theorem signed_identity (a x : ℝ) :
    largeProduct a x - QE a x = selected a x - 0.02 * primeCompanion x := by
  rw [source_split a x]
  unfold QE
  ring

/-- Split the literal complement at semiprime inputs with both primes above
U and product above D. The output masks and presieve are evaluated at their
original arguments on both sides of the split. -/
def pairSector (x : ℝ) (n : ℕ) : Prop :=
  ¬ inE x n ∧ ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ n-2 = p*q ∧
    cutU x < (p:ℝ) ∧ cutU x < (q:ℝ) ∧ cutD x < (p*q:ℕ)
def otherComplement (a x : ℝ) := total (x/2) (fun n =>
  if ¬ inE x n ∧ ¬ pairSector x n then term a x n else 0)
def pairWeight (a x : ℝ) (n : ℕ) :=
  sieve (roughW a x) (n-2) * mu (n-2)^2 * Real.log (n-2 : ℕ)
def pairMass (part : ℝ → ℝ) (a x : ℝ) := total (x/2) (fun n =>
  if pairSector x n then pairWeight a x n * part (phi x n) else 0)

theorem pair_weight_nonneg {a x : ℝ} {n : ℕ} (h : pairSector x n) :
    0 ≤ pairWeight a x n := by
  obtain ⟨_, p,q,hp,hq,_,heq,_⟩ := h
  have hpos : 1 ≤ n-2 := by rw [heq]; exact Nat.mul_pos hp.pos hq.pos
  have hg := Real.log_nonneg (by exact_mod_cast hpos : (1:ℝ) ≤ (n-2:ℕ))
  unfold pairWeight sieve
  split_ifs <;> positivity

theorem pair_mass_nonneg (part : ℝ → ℝ) (hpart : ∀ y, 0 ≤ part y) (a x : ℝ) :
    0 ≤ pairMass part a x := by
  unfold pairMass total
  apply Finset.sum_nonneg
  intro n _
  by_cases h : pairSector x n
  · simpa [h] using mul_nonneg (pair_weight_nonneg (a:=a) h) (hpart (phi x n))
  · simp [h]

/-- Negative Phi contributes positively on this semiprime sector. Both pieces
appear with their actual signs before any asymptotic bound is used. -/
theorem complement_pair_balance (a x : ℝ) (hu : 1 ≤ cutU x) :
    QE a x = otherComplement a x + pairMass (fun y => max (-y) 0) a x -
      pairMass (fun y => max y 0) a x + 0.02 * primeCompanion x := by
  unfold QE
  congr 1
  unfold complement otherComplement pairMass total
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _
  by_cases h : pairSector x n
  · have hkeep := h
    obtain ⟨hn,p,q,hp,hq,hne,hk,hup,huq,hd⟩ := h
    have cf := coeff_semiprime hp hq hne hu hup huq hd
    rw [← hk] at cf
    simp [hkeep, hn, term, cf, pairWeight]
    rcases le_total (phi x n) 0 with hn' | hn'
    · rw [max_eq_left (by linarith), max_eq_right hn']
      ring
    · rw [max_eq_right (by linarith), max_eq_left hn']
      ring
  · by_cases hn : inE x n <;> simp [h, hn]

/-- A subpower input presieve lies below every fixed positive power. -/
theorem log_power_lt_linear {a b : ℝ} (ha : a < 1) (hb : 0 < b) :
    ∀ᶠ x : ℝ in atTop, Real.log x ^ a < b * Real.log x := by
  have ht := (tendsto_rpow_atTop (sub_pos.mpr ha)).comp Real.tendsto_log_atTop
  filter_upwards [ht.eventually_gt_atTop (1/b), eventually_gt_atTop (1:ℝ)] with x hx hx1
  change 1/b < Real.log x ^ (1-a) at hx
  have hL := Real.log_pos hx1
  have h1 := (div_lt_iff₀ hb).mp hx
  have hsum : Real.log x ^ a * Real.log x ^ (1-a) = Real.log x := by
    rw [← Real.rpow_add hL, show a + (1-a) = 1 by ring, Real.rpow_one]
  nlinarith only [mul_lt_mul_of_pos_left h1 (Real.rpow_pos_of_pos hL a), hsum,
    congrArg (fun t : ℝ => b*t) hsum]

theorem boxes_prime_size {n p : ℕ} (hn : 1 < (n:ℝ)) (hB : boxes n)
    (hp : p.Prime) (hd : p ∣ n) : 0.04 * Real.log n < Real.log p := by
  obtain ⟨_, u,v,r,s,t,i,j,k,l,hf,hidx,hu,_⟩ := hB
  have hmem : p ∈ n.primeFactorsList := (Nat.mem_primeFactorsList_iff_dvd (by
    intro h; norm_num [h] at hn) hp).mpr hd
  have hsort := (Nat.primeFactorsList_sorted n).pairwise
  rw [hf] at hmem hsort
  have hup : u ≤ p := by
    rcases List.mem_cons.mp hmem with he | ht
    · omega
    · exact (List.pairwise_cons.mp hsort).1 p ht
  have huprime : u.Prime := Nat.prime_of_mem_primeFactorsList (by rw [hf]; simp)
  have hlog : Real.log u ≤ Real.log p := Real.log_le_log (by exact_mod_cast huprime.pos) (by exact_mod_cast hup)
  have hfirst : (4:ℝ) ≤ i := by exact_mod_cast first_index_lower hidx
  have hcell := (lt_div_iff₀ (Real.log_pos hn)).mp hu.1
  nlinarith only [hcell, hlog, mul_le_mul_of_nonneg_right hfirst (Real.log_pos hn).le]

/-- On the joint boxes the output presieve in the original prime source
is eventually automatic throughout the physical window. -/
theorem boxes_sifted : ∀ᶠ x : ℝ in atTop, ∀ n ∈ interval (x/2), boxes n → Sifted (y x) n := by
  filter_upwards [log_power_lt_linear (a:=(1/20:ℝ)) (b:=0.01) (by norm_num) (by norm_num),
    eventually_ge_atTop (4:ℝ)] with x hy hx n hn hB p hp hd
  have hn' : x/2 < (n:ℝ) := (Finset.mem_filter.mp hn).2
  have hn1 : (1:ℝ) < n := by linarith
  have hlog := boxes_prime_size hn1 hB hp hd
  have h2 := Real.log_le_log (by norm_num : (0:ℝ)<2) (by linarith : 2 ≤ (n:ℝ))
  have h3 := Real.log_le_log (by linarith : 0 < x) (by linarith : x ≤ 2*(n:ℝ))
  rw [Real.log_mul (by norm_num) (by linarith)] at h3
  unfold y
  rw [← Real.exp_log (by exact_mod_cast hp.pos : (0:ℝ) < p), Real.exp_lt_exp]
  linarith [Real.log_pos hn1]

def rawPrimeCompanion (x : ℝ) :=
  total (x/2) (fun n => theta (n-2) * (if boxes n then phi x n else 0))
theorem prime_companion_eq_raw : ∀ᶠ x : ℝ in atTop, primeCompanion x = rawPrimeCompanion x := by
  filter_upwards [boxes_sifted] with x hx
  unfold primeCompanion rawPrimeCompanion total
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hb : boxes n
  · simp [hb, actual, sieve, hx n hn hb]
  · simp [hb]

/-- The inherited subpower presieve is redundant on the selected input mask. -/
theorem selected_without_presieve {a : ℝ} (ha : a < 1) :
    ∀ᶠ x : ℝ in atTop, selected a x = total (x/2) (fun n => if inE x n then
      mu (n-2)^2 * coeff (cutU x) (cutD x) (n-2) * phi x n else 0) := by
  filter_upwards [log_power_lt_linear (b:=0.24) ha (by norm_num),
    eventually_gt_atTop (1:ℝ)] with x hlog hx
  have hz : roughW a x < cutU x := by
    unfold roughW cutU
    rw [Real.rpow_def_of_pos (show 0 < x by linarith) (0.24:ℝ), Real.exp_lt_exp]
    linarith
  unfold selected total
  apply Finset.sum_congr rfl
  intro n _
  by_cases h : inE x n
  · have hw : Sifted (roughW a x) (n-2) := fun p hp hd => hz.trans (h.2.2 p hp hd)
    simp [h, term, sieve, hw]
  · simp [h]

theorem margin_certificate :
    (0.00048 : ℝ) < 7558755113252227 / 15547490081739244800 ∧
    (0.999892775499 : ℝ) + 0.00048 = 1.000372775499 := by norm_num

/-- Fixed tolerance, then sufficiently large physical scales. -/
def LowerLedger : Prop := ∀ e : ℝ, 0 < e → ∀ᶠ x : ℝ in atTop,
  (0.999892775499 - e) * Sb x ≤ covariance x + T x
def Reduction (a : ℝ) : Prop := ∀ e : ℝ, 0 < e → ∀ᶠ x : ℝ in atTop,
  |covariance x - largeProduct a x| ≤ e * Sb x
def Joint (a : ℝ) : Prop := ∀ e : ℝ, 0 < e → ∀ᶠ x : ℝ in atTop,
  selected a x - 0.02 * primeCompanion x ≤ (-0.00048 + e) * Sb x
def ComplementBound (a κ : ℝ) : Prop :=
  ∀ e : ℝ, 0 < e → ∀ᶠ x : ℝ in atTop, QE a x ≤ (1.000372775499 - κ + e) * Sb x

/-- Equivalent arithmetic target after separating the signed semiprime source.
Both nonnegative semiprime masses occur with their full weights. -/
theorem complement_bound_iff_pair_budget (a κ : ℝ) :
    ComplementBound a κ ↔ ∀ e : ℝ, 0 < e → ∀ᶠ x : ℝ in atTop,
      otherComplement a x + pairMass (fun y => max (-y) 0) a x + 0.02 * primeCompanion x ≤
        (1.000372775499 - κ + e) * Sb x + pairMass (fun y => max y 0) a x := by
  have hu : ∀ᶠ x : ℝ in atTop, 1 ≤ cutU x := by
    filter_upwards [eventually_ge_atTop (1:ℝ)] with x hx
    exact Real.one_le_rpow hx (by norm_num)
  constructor
  · intro h e he
    filter_upwards [hu, h e he] with x hx hq
    rw [complement_pair_balance a x hx] at hq
    linarith
  · intro h e he
    filter_upwards [hu, h e he] with x hx hq
    rw [complement_pair_balance a x hx]
    linarith

theorem eventual_reserve {a κ : ℝ}
    (hl : LowerLedger) (hr : Reduction a) (hj : Joint a) (hq : ComplementBound a κ) :
    ∀ e : ℝ, 0 < e → ∀ᶠ x : ℝ in atTop, (κ-e) * Sb x ≤ T x := by
  intro e he
  have h : 0 < e/4 := by linarith
  filter_upwards [hl _ h, hr _ h, hj _ h, hq _ h] with x hL hR hJ hQ
  rw [← signed_identity] at hJ
  have hR' := (abs_le.mp hR).2
  linarith only [hL, hR', hJ, hQ]

private theorem infinite_of_reserve {κ : ℝ} (hκ : 0 < κ)
    (hR : ∀ e : ℝ, 0 < e → ∀ᶠ x : ℝ in atTop, (κ-e) * Sb x ≤ T x)
    (hs : ∀ᶠ x : ℝ in atTop, 0 < Sb x) :
    Set.Infinite {p : ℕ | p.Prime ∧ (p+2).Prime} := by
  have h := hR (κ/2) (by linarith)
  apply infinite_of_unbounded_mass
  intro M
  obtain ⟨x,hx,hT,hS⟩ := ((eventually_gt_atTop (2*(M:ℝ))).and (h.and hs)).exists
  refine ⟨x/2, by linarith, ?_⟩
  exact (mul_pos (by linarith : 0 < κ - κ/2) hS).trans_le (hT.trans (T_le_native x))

theorem infinite_of_joint_complement {a : Set.Ioo (0:ℝ) 1} {κ : ℝ} (hκ : 0 < κ)
    (hl : LowerLedger) (hr : Reduction a) (hj : Joint a) (hq : ComplementBound a κ)
    (hs : ∀ᶠ x : ℝ in atTop, 0 < Sb x) :
    Set.Infinite {p : ℕ | p.Prime ∧ (p+2).Prime} :=
  infinite_of_reserve hκ (eventual_reserve hl hr hj hq) hs

/-! Gold 4.60 Fouvry boxwise variant, §§B–E. The three analytic inputs below
keep the lower-sieve population, all three short pairs in the positive
exception, and the genuine prime companion on the same source. -/
def triangle (x : ℝ) (k : ℕ) : Prop :=
  ∃ p q r s : ℕ, k.primeFactorsList = [p,q,r,s] ∧
    (p*q:ℕ) ≤ cutD x ∧ (p*r:ℕ) ≤ cutD x ∧ (q*r:ℕ) ≤ cutD x

def inputPopulation (x : ℝ) :=
  total (x/2) (fun n => if inE x n then mu (n-2)^2 * phi x n else 0)
def trianglePopulation (x : ℝ) :=
  total (x/2) (fun n => if inE x n ∧ triangle x (n-2) then mu (n-2)^2 * phi x n else 0)

def RoughSupply : Prop := ∀ e : ℝ, 0 < e → ∀ᶠ x : ℝ in atTop,
  (0.0026942415488-e) * Sb x ≤ 0.02 * Real.log x * inputPopulation x
def TriangleCost : Prop := ∀ e : ℝ, 0 < e → ∀ᶠ x : ℝ in atTop,
  0.49 * Real.log x * trianglePopulation x ≤ (153125/248769792+e) * Sb x
def CoefficientAssembly (a : ℝ) : Prop := ∀ e : ℝ, 0 < e → ∀ᶠ x : ℝ in atTop,
  selected a x - 0.02 * rawPrimeCompanion x ≤
    0.49 * Real.log x * trianglePopulation x - 0.02 * Real.log x * inputPopulation x + e * Sb x
def Joint60 (a : ℝ) : Prop := ∀ e : ℝ, 0 < e → ∀ᶠ x : ℝ in atTop,
  selected a x - 0.02 * primeCompanion x ≤ (-0.00207+e) * Sb x
def Complement60 (a κ : ℝ) : Prop := ∀ e : ℝ, 0 < e → ∀ᶠ x : ℝ in atTop,
  QE a x ≤ (1.001962775499-κ+e) * Sb x

/-- The rational cubic used by the box verifier always rounds the true
logarithmic factor down. The next positive series term makes this strict. -/
theorem cubic_log_lower {z : ℝ} (hz : 0 < z) (hz1 : z < 1) :
    2 * (z+z^3/3) < Real.log ((1+z)/(1-z)) := by
  have h := Real.hasSum_log_sub_log_of_abs_lt_one ((abs_of_pos hz).trans_lt hz1)
  have hs := sum_le_hasSum (Finset.range 3) (fun k _ => by positivity) h
  norm_num [Finset.sum_range_succ] at hs
  rw [Real.log_div (by linarith) (by linarith)]
  linarith only [hs, pow_pos hz 5]

theorem boxwise_rounding :
    (0.00207:ℝ) < 0.0026942415488 - 153125/248769792 ∧
    (0.999892775499:ℝ)+0.00207 = 1.001962775499 := by norm_num

theorem joint60_of_source_estimates {a : ℝ} (hN : RoughSupply) (hM : TriangleCost)
    (hA : CoefficientAssembly a) (hs : ∀ᶠ x : ℝ in atTop, 0 < Sb x) : Joint60 a := by
  intro e he
  have h : 0 < e/3 := by linarith
  filter_upwards [hN _ h, hM _ h, hA _ h, hs, prime_companion_eq_raw] with x h1 h2 h3 h4 h5
  rw [h5]
  linarith only [h1, h2, h3, mul_lt_mul_of_pos_right boxwise_rounding.1 h4]

theorem gold60_lower {a : ℝ} (hl : LowerLedger) (hr : Reduction a) (hj : Joint60 a) :
    ∀ e : ℝ, 0 < e → ∀ᶠ x : ℝ in atTop, (1.001962775499-e)*Sb x ≤ QE a x + T x := by
  intro e he
  have h : 0 < e/3 := by linarith
  filter_upwards [hl _ h, hr _ h, hj _ h] with x hL hR hJ
  rw [← signed_identity] at hJ
  linarith only [hL, (abs_le.mp hR).2, hJ]

theorem reserve60 {a κ : ℝ} (hl : LowerLedger) (hr : Reduction a) (hj : Joint60 a)
    (hq : Complement60 a κ) :
    ∀ e : ℝ, 0 < e → ∀ᶠ x : ℝ in atTop, (κ-e) * Sb x ≤ T x := by
  intro e he
  have h : 0 < e/2 := by linarith
  filter_upwards [gold60_lower hl hr hj _ h, hq _ h] with x hL hQ
  linarith only [hL,hQ]

theorem infinite_of_boxwise_complement {a : Set.Ioo (0:ℝ) 1} {κ : ℝ} (hκ : 0 < κ)
    (hl : LowerLedger) (hr : Reduction a) (hN : RoughSupply) (hM : TriangleCost)
    (hA : CoefficientAssembly a) (hq : Complement60 a κ) (hs : ∀ᶠ x : ℝ in atTop, 0 < Sb x) :
    Set.Infinite {p : ℕ | p.Prime ∧ (p+2).Prime} :=
  infinite_of_reserve hκ (reserve60 hl hr (joint60_of_source_estimates hN hM hA hs) hq) hs


end
end REAL1B.FM.Closing

#print axioms REAL1B.FM.Closing.one_large_switch
#print axioms REAL1B.FM.Closing.coeff_prime
#print axioms REAL1B.FM.Closing.coeff_semiprime
#print axioms REAL1B.FM.Closing.first_index_lower
#print axioms REAL1B.FM.Closing.source_split
#print axioms REAL1B.FM.Closing.signed_identity
#print axioms REAL1B.FM.Closing.pair_weight_nonneg
#print axioms REAL1B.FM.Closing.pair_mass_nonneg
#print axioms REAL1B.FM.Closing.complement_pair_balance
#print axioms REAL1B.FM.Closing.log_power_lt_linear
#print axioms REAL1B.FM.Closing.boxes_prime_size
#print axioms REAL1B.FM.Closing.boxes_sifted
#print axioms REAL1B.FM.Closing.prime_companion_eq_raw
#print axioms REAL1B.FM.Closing.selected_without_presieve
#print axioms REAL1B.FM.Closing.margin_certificate
#print axioms REAL1B.FM.Closing.complement_bound_iff_pair_budget
#print axioms REAL1B.FM.Closing.eventual_reserve
#print axioms REAL1B.FM.Closing.infinite_of_joint_complement

#print axioms REAL1B.FM.Closing.boxwise_rounding
#print axioms REAL1B.FM.Closing.joint60_of_source_estimates
#print axioms REAL1B.FM.Closing.gold60_lower
#print axioms REAL1B.FM.Closing.reserve60
#print axioms REAL1B.FM.Closing.infinite_of_boxwise_complement
#print axioms REAL1B.FM.Closing.cubic_log_lower
