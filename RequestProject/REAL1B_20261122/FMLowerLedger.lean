import RequestProject.REAL1B_20261122.FMCollarIntegral

/-! Gold 4.57 complete-source partition and Gold 4.58 (U9).
All error functions below are finite sums on the same physical window. -/
namespace REAL1B.FM.Ledger
open Filter Vaughan Source Analytic ArithmeticFunction
noncomputable section
open Classical

def positive (x : ℝ) (n : ℕ) : ℝ := if n ∈ interval (x/2) ∧ Squarefree n ∧ Direct.good n
  then max (kernelH n) 0 else 0
def calibrated (x : ℝ) (n : ℕ) : ℝ := if Squarefree n ∧ Sifted (z x) n
  then kernelH n - kernelK (x/2) n else 0
def omitted (rank : ℕ → Prop) (x : ℝ) (n : ℕ) : ℝ :=
  if ¬Direct.good n ∧ rank (cardFactors n) then calibrated x n else 0

/-- Pointwise geometric inputs on the actual H/K source, stated only where used. -/
structure GeometryAt (x : ℝ) : Prop where
  prime : ∀ n ∈ interval (x/2), n.Prime → Sifted (z x) n ∧ kernelH n - kernelK (x/2) n = 1
  good : ∀ n ∈ interval (x/2), Squarefree n → Direct.good n →
    kernelK (x/2) n = 0 ∧ (kernelH n ≠ 0 → Sifted (z x) n)

theorem H_prime {p : ℕ} (hp : p.Prime) : kernelH p = 1 := by
  have hp' : (1:ℝ) < p := by exact_mod_cast hp.one_lt
  have hlt : (p:ℝ)^γ < p := by
    simpa only [Real.rpow_one] using Real.rpow_lt_rpow_of_exponent_lt hp' (by norm_num [γ,ε] : γ < 1)
  have hge : 1 ≤ (p:ℝ)^γ := Real.one_le_rpow hp'.le (by norm_num [γ,ε])
  have h₁ : divisorCoefficient p 1 = 1 := by
    simp [divisorCoefficient,profile,g0,mu,hge,show (0:ℝ) ≤ β by norm_num [β,ε]]
  have h₂ : divisorCoefficient p p = 0 := by simp [divisorCoefficient,not_le.mpr hlt]
  simp [kernelH,hp.divisors,Ne.symm hp.ne_one,h₁,h₂]

theorem K_prime (X : ℝ) {p : ℕ} (hp : p.Prime) : kernelK X p = 0 := by
  have hzero (d : ℕ) (hd : d ∈ p.divisors) : labels X d = 0 := by
    unfold labels
    apply Finset.sum_eq_zero
    intro u hu
    apply Finset.sum_eq_zero
    intro v hv
    apply Finset.sum_eq_zero
    intro w _
    apply if_neg
    rintro ⟨hu',hv',_⟩
    have hdu := (Nat.mem_divisors.mp hu).1
    have hdp := (Nat.mem_divisors.mp hd).1
    have hueq := (Nat.prime_dvd_prime_iff_eq hu' hp).mp (hdu.trans hdp)
    have hdeq : d = u := Nat.le_antisymm (hueq ▸ Nat.le_of_dvd hp.pos hdp)
      (Nat.le_of_dvd (Nat.pos_of_mem_divisors hd) hdu)
    have hv₁ := (Nat.mem_divisors.mp hv).1
    rw [hdeq,Nat.div_self hu'.pos] at hv₁
    exact hv'.ne_one (Nat.dvd_one.mp hv₁)
  unfold kernelK
  rw [Finset.sum_eq_zero (fun d hd => by simp [hzero d hd]),mul_zero]

theorem geometry_of_good
    (hgood : ∀ᶠ x : ℝ in atTop, ∀ n ∈ interval (x/2), Squarefree n → Direct.good n →
      kernelK (x/2) n = 0 ∧ (kernelH n ≠ 0 → Sifted (z x) n)) :
    ∀ᶠ x : ℝ in atTop, GeometryAt x := by
  filter_upwards [hgood,small_power (by norm_num : (1/400000000000:ℝ) ≤ 1/2)] with x hgood hz
  refine ⟨?_,hgood⟩
  intro p hp hprime
  refine ⟨?_,by rw [H_prime hprime,K_prime _ hprime,sub_zero]⟩
  intro q hq hd
  have hlt : z x < (p:ℝ) := (hz p hp).trans_le (by exact_mod_cast Nat.sub_le p 2)
  exact (Nat.prime_dvd_prime_iff_eq hq hprime).mp hd ▸ hlt

theorem geometry : ∀ᶠ x : ℝ in atTop, GeometryAt x := by
  apply geometry_of_good
  filter_upwards [eventually_ge_atTop (4:ℝ)] with x hx n hn hs hg
  exact ⟨GoodSupport.marked_zero hx hn hg,GoodSupport.active_rough hx hn hs hg⟩

theorem partition {x : ℝ} (h : GeometryAt x) {n : ℕ} (hn : n ∈ interval (x/2)) :
    calibrated x n = primeMask n + positive x n + Direct.phi x n +
      omitted (· = 2) x n + omitted (· = 4) x n + omitted (256 ≤ ·) x n := by
  have hn₂ := (window hn).2.2
  by_cases hp : n.Prime
  · obtain ⟨hz,hk⟩ := h.prime n hn hp
    have hcard := cardFactors_eq_one_iff_prime.mpr hp
    have hg : ¬ Direct.good n := fun hh => hh.2.1 hp
    simp [calibrated,primeMask,hp,hp.squarefree,hz,hk,positive,Direct.phi,Direct.F,Direct.G,
      omitted,hg,retained,hcard]
  · have hc₀ : cardFactors n ≠ 0 := fun hc => by
      rcases cardFactors_eq_zero_iff_eq_zero_or_one.mp hc with h | h <;> omega
    have hc₁ : cardFactors n ≠ 1 := fun hc => hp (cardFactors_eq_one_iff_prime.mp hc)
    by_cases hs : Squarefree n
    · by_cases hg : Direct.good n
      · obtain ⟨hK,hH⟩ := h.good n hn hs hg
        by_cases hz : Sifted (z x) n
        · simp [calibrated,primeMask,hp,positive,hn,hs,hg,hK,hz,Direct.phi,Direct.F,Direct.G,omitted]
          simpa [sub_eq_add_neg] using (max_zero_sub_max_neg_zero_eq_self (kernelH n)).symm
        · have hzero : kernelH n = 0 := by by_contra hne; exact hz (hH hne)
          simp [calibrated,primeMask,hp,positive,hn,hs,hg,hz,hzero,Direct.phi,Direct.F,Direct.G,omitted]
      · by_cases hz : Sifted (z x) n
        · have hr : retained n ↔ cardFactors n ≠ 2 ∧ cardFactors n ≠ 4 ∧ ¬256 ≤ cardFactors n := by
            unfold retained; omega
          simp only [calibrated,hs,hz,and_self,if_true,primeMask,if_neg hp,positive,hn,hg,and_false,
            if_false,Direct.phi,Direct.F,Direct.G,not_false_eq_true, true_and,omitted,hr]
          split_ifs <;> first | omega | ring
        · simp [calibrated,primeMask,hp,positive,hg,hz,Direct.phi,Direct.F,Direct.G,omitted]
    · simp [calibrated,primeMask,hp,positive,hs,Direct.phi,Direct.F,Direct.G,omitted]

def weighted (w : ℝ → ℕ → ℝ) (f : ℝ → ℕ → ℝ) (x : ℝ) := total (x/2) (fun n => w x n * f x n)
def deviation (f : ℝ → ℕ → ℝ) (x : ℝ) := weighted actual f x - weighted compare f x
def normalError (x : ℝ) := mean Direct.phi x - weighted compare Direct.phi x
def powerError (x : ℝ) := lambdaSum (intrinsicCut x) x (Direct.phi x) - weighted actual Direct.phi x

theorem exact_ledger {x : ℝ} (h : GeometryAt x) :
    Closing.covariance x + T x + weighted actual positive x =
    Sb x + weighted compare positive x - deviation (omitted (· = 2)) x -
      deviation (omitted (· = 4)) x - deviation (omitted (256 ≤ ·)) x +
      deviation calibrated x + powerError x - normalError x := by
  have part (w : ℝ → ℕ → ℝ) : weighted w calibrated x = total (x/2) (fun n => w x n * primeMask n) +
      weighted w positive x + weighted w Direct.phi x + weighted w (omitted (· = 2)) x +
      weighted w (omitted (· = 4)) x + weighted w (omitted (256 ≤ ·)) x := by
    unfold weighted total
    simp only [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    rw [partition h hn]
    ring
  rw [native_covariance]
  unfold deviation powerError normalError T Sb
  rw [part actual,part compare]
  ring

def goodCap : ℝ := 0.0000000142500001
def goodRational : ℝ :=
  let a₀ := 1/5 - ε
  ε/(a₀*(1-a₀)) + 2*ε/(β*(1-β)) + ε^2/(2*a₀^2*(3/5)) +
    3*(5*ε)^4/((Nat.factorial 5:ℝ)*Nat.factorial 4*a₀^5)

theorem good_cap_rounding : goodRational < goodCap := by
  norm_num [goodRational,goodCap,ε,β,Nat.factorial]

def pairCap : ℝ := ε / (ν*(1-ν))
def tailCap : ℝ := 1/10^58
def transferCap : ℝ := 9 * (400000000000:ℝ)^2 / (50 * (Nat.factorial 99:ℝ))

theorem ledger_rounding : (0.999892775499:ℝ) ≤
    1 - 3*goodCap - 3*pairCap - 0.000107163 - tailCap - transferCap := by
  norm_num [goodCap,pairCap,tailCap,transferCap,ε,ν,Nat.factorial]

def upper (f : ℝ → ℝ) (c : ℝ) : Prop := ∀ e : ℝ, 0 < e → ∀ᶠ x : ℝ in atTop, f x ≤ (c+e)*Sb x

structure Estimates : Prop where
  goodMass : ∃ Jp : ℝ, Jp ≤ goodRational ∧ negligible (fun x => weighted compare positive x - Jp*Sb x) Sb ∧
    upper (weighted actual positive) (4*Jp)
  pairs : upper (deviation (omitted (· = 2))) (3*pairCap)
  four : upper (fun x => |deviation (omitted (· = 4)) x|) 0.000107163
  tail : upper (fun x => |deviation (omitted (256 ≤ ·)) x|) tailCap
  calibratedMean : upper (fun x => |deviation calibrated x|) transferCap
  comparator : negligible normalError Sb

/-- Output presieving is separate from the prime-power estimate on the input. -/
def OutputSupport : Prop := ∀ᶠ x : ℝ in atTop, ∀ n ∈ interval (x/2),
  Direct.phi x n ≠ 0 → Sifted (y x) n

theorem output_support (hgeom : ∀ᶠ x : ℝ in atTop, GeometryAt x) : OutputSupport := by
  filter_upwards [hgeom,Closing.log_power_lt_linear (a:=1/20) (b:=1/400000000000)
    (by norm_num) (by norm_num),eventually_gt_atTop (1:ℝ)] with x hg hlog hx n hn hne
  have hy : y x ≤ z x := by
    unfold y z
    rw [Real.rpow_def_of_pos (by linarith : 0<x),Real.exp_le_exp]
    linarith only [hlog]
  have hZ : Sifted (z x) n := by
    by_contra hno
    apply hne
    unfold Direct.phi Direct.F Direct.G
    simp only [hno,false_and,and_false,if_false,zero_sub,neg_eq_zero]
    split_ifs with h
    · have hzero : kernelH n = 0 := by
        by_contra hH
        exact hno ((hg.good n hn h.2.1 h.2.2).2 hH)
      simp [hzero]
    · rfl
  exact fun p hp hd => hy.trans_lt (hZ p hp hd)

theorem powerError_small (hs : ScaleLower) (hout : OutputSupport) : negligible powerError Sb := by
  have hp := negligible_comparator (prime_replacement
    (small_power (by norm_num : (1/800000000000:ℝ) ≤ 1/2)) native_power_mass) hs
  intro e he
  filter_upwards [hp e he,hout] with x h hx
  have heq : weighted actual Direct.phi x = primeSum x (Direct.phi x) := by
    unfold weighted primeSum total
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hzero : Direct.phi x n = 0
    · simp [hzero]
    · simp [actual,sieve,hx n hn hzero]
  simpa only [powerError,heq,intrinsicCut] using h

theorem lower_of_estimates (h : Estimates) (hs : ScaleLower) : Closing.LowerLedger := by
  obtain ⟨j,hj,hB,hA⟩ := h.goodMass
  intro e he
  have ht : 0 < e/8 := by linarith
  filter_upwards [geometry,comparator_pos hs,hB _ ht,hA _ ht,h.pairs _ ht,h.four _ ht,
    h.tail _ ht,h.calibratedMean _ ht,powerError_small hs (output_support geometry) _ ht,h.comparator _ ht]
    with x hg hpos hB hA hR h4 hT hW hP hC
  have hc := mul_le_mul_of_nonneg_right ledger_rounding hpos.le
  have hj' := mul_le_mul_of_nonneg_right (hj.trans good_cap_rounding.le) hpos.le
  linarith only [exact_ledger hg,hc,hj',(abs_le.mp hB).1,hA,hR,(abs_le.mp h4).2,
    (abs_le.mp hT).2,(abs_le.mp hW).1,(abs_le.mp hP).1,(abs_le.mp hC).2]

end
end REAL1B.FM.Ledger
#print axioms REAL1B.FM.Ledger.partition
#print axioms REAL1B.FM.Ledger.exact_ledger
#print axioms REAL1B.FM.Ledger.ledger_rounding
#print axioms REAL1B.FM.Ledger.powerError_small
#print axioms REAL1B.FM.Ledger.lower_of_estimates
#print axioms REAL1B.FM.Ledger.output_support
#print axioms REAL1B.FM.Ledger.H_prime
#print axioms REAL1B.FM.Ledger.K_prime
#print axioms REAL1B.FM.Ledger.geometry_of_good
#print axioms REAL1B.FM.Ledger.good_cap_rounding
#print axioms REAL1B.FM.Ledger.geometry
