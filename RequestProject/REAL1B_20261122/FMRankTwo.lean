import RequestProject.REAL1B_20261122.FMLowerLedger

/-! Gold 4.48 Appendix H and Gold 4.58 Part V §2. A marked divisor on the
physical window has three prime marks, a nontrivial general-integer cofactor,
and at least one more prime factor from its complementary divisor. -/
namespace REAL1B.FM.Ledger
open Source ArithmeticFunction Vaughan Filter
noncomputable section
open Classical

private theorem marked_rank {X : ℝ} (hX : 1<X) {n d u v w : ℕ}
    (hn : X < n) (hd : d ∣ n) (hu : u ∣ d) (hv : v ∣ d/u) (hw : w ∣ d/u/v)
    (pu : u.Prime) (pv : v.Prime) (pw : w.Prime)
    (bu : inBank X 0.0265 0.028 u) (bv : inBank X 0.0105 0.0115 v)
    (bw : inBank X 0.0115 0.0125 w) (bq : inBank X 0.463 0.465 (d/u/v/w)) :
    5 ≤ cardFactors n := by
  let q := d/u/v/w
  have hq : 1 < q := by
    exact_mod_cast (Real.one_lt_rpow hX (by norm_num : (0:ℝ)<0.463)).trans bq.1
  have deq : d = q*w*v*u := by
    dsimp [q]
    rw [Nat.div_mul_cancel hw,Nat.div_mul_cancel hv,Nat.div_mul_cancel hu]
  have hprod : (q:ℝ)*w*v*u ≤ X^((0.465:ℝ)+0.0125+0.0115+0.028) := by
    have hx : 0<X := by linarith
    simp only [Real.rpow_add hx]
    gcongr
    · exact bq.2
    · exact bw.2
    · exact bv.2
    · exact bu.2
  have hlt : d < n := by
    have hupper := Real.rpow_lt_rpow_of_exponent_lt hX
      (by norm_num : (0.465:ℝ)+0.0125+0.0115+0.028 < 1)
    rw [Real.rpow_one] at hupper
    rw [deq]
    exact_mod_cast (hprod.trans_lt hupper).trans hn
  obtain ⟨r, hr⟩ := hd
  have hrest : 1<r := by
    by_contra! h
    interval_cases r <;> simp_all
  have he : n=q*w*v*u*r := by rw [hr,← deq]
  have hu0 := pu.ne_zero
  have hv0 := pv.ne_zero
  have hw0 := pw.ne_zero
  have hq0 : q ≠ 0 := by omega
  rw [he,cardFactors_mul (by simp [hu0,hv0,hw0,hq0]) (by omega),cardFactors_mul (by simp [hv0,hw0,hq0]) pu.ne_zero,
    cardFactors_mul (by simp [hw0,hq0]) pv.ne_zero,cardFactors_mul (by omega) pw.ne_zero,
    cardFactors_apply_prime pu,cardFactors_apply_prime pv,cardFactors_apply_prime pw]
  have hqr := cardFactors_pos_iff_one_lt.mpr hq
  have hrr := cardFactors_pos_iff_one_lt.mpr hrest
  omega

/-- For every physical rank up to four, every marked contribution vanishes. -/
theorem low_rank_K_zero {X : ℝ} (hX : 1<X) {n : ℕ} (hn : X < n)
    (hr : cardFactors n ≤ 4) : kernelK X n = 0 := by
  have hz (d : ℕ) (hd : d ∈ n.divisors) : labels X d = 0 := by
    unfold labels
    apply Finset.sum_eq_zero
    intro u hu
    apply Finset.sum_eq_zero
    intro v hv
    apply Finset.sum_eq_zero
    intro w hw
    apply if_neg
    rintro ⟨pu,pv,pw,bu,bv,bw,bq⟩
    have hc := marked_rank hX hn (Nat.mem_divisors.mp hd).1 (Nat.mem_divisors.mp hu).1
      (Nat.mem_divisors.mp hv).1 (Nat.mem_divisors.mp hw).1 pu pv pw bu bv bw bq
    omega
  unfold kernelK
  rw [Finset.sum_eq_zero (fun d hd => by simp [hz d hd]),mul_zero]

/-- Above the lower edge the two prime coordinates admit the paper's rank
assignment (1,2). Both tiny costs are zero. -/
private theorem pair_good {n p q : ℕ} (hn : 1<n) (hf : n.primeFactorsList=[p,q])
    (hp : Direct.lowerEdge < Box.coord n p) (ho : Box.coord n p ≤ Box.coord n q)
    (hsum : Box.coord n p + Box.coord n q = 1) : Direct.good n := by
  have hnp : ¬n.Prime := by
    intro h
    have he := Nat.primeFactorsList_prime h
    rw [hf] at he
    simp at he
  refine ⟨hn,hnp,?_⟩
  change Direct.rankTest (fun i : Fin n.primeFactorsList.length => Box.coord n (n.primeFactorsList.get i))
  rw [hf]
  let r : Fin 2 → ℕ := ![1,2]
  have ha : (1:ℝ)/5 - Source.ε < Box.coord n p := hp
  have hε : 0<Source.ε := by norm_num [Source.ε]
  refine ⟨r, by change (∑ i : Fin 2, r i) ≤ 5; norm_num [r, Fin.sum_univ_two], ?_, ?_⟩
  · intro i _
    fin_cases i <;>
      norm_num [r,Direct.lowerEdge,Matrix.cons_val_zero,Matrix.cons_val_one] <;> linarith
  · change (∑ i : Fin 2, Direct.tinyCost (Box.coord n ([p,q].get i)) (r i)) < ε
    rw [Fin.sum_univ_two]
    have hz (t : ℝ) (k : ℕ) (hk : k ≠ 0) (h : t ≤ k * Direct.upperEdge) :
        Direct.tinyCost t k = 0 := by
      simp only [Direct.tinyCost, if_neg hk, max_eq_right (sub_nonpos.mpr h)]
    change Direct.tinyCost (Box.coord n p) 1 + Direct.tinyCost (Box.coord n q) 2 < ε
    rw [hz _ 1 (by decide) (by norm_num [Direct.upperEdge]; linarith),
        hz _ 2 (by decide) (by norm_num [Direct.upperEdge]; linarith)]
    simpa using hε

/-- At an off-good squarefree semiprime the native kernel equals the strip
indicator, including its lower and upper boundary conventions. -/
theorem pair_strip {n p q : ℕ} (hn : 1<n) (hs : Squarefree n)
    (hf : n.primeFactorsList=[p,q]) (hg : ¬ Direct.good n) :
    Source.kernelH n = if Source.ν ≤ Box.coord n p ∧ Box.coord n p ≤ Direct.lowerEdge then 1 else 0 := by
  have pp := Nat.prime_of_mem_primeFactorsList (n:=n) (p:=p) (by simp [hf])
  have pq := Nat.prime_of_mem_primeFactorsList (n:=n) (p:=q) (by simp [hf])
  have hsum := Collar.coordinate_sum hn
  simp [hf] at hsum
  have hpq : p≤q := by
    have hh := (Nat.primeFactorsList_sorted n).pairwise
    simpa [hf] using hh
  have ho : Box.coord n p ≤ Box.coord n q :=
    div_le_div_of_nonneg_right (Real.log_le_log (by exact_mod_cast pp.pos) (by exact_mod_cast hpq)) (Real.log_natCast_nonneg _)
  have hlow : Box.coord n p ≤ Direct.lowerEdge := le_of_not_gt (fun h => hg (pair_good hn hf h ho hsum))
  have lq : [q].Sublist n.primeFactorsList := by rw [hf]; exact List.sublist_cons_self _ _
  have lp : [p].Sublist n.primeFactorsList := by rw [hf]; exact List.Sublist.cons₂ _ (List.nil_sublist _)
  have lall : [p,q].Sublist n.primeFactorsList := by rw [hf]
  have hq : ¬ ((q:ℝ) ≤ (n:ℝ)^γ) := by
    intro h
    have hh := (Box.mass_cut hn lq).mp (by simpa using h)
    simp [Box.mass] at hh
    unfold γ ε at hh
    linarith
  have hfull : ¬ (((p*q:ℕ):ℝ) ≤ (n:ℝ)^γ) := by
    intro h
    have hh := (Box.mass_cut hn lall).mp (by simpa using h)
    simp [Box.mass,hsum] at hh
    norm_num [γ,ε] at hh
  have hp_cut : (p:ℝ) ≤ (n:ℝ)^γ := by
    have h : Box.mass n [p] ≤ γ := by
      simp [Box.mass]; unfold Direct.lowerEdge at hlow; unfold γ; linarith
    simpa using (Box.mass_cut hn lp).mpr h
  have h1 : divisorCoefficient n 1 = 1 := by
    have hp1 : (1:ℝ) ≤ (n:ℝ)^γ := Real.one_le_rpow (by exact_mod_cast (show 1≤n by omega)) (by norm_num [γ,ε])
    simp [divisorCoefficient,profile,g0,REAL1B.mu,hp1,show 0≤β by norm_num [β,ε]]
  have hq0 : divisorCoefficient n q = 0 := by simp [divisorCoefficient,hq]
  have hfull0 : divisorCoefficient n (p*q) = 0 := by simp only [divisorCoefficient, hfull, false_and, if_false]
  have hpeq : divisorCoefficient n p = if ν ≤ Box.coord n p then 0 else -1 := by
    have hnot : ¬((5:ℝ)⁻¹ < Box.coord n p) := by unfold Direct.lowerEdge ε at hlow; linarith
    by_cases hb : ν ≤ Box.coord n p
    · have h := (Box.cutoff_iff hn pp).mpr hb
      simp [divisorCoefficient,Nat.primeFactorsList_prime pp,not_lt.mpr h,h,Box.source_profile,g0,hnot,hb]
    · have h := lt_of_not_ge (fun hh => hb ((Box.cutoff_iff hn pp).mp hh))
      simp [divisorCoefficient,Nat.primeFactorsList_prime pp,not_le.mpr h,h,profile,g0,REAL1B.mu,
        ArithmeticFunction.moebius_apply_prime pp,hp_cut,hb,show 0≤β by norm_num [β,ε]]
  rw [Box.H_sublists hs,hf]
  simp [List.sublists'_cons,h1,hq0,hfull0,hpeq,hlow]
  split_ifs <;> norm_num

/-- Exact omitted two-prime weight on its physical window, with the output
presieve and both strip endpoints retained. -/
theorem omitted_pair_eq {x : ℝ} (hx : 4≤x) {n p q : ℕ} (hn : n ∈ interval (x/2))
    (hs : Squarefree n) (hf : n.primeFactorsList=[p,q]) :
    omitted (·=2) x n = if Sifted (z x) n ∧ ν ≤ Box.coord n p ∧ Box.coord n p ≤ Direct.lowerEdge
      then 1 else 0 := by
  have hwin := Analytic.window hn
  have hc : cardFactors n = 2 := by simp [cardFactors_apply,hf]
  have hK := low_rank_K_zero (by linarith : 1<x/2) hwin.1 (by omega : cardFactors n ≤ 4)
  by_cases hg : Direct.good n
  · have hmem : p ∈ n.primeFactorsList := by simp [hf]
    obtain ⟨hp,hd⟩ := (Nat.mem_primeFactorsList hs.ne_zero).mp hmem
    have hfalse : ¬(Sifted (z x) n ∧ ν ≤ Box.coord n p ∧ Box.coord n p ≤ Direct.lowerEdge) :=
      fun h => GoodSupport.gap_excluded hg hp hd
        ((by norm_num [ε,ν] : ε ≤ ν).trans h.2.1) h.2.2
    simp [omitted,hg,hfalse]
  · have hh := pair_strip (show 1<n from hwin.2.2) hs hf hg
    by_cases hz : Sifted (z x) n <;> simp [omitted,calibrated,hg,hc,hs,hz,hK,hh]

theorem pair_reference_bound : Collar.pairIntegral ν Direct.lowerEdge ≤ pairCap := by
  have h := (Collar.pair_band (l:=ν) (u:=Direct.lowerEdge)
    (by norm_num [ν,ε]) (by norm_num [ν,ε,Direct.lowerEdge]) (by norm_num [Direct.lowerEdge,ε])).2
  rwa [show Direct.lowerEdge-ν=ε by unfold Direct.lowerEdge ν; ring] at h

theorem pair_actual_nonneg {x : ℝ} (hx : 4≤x) : 0 ≤ weighted actual (omitted (·=2)) x := by
  unfold weighted total
  apply Finset.sum_nonneg
  intro n hn
  have ht : 0 ≤ theta (n-2) := by unfold theta; split_ifs <;> first | exact Real.log_natCast_nonneg _ | rfl
  apply mul_nonneg (show 0 ≤ actual x n by unfold actual sieve; split_ifs <;> positivity)
  by_cases hc : cardFactors n = 2
  · by_cases hs : Squarefree n
    · have hl : n.primeFactorsList.length=2 := hc
      obtain ⟨p,q,hf⟩ : ∃ p q, n.primeFactorsList=[p,q] := by
        rcases he : n.primeFactorsList with _ | ⟨p,l⟩ <;> simp [he] at hl
        rcases l with _ | ⟨q,l⟩ <;> simp_all
      rw [omitted_pair_eq hx hn hs hf]
      split_ifs <;> norm_num
    · simp [omitted,calibrated,hs]
  · simp [omitted,hc]

/-- The lower side of the signed pair estimate follows from the comparator
upper alone because the original actual pair weight is nonnegative. -/
theorem lower_pair_of_comparator (h : upper (weighted compare (omitted (·=2))) pairCap) :
    upper (fun x => -deviation (omitted (·=2)) x) pairCap := by
  intro e he
  filter_upwards [Filter.eventually_ge_atTop (4:ℝ), h e he] with x hx hc
  dsimp [deviation]
  linarith only [pair_actual_nonneg hx,hc]

end
end REAL1B.FM.Ledger
#print axioms REAL1B.FM.Ledger.low_rank_K_zero
#print axioms REAL1B.FM.Ledger.pair_strip
#print axioms REAL1B.FM.Ledger.omitted_pair_eq
#print axioms REAL1B.FM.Ledger.pair_reference_bound
#print axioms REAL1B.FM.Ledger.pair_actual_nonneg
#print axioms REAL1B.FM.Ledger.lower_pair_of_comparator
