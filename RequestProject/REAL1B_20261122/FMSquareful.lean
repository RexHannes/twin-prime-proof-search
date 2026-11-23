import RequestProject.REAL1B_20261122.FMUniform

/-! Count the divisor weight on rough nonsquarefree inputs before using the signed
Vaughan decomposition. All multiplicities are charged on the full input. -/
namespace REAL1B.FM.Squareful
open Filter Source Vaughan Analytic Finset
open scoped Pointwise
noncomputable section
open Classical

private theorem divisors_sum (N : ℕ) :
    (∑ k ∈ Ioc 0 N, (k.divisors.card : ℝ)) ≤ (N:ℝ)*(1+Real.log N) := by
  let I := Ioc 0 N
  have hd (k : ℕ) (hk : k ∈ I) : I.filter (· ∣ k) = k.divisors := by
    ext d
    have ⟨hk₀,hk₁⟩ := mem_Ioc.mp hk
    simp only [I,mem_filter,mem_Ioc,Nat.mem_divisors]
    constructor
    · rintro ⟨_,h⟩; exact ⟨h,hk₀.ne'⟩
    · rintro ⟨h,_⟩; exact ⟨⟨Nat.pos_of_dvd_of_pos h hk₀,(Nat.le_of_dvd hk₀ h).trans hk₁⟩,h⟩
  have count (s : Finset ℕ) (P : ℕ → Prop) [DecidablePred P] :
      ((s.filter P).card:ℝ) = ∑ k ∈ s, if P k then (1:ℝ) else 0 := by
    rw [← sum_filter]; simp
  have hi : I = Icc 1 N := by ext d; simp [I]; omega
  calc
    _ = ∑ k ∈ I, ∑ d ∈ I, if d ∣ k then (1:ℝ) else 0 := sum_congr rfl (fun k hk => by rw [← hd k hk,count])
    _ = ∑ d ∈ I, (↑(N/d):ℝ) := by
      rw [sum_comm]; apply sum_congr rfl; intro d _
      rw [← count, Nat.Ioc_filter_dvd_card_eq_div]
    _ ≤ ∑ d ∈ I, (N:ℝ) * (d:ℝ)⁻¹ := sum_le_sum (fun d _ => by simpa [div_eq_mul_inv] using (Nat.cast_div_le (m:=N) (n:=d) (α:=ℝ)))
    _ = (N:ℝ)*(harmonic N:ℝ) := by rw [← mul_sum,hi,harmonic_eq_sum_Icc]; push_cast; rfl
    _ ≤ _ := mul_le_mul_of_nonneg_left (harmonic_le_one_add_log N) (Nat.cast_nonneg _)

private theorem multiple_cost {N p : ℕ} (hp : p.Prime) :
    (∑ k ∈ (Ioc 0 N).filter (fun k => p^2 ∣ k), (k.divisors.card:ℝ)) ≤
      3*(N:ℝ)*(1+Real.log N)/(p:ℝ)^2 := by
  let u := p^2
  have hu : 0<u := pow_pos hp.pos _
  have hcard : u.divisors.card = 3 := by simp [u,Nat.divisors_prime_pow hp]
  have hτ (m : ℕ) : ((u*m).divisors.card:ℝ) ≤ 3*(m.divisors.card:ℝ) := by
    exact_mod_cast (show (u*m).divisors.card ≤ 3*m.divisors.card by rw [Nat.divisors_mul,← hcard]; exact card_mul_le)
  have hset : ((Ioc 0 N).filter (fun k => u ∣ k)) = (Ioc 0 (N/u)).image (fun m => u*m) := by
    ext k
    simp only [mem_filter,mem_image,mem_Ioc]
    constructor
    · rintro ⟨⟨hk,hN⟩,m,rfl⟩
      exact ⟨m,⟨Nat.pos_of_mul_pos_left hk,(Nat.le_div_iff_mul_le hu).mpr (by simpa [Nat.mul_comm] using hN)⟩,rfl⟩
    · rintro ⟨m,⟨hm,hM⟩,rfl⟩
      exact ⟨⟨Nat.mul_pos hu hm,by simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hu).mp hM⟩,dvd_mul_right _ _⟩
  change (∑ k ∈ (Ioc 0 N).filter (fun k => u ∣ k), _) ≤ _
  rw [hset,sum_image (fun _ _ _ _ h => Nat.eq_of_mul_eq_mul_left hu h)]
  calc
    _ ≤ ∑ m ∈ Ioc 0 (N/u), 3*(m.divisors.card:ℝ) := sum_le_sum (fun m _ => hτ m)
    _ ≤ 3*((N/u:ℕ):ℝ)*(1+Real.log (N/u:ℕ)) := by rw [← mul_sum,mul_assoc]; exact mul_le_mul_of_nonneg_left (divisors_sum _) (by norm_num)
    _ ≤ 3*((N:ℝ)/(u:ℝ))*(1+Real.log N) := by
      have hl : Real.log (N/u:ℕ) ≤ Real.log N := by
        by_cases hz : N/u = 0
        · simpa [hz] using Real.log_natCast_nonneg N
        · exact Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hz) (by exact_mod_cast Nat.div_le_self N u)
      apply mul_le_mul _ (by linarith only [hl]) (by linarith only [Real.log_natCast_nonneg (N/u)]) (by positivity)
      exact mul_le_mul_of_nonneg_left Nat.cast_div_le (by norm_num)
    _ = _ := by dsimp [u]; push_cast; ring

private theorem reciprocal_tail {D : ℕ} (hd : 0<D) (N : ℕ) :
    (∑ p ∈ Ioc D N, 1/(p:ℝ)^2) ≤ 1/(D:ℝ) := by
  by_cases h : D ≤ N
  · suffices (∑ p ∈ Ioc D N, 1/(p:ℝ)^2) + 1/(N:ℝ) ≤ 1/(D:ℝ) by
      linarith only [this,show 0 ≤ 1/(N:ℝ) by positivity]
    induction N, h using Nat.le_induction with
    | base => simp
    | succ n hn ih =>
      rw [sum_Ioc_succ_top hn]
      push_cast
      have hn' : (0:ℝ)<n := by exact_mod_cast hd.trans_le hn
      have hh : 1/((n:ℝ)+1)^2 + 1/((n:ℝ)+1) ≤ 1/(n:ℝ) := by
        field_simp; nlinarith
      linarith
  · rw [Ioc_eq_empty_of_le (by omega),sum_empty]; positivity

def bad (D k : ℕ) : Prop := ¬Squarefree k ∧ ∀ p, p.Prime → p ∣ k → D < p

theorem rough_divisor_mass (D N : ℕ) (hd : 0<D) :
    (∑ k ∈ Ioc 0 N, if bad D k then (k.divisors.card:ℝ) else 0) ≤
      3*(N:ℝ)*(1+Real.log N)/(D:ℝ) := by
  let P := (Ioc D N).filter Nat.Prime
  let C := 3*(N:ℝ)*(1+Real.log N)
  have hc : 0 ≤ C := by dsimp [C]; positivity
  have count (k : ℕ) (hk : k ∈ Ioc 0 N) :
      (if bad D k then (k.divisors.card:ℝ) else 0) ≤
        ∑ p ∈ P, if p^2 ∣ k then (k.divisors.card:ℝ) else 0 := by
    have hn (p : ℕ) : 0 ≤ (if p^2 ∣ k then (k.divisors.card:ℝ) else 0) := by split_ifs <;> positivity
    split_ifs with h
    · have hnq := h.1
      rw [Nat.squarefree_iff_prime_squarefree] at hnq
      push_neg at hnq
      obtain ⟨p,hp,hp₂⟩ := hnq
      have hpk := (dvd_mul_right p p).trans hp₂
      have hP : p ∈ P := mem_filter.mpr ⟨mem_Ioc.mpr ⟨h.2 p hp hpk,(Nat.le_of_dvd (mem_Ioc.mp hk).1 hpk).trans (mem_Ioc.mp hk).2⟩,hp⟩
      have hpp : p^2 ∣ k := by simpa [pow_two] using hp₂
      simpa only [if_pos hpp] using single_le_sum (s:=P) (f:=fun p => if p^2 ∣ k then (k.divisors.card:ℝ) else 0) (fun i _ => hn i) hP
    · exact sum_nonneg (fun p _ => hn p)
  calc
    _ ≤ ∑ k ∈ Ioc 0 N, ∑ p ∈ P, if p^2 ∣ k then (k.divisors.card:ℝ) else 0 := sum_le_sum count
    _ ≤ ∑ p ∈ P, C*(1/(p:ℝ)^2) := by
      rw [sum_comm]; apply sum_le_sum; intro p hp
      rw [← sum_filter]; simpa [C,div_eq_mul_inv] using multiple_cost (N:=N) (mem_filter.mp hp).2
    _ ≤ C*(1/(D:ℝ)) := by
      rw [← mul_sum]; apply mul_le_mul_of_nonneg_left _ hc
      exact (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => by positivity)).trans (reciprocal_tail hd N)
    _ = _ := by simp [C,div_eq_mul_inv]


theorem physical_bound {a x B : ℝ} {f : ℝ → ℕ → ℝ} (hx : 8 ≤ x) (hB : 0 ≤ B)
    (hf : ∀ n ∈ interval (x/2), |f x n| ≤ B) (hd : 0 < ⌊Closing.roughW a x⌋₊) :
    squarefulMass a x (f x) ≤ 6*B*x*(Real.log x)*(1+Real.log x)/⌊Closing.roughW a x⌋₊ := by
  let D := ⌊Closing.roughW a x⌋₊
  let N := ⌊x⌋₊
  let M (k : ℕ) : ℝ := if bad D k then k.divisors.card else 0
  let I := interval (x/2)
  have hlog : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hN : (N:ℝ) ≤ x := Nat.floor_le (by linarith)
  have hW : 0 ≤ Closing.roughW a x := (Real.exp_pos _).le
  have hpos (n : ℕ) (hn : n ∈ I) : 0 < n-2 := by
    have hh := (window hn).1
    exact Nat.sub_pos_of_lt (by exact_mod_cast (show (2:ℝ)<n by linarith))
  have hNlog : Real.log (N:ℝ) ≤ Real.log x := Real.log_le_log
    (by exact_mod_cast (show 0<N from Nat.floor_pos.mpr (by linarith))) hN
  have nonneg (k : ℕ) : 0 ≤ M k := by dsimp [M]; split_ifs <;> positivity
  have hsub : I.image (fun n : ℕ => n-2) ⊆ Ioc 0 N := by
    intro k hk
    obtain ⟨n,hn,rfl⟩ := mem_image.mp hk
    exact mem_Ioc.mpr ⟨hpos n hn,(Nat.sub_le _ _).trans (Nat.le_floor (window hn).2.1)⟩
  have hinj : Set.InjOn (fun n : ℕ => n-2) (I : Set ℕ) := by
    intro m hm n hn he
    have := hpos m hm; have := hpos n hn
    change m-2 = n-2 at he
    omega
  have hsum : (∑ n ∈ I, M (n-2)) ≤ 3*(N:ℝ)*(1+Real.log N)/(D:ℝ) := by
    rw [← sum_image hinj]
    exact (sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => nonneg k)).trans (rough_divisor_mass D N hd)
  have hpt (n : ℕ) (hn : n ∈ I) :
      sieve (Closing.roughW a x) (n-2) * (if Squarefree (n-2) then 0 else 2*((n-2).divisors.card:ℝ)*Real.log (n-2:ℕ)) * |f x n|
      ≤ (2*B*Real.log x)*M (n-2) := by
    have rhs : 0 ≤ (2*B*Real.log x)*M (n-2) := by have := nonneg (n-2); positivity
    by_cases hs : Sifted (Closing.roughW a x) (n-2)
    · by_cases hsq : Squarefree (n-2)
      · simpa [sieve,hs,hsq] using rhs
      · have hh : bad D (n-2) := ⟨hsq,fun p hp hdiv => by
          exact_mod_cast ((Nat.floor_le hW).trans_lt (hs p hp hdiv) : (D:ℝ)<p)⟩
        have hl : Real.log (n-2:ℕ) ≤ Real.log x := Real.log_le_log
          (by exact_mod_cast hpos n hn) ((by exact_mod_cast Nat.sub_le n 2 : ((n-2:ℕ):ℝ) ≤ n).trans (window hn).2.1)
        simp only [M,hh,if_true,sieve,hs,hsq,if_false,one_mul]
        calc
          _ ≤ 2*((n-2).divisors.card:ℝ)*Real.log x * B := mul_le_mul
            (mul_le_mul_of_nonneg_left hl (by positivity)) (hf n hn) (abs_nonneg _) (by positivity)
          _ = _ := by ring
    · simpa [sieve,hs] using rhs
  calc
    _ ≤ ∑ n ∈ I, (2*B*Real.log x)*M (n-2) := sum_le_sum hpt
    _ ≤ (2*B*Real.log x)*(3*(N:ℝ)*(1+Real.log N)/(D:ℝ)) := by
      rw [← mul_sum]; exact mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ (2*B*Real.log x)*(3*x*(1+Real.log x)/(D:ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      exact mul_le_mul (mul_le_mul_of_nonneg_left hN (by norm_num)) (by linarith) (by linarith only [Real.log_natCast_nonneg N]) (by linarith)
    _ = _ := by ring

theorem presieve_dominates {a : ℝ} (ha : 0<a) {e : ℝ} (he : 0<e) :
    ∀ᶠ x : ℝ in atTop, (Real.log x)^3 ≤ e*(⌊Closing.roughW a x⌋₊:ℝ) := by
  have hlim := (tendsto_rpow_atTop ha).comp Real.tendsto_log_atTop
  have hh := ((isLittleO_rpow_exp_atTop (3/a)).comp_tendsto hlim).bound (show 0<e/2 by linarith)
  have hw := (Real.tendsto_exp_atTop.comp hlim).eventually_ge_atTop 2
  filter_upwards [hh,hw,eventually_gt_atTop (1:ℝ)] with x ht hw hx
  have hl := Real.log_pos hx
  change ‖(Real.log x ^ a)^(3/a)‖ ≤ e/2 * ‖Closing.roughW a x‖ at ht
  rw [← Real.rpow_mul hl.le,show a*(3/a)=3 by field_simp,Real.rpow_ofNat,
    Real.norm_eq_abs,abs_of_pos (pow_pos hl _),Real.norm_eq_abs,abs_of_pos (show 0<Closing.roughW a x from Real.exp_pos _)] at ht
  change 2 ≤ Closing.roughW a x at hw
  have hf := Nat.lt_floor_add_one (Closing.roughW a x)
  linarith only [ht,mul_le_mul_of_nonneg_left (show Closing.roughW a x/2 ≤ (⌊Closing.roughW a x⌋₊:ℝ) by linarith) he.le]

theorem negligible_of_bounded {a B : ℝ} {f : ℝ → ℕ → ℝ} (ha : 0<a) (hB : 0<B)
    (hf : ∀ x n, |f x n| ≤ B) : negligible (fun x => squarefulMass a x (f x)) scale := by
  intro e he
  have hL := Real.tendsto_log_atTop.eventually_ge_atTop 1
  filter_upwards [presieve_dominates ha (show 0 < e/(12*B) by positivity),hL,eventually_ge_atTop (8:ℝ)] with x hlog hl hx
  have hD : 0 < ⌊Closing.roughW a x⌋₊ := Nat.floor_pos.mpr (Real.one_le_exp (by positivity))
  have hDn : (0:ℝ)<⌊Closing.roughW a x⌋₊ := by exact_mod_cast hD
  have hh := physical_bound hx hB.le (fun n _ => hf x n) hD
  have hnon : 0 ≤ squarefulMass a x (f x) := by
    unfold squarefulMass weightedInput total
    apply sum_nonneg; intro n _
    unfold sieve; split_ifs <;> positivity
  rw [abs_of_nonneg hnon]
  apply hh.trans
  unfold scale
  have hl' : 0 < Real.log x := by linarith
  have ha' : 12*B*(Real.log x)^3 ≤ e*(⌊Closing.roughW a x⌋₊:ℝ) := by
    convert mul_le_mul_of_nonneg_left hlog (show 0 ≤ 12*B by positivity) using 1
    field_simp
  have haux : 6*B*(Real.log x)^2*(1+Real.log x) ≤ 12*B*(Real.log x)^3 := by
    nlinarith only [mul_nonneg (show 0 ≤ 6*B*(Real.log x)^2 by positivity) (sub_nonneg.mpr hl)]
  apply (div_le_iff₀ hDn).mpr
  rw [show e*(x/Real.log x)*(⌊Closing.roughW a x⌋₊:ℝ) = (x*(e*(⌊Closing.roughW a x⌋₊:ℝ)))/Real.log x by ring]
  apply (le_div_iff₀ hl').mpr
  nlinarith only [mul_le_mul_of_nonneg_left (haux.trans ha') (by linarith : 0 ≤ x)]

theorem native_squareful {a : ℝ} (ha : 0<a) (hs : ScaleLower) :
    negligible (fun x => squarefulMass a x (Direct.phi x)) Sb :=
  negligible_comparator (negligible_of_bounded ha (by positivity) GoodSupport.uniform_phi) hs

theorem box_squareful {a : ℝ} (ha : 0<a) (hs : ScaleLower) :
    negligible (fun x => squarefulMass a x (Direct.psi x)) Sb :=
  negligible_comparator (negligible_of_bounded ha (by positivity) GoodSupport.uniform_psi) hs

end
end REAL1B.FM.Squareful
#print axioms REAL1B.FM.Squareful.rough_divisor_mass
#print axioms REAL1B.FM.Squareful.physical_bound
#print axioms REAL1B.FM.Squareful.presieve_dominates
#print axioms REAL1B.FM.Squareful.negligible_of_bounded
#print axioms REAL1B.FM.Squareful.native_squareful
#print axioms REAL1B.FM.Squareful.box_squareful
