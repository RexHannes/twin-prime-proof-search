import RequestProject.REAL1B_20261122.FMBoxDivisors

/-! Gold 4.55 Part I, Propositions 1–2. Complete the small-prime Möbius
sum on the actual good set before applying any source-distribution estimate. -/
namespace REAL1B.FM.GoodSupport
open Filter Source Vaughan Analytic Box
noncomputable section
open Classical

def small (n p : ℕ) := decide ((p:ℝ) < (n:ℝ)^ν)

private theorem mass_filter (n : ℕ) (s : ℕ → Bool) (l : List ℕ) :
    Box.mass n (l.filter s) = (l.map (fun p => if s p then coord n p else 0)).sum := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    by_cases h : s p <;> simp [Box.mass,h] at ih ⊢ <;> exact ih

private theorem both_mass (n : ℕ) (s : ℕ → Bool) (l : List ℕ) :
    Box.mass n l = Box.mass n (l.filter s) + Box.mass n (l.filter (fun p => !s p)) := by
  induction l with
  | nil => simp [Box.mass]
  | cons p l ih => by_cases h : s p <;> simp [Box.mass,h] at ih ⊢ <;> linarith only [ih]

theorem tiny_budget {n : ℕ} (hg : Direct.good n) {l : List ℕ} (hl : l.Sublist n.primeFactorsList) :
    Box.mass n (l.filter (small n)) < ε := by
  obtain ⟨hn,_,r,_,hr,hc⟩ := hg
  let f := fun p : ℕ => if small n p then coord n p else 0
  have local_le (i : Fin n.primeFactorsList.length) : f (n.primeFactorsList.get i) ≤
      Direct.tinyCost (coord n (n.primeFactorsList.get i)) (r i) := by
    let p := n.primeFactorsList.get i
    have hp : p.Prime := Nat.prime_of_mem_primeFactorsList (List.get_mem _ _)
    have hpos : 0 ≤ coord n p := div_nonneg (Real.log_natCast_nonneg _) (Real.log_natCast_nonneg _)
    by_cases h : small n p
    · have hp' : (p:ℝ) < (n:ℝ)^ν := of_decide_eq_true h
      have ht : coord n p < ν := lt_of_not_ge (fun ht => (not_le.mpr hp') ((cutoff_iff hn hp).mpr ht))
      have hz : r i = 0 := by
        by_contra he
        have h₁ : (1:ℝ) ≤ r i := by exact_mod_cast (show 1 ≤ r i by omega)
        have h₂ := hr i (by omega)
        change _ < coord n p at h₂
        have hb : 0 ≤ Direct.lowerEdge := by norm_num [Direct.lowerEdge,ε]
        have h₃ := mul_le_mul_of_nonneg_right h₁ hb
        simp only [Direct.lowerEdge,ν,ε] at h₂ ht h₃
        linarith only [h₂,ht,h₃]
      change (if small n p then coord n p else 0) ≤ Direct.tinyCost (coord n p) _
      simp [h,Direct.tinyCost,hz]
    · change (if small n p then coord n p else 0) ≤ Direct.tinyCost (coord n p) _
      simp only [if_neg h,Direct.tinyCost]
      split_ifs <;> first | exact hpos | exact le_max_right _ _
  have allmass : (n.primeFactorsList.map f).sum < ε := by
    have hh := (Finset.sum_le_sum (fun i _ => local_le i)).trans_lt hc
    rw [← List.sum_ofFn] at hh
    have hmap := (List.map_ofFn n.primeFactorsList.get f).symm
    rw [List.ofFn_get] at hmap
    change (List.ofFn (f ∘ n.primeFactorsList.get)).sum < ε at hh
    rw [hmap] at hh
    exact hh
  rw [mass_filter]
  apply lt_of_le_of_lt _ allmass
  apply (hl.map f).sum_le_sum
  intro y hy
  obtain ⟨p,_,rfl⟩ := List.mem_map.mp hy
  dsimp only [f]
  split_ifs
  · exact div_nonneg (Real.log_natCast_nonneg _) (Real.log_natCast_nonneg _)
  · rfl

def signedWeight {α : Type} (s : α → Bool) (g : List α → ℝ) (l : List α) :=
  (-1:ℝ)^(l.filter s).length * g (l.filter (fun a => !s a))

private theorem complete_cancel {α : Type} (s : α → Bool) (L : List α)
    (h : ∃ p ∈ L, s p = true) (g : List α → ℝ) :
    (L.sublists'.map (signedWeight s g)).sum = 0 := by
  induction L generalizing g with
  | nil => simp at h
  | cons p L ih =>
    rw [List.sublists'_cons,List.map_append,List.sum_append,List.map_map]
    by_cases hs : s p
    · have hn (l : List α) : (signedWeight s g ∘ List.cons p) l = -signedWeight s g l := by
        simp [signedWeight,hs,pow_succ]
      rw [show (signedWeight s g ∘ List.cons p) = (fun l => -signedWeight s g l) from funext hn]
      have negmap (A : List (List α)) : (A.map (fun l => -signedWeight s g l)).sum =
          -(A.map (signedWeight s g)).sum := by
        induction A with
        | nil => simp
        | cons a A ih => simp [ih,add_comm]
      rw [negmap,add_neg_cancel]
    · obtain ⟨q,hq,hb⟩ := h
      have htail : ∃ q ∈ L, s q = true := by
        rcases List.mem_cons.mp hq with rfl | hmem
        · exact False.elim (hs hb)
        · exact ⟨q,hmem,hb⟩
      have hn (l : List α) : (signedWeight s g ∘ List.cons p) l = signedWeight s (fun t => g (p::t)) l := by
        simp [signedWeight,hs]
      rw [show (signedWeight s g ∘ List.cons p) = _ from funext hn,ih htail,ih htail,zero_add]

def bigWeight (n : ℕ) (l : List ℕ) := if Box.mass n l ≤ β then g0 (l.map (coord n)) else 0

theorem native_factorization {n : ℕ} (hs : Squarefree n) (hg : Direct.good n) {l : List ℕ}
    (hl : l.Sublist n.primeFactorsList) :
    divisorCoefficient n l.prod = signedWeight (small n) (bigWeight n) l := by
  have ht := tiny_budget hg hl
  have hmass := both_mass n (small n) l
  have hB : (fun p : ℕ => decide ((n:ℝ)^ν ≤ (p:ℝ))) = fun p => !(small n p) := by
    funext p
    by_cases h : (p:ℝ) < (n:ℝ)^ν <;> simp [small,h,not_le.mpr,le_of_not_gt]
  unfold divisorCoefficient
  simp only [recover hl,source_profile,hB]
  change (if (l.prod:ℝ) ≤ (n:ℝ)^γ ∧ Box.mass n (l.filter (fun p => !(small n p))) ≤ β then
    mu (l.filter (small n)).prod * g0 ((l.filter (fun p => !(small n p))).map (coord n)) else 0) = _
  rw [mu_sublist hs (List.filter_sublist.trans hl)]
  unfold signedWeight bigWeight
  by_cases hb : Box.mass n (l.filter (fun p => !(small n p))) ≤ β
  · have hh : (l.prod:ℝ) ≤ (n:ℝ)^γ := (mass_cut hg.1 hl).mpr (by unfold γ; unfold β at hb; linarith only [hmass,ht,hb])
    simp only [hh,hb,and_self,if_true]
  · simp only [hb,and_false,if_false,mul_zero]

theorem small_prime_cancels {n : ℕ} (hs : Squarefree n) (hg : Direct.good n)
    {p : ℕ} (hp : p.Prime) (hd : p ∣ n) (hsmall : (p:ℝ) < (n:ℝ)^ν) : kernelH n = 0 := by
  rw [H_sublists hs]
  have hh : n.primeFactorsList.sublists'.map (fun l => divisorCoefficient n l.prod) =
      n.primeFactorsList.sublists'.map (signedWeight (small n) (bigWeight n)) :=
    List.map_congr_left (fun l hl => native_factorization hs hg (List.mem_sublists'.mp hl))
  rw [hh]
  exact complete_cancel _ _ ⟨p,(Nat.mem_primeFactorsList hs.ne_zero).mpr ⟨hp,hd⟩,decide_eq_true hsmall⟩ _

theorem gap_excluded {n p : ℕ} (hg : Direct.good n) (hp : p.Prime) (hd : p ∣ n)
    (lo : ε ≤ coord n p) (hi : coord n p ≤ Direct.lowerEdge) : False := by
  obtain ⟨hn,_,hr⟩ := hg
  obtain ⟨i,he⟩ := List.mem_iff_get.mp ((Nat.mem_primeFactorsList (by omega)).mpr ⟨hp,hd⟩)
  apply rank_gap (t:=fun j => coord n (n.primeFactorsList.get j))
    (fun _ => div_nonneg (Real.log_natCast_nonneg _) (Real.log_natCast_nonneg _)) (i:=i) _ _ hr
  · change ε ≤ coord n (n.primeFactorsList.get i)
    rwa [he]
  · change coord n (n.primeFactorsList.get i) ≤ Direct.lowerEdge
    rwa [he]

theorem marked_zero {x : ℝ} (hx : 4 ≤ x) {n : ℕ} (hn : n ∈ interval (x/2)) (hg : Direct.good n) :
    kernelK (x/2) n = 0 := by
  obtain ⟨hnX,hnx,_⟩ := window hn
  have hX : 0 < x/2 := by linarith
  have hlog := Real.log_pos (by exact_mod_cast hg.1 : (1:ℝ)<n)
  have hupper := Real.log_le_log (by exact_mod_cast (Nat.zero_lt_of_lt hg.1) : (0:ℝ)<n) hnx
  have hlower := Real.log_le_log hX hnX.le
  have h₂ := Real.log_le_log (by norm_num : (0:ℝ)<2) (by linarith : 2 ≤ x/2)
  have hsplit : Real.log x = Real.log 2 + Real.log (x/2) := by
    rw [← Real.log_mul (by norm_num : (2:ℝ) ≠ 0) hX.ne']; congr 1; ring
  have no_label (d : ℕ) (hd : d ∈ n.divisors) : labels (x/2) d = 0 := by
    unfold labels
    apply Finset.sum_eq_zero
    intro p hp
    apply Finset.sum_eq_zero
    intro _ _
    apply Finset.sum_eq_zero
    intro _ _
    apply if_neg
    rintro ⟨hprime,_,_,hbank,_⟩
    have h₁ := Real.log_lt_log (Real.rpow_pos_of_pos hX _) hbank.1
    have h₃ := Real.log_le_log (by exact_mod_cast hprime.pos) hbank.2
    rw [Real.log_rpow hX] at h₁ h₃
    apply gap_excluded hg hprime ((Nat.mem_divisors.mp hp).1.trans (Nat.mem_divisors.mp hd).1)
    · apply (le_div_iff₀ hlog).mpr
      unfold ε; linarith only [h₁,hupper,h₂,hsplit,hlog]
    · apply (div_le_iff₀ hlog).mpr
      unfold Direct.lowerEdge ε; linarith only [h₃,hlower,hlog]
  unfold kernelK
  rw [Finset.sum_eq_zero (fun d hd => by simp [no_label d hd]),mul_zero]

theorem active_rough {x : ℝ} (hx : 4 ≤ x) {n : ℕ} (hn : n ∈ interval (x/2))
    (hs : Squarefree n) (hg : Direct.good n) (hH : kernelH n ≠ 0) : Sifted (z x) n := by
  intro p hp hd
  have h₁ : (n:ℝ)^ν ≤ p := le_of_not_gt (fun h => hH (small_prime_cancels hs hg hp hd h))
  have hwin := (window hn).1
  have hnpos : (0:ℝ)<n := by exact_mod_cast (Nat.zero_lt_of_lt hg.1)
  have hL := Real.log_pos (by exact_mod_cast hg.1 : (1:ℝ)<n)
  have h₂ := Real.log_le_log (by norm_num : (0:ℝ)<2) (by linarith : 2 ≤ (n:ℝ))
  have hh := Real.log_le_log (by linarith : 0<x) (by linarith : x ≤ 2*(n:ℝ))
  rw [Real.log_mul (by norm_num) hnpos.ne'] at hh
  apply lt_of_lt_of_le _ h₁
  rw [z,Real.rpow_def_of_pos (by linarith : 0<x),Real.rpow_def_of_pos hnpos,Real.exp_lt_exp]
  unfold ν ε; linarith only [h₂,hh,hL]

end
end REAL1B.FM.GoodSupport
#print axioms REAL1B.FM.GoodSupport.tiny_budget
#print axioms REAL1B.FM.GoodSupport.native_factorization
#print axioms REAL1B.FM.GoodSupport.small_prime_cancels
#print axioms REAL1B.FM.GoodSupport.marked_zero
#print axioms REAL1B.FM.GoodSupport.active_rough
