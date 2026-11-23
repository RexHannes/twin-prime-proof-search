import RequestProject.REAL1B_20261122.FMUniform

/-! The active good-set kernel in normalized prime coordinates, with its strict
and weak endpoints as in Gold 4.58 Part V §9. -/
namespace REAL1B.FM.Collar
open Source Analytic Box GoodSupport
noncomputable section
open Classical

def term (v : List ℝ) : ℝ := if v.sum ≤ β then g0 v else 0
def profileSum (v : List ℝ) := (v.sublists'.map term).sum
def single (x : ℝ) : ℝ := if 1/5<x ∧ x≤β then 1 else 0
def pair (x y : ℝ) : ℝ := if 1/5<x ∧ 1/5<y ∧ x+y≤β then 1 else 0

private theorem map_subsets {α β : Type} (f : α → β) (l : List α) :
    (l.map f).sublists' = l.sublists'.map (List.map f) := by
  induction l with
  | nil => rfl
  | cons p l ih => simp [List.sublists'_cons,ih,List.map_map,Function.comp_def]

theorem active_coordinate {n : ℕ} (hs : Squarefree n) (hg : Direct.good n) (hH : kernelH n ≠ 0)
    {p : ℕ} (hp : p ∈ n.primeFactorsList) : Direct.lowerEdge < coord n p := by
  obtain ⟨hprime,hd⟩ := (Nat.mem_primeFactorsList hs.ne_zero).mp hp
  have hc := (cutoff_iff hg.1 hprime).mp (le_of_not_gt (fun h => hH (small_prime_cancels hs hg hprime hd h)))
  apply lt_of_not_ge; intro hh
  exact gap_excluded hg hprime hd (le_trans (by norm_num [ν,ε]) hc) hh

theorem active_kernel {n : ℕ} (hs : Squarefree n) (hg : Direct.good n) (hH : kernelH n ≠ 0) :
    kernelH n = profileSum (n.primeFactorsList.map (coord n)) := by
  rw [H_sublists hs,profileSum,map_subsets,List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro l hl
  have sub := List.mem_sublists'.mp hl
  have hall (p : ℕ) (hp : p ∈ l) : small n p = false := by
    apply Bool.eq_false_iff.mpr
    intro ht
    have hh : (p:ℝ) < (n:ℝ)^ν := of_decide_eq_true ht
    obtain ⟨hprime,hd⟩ := (Nat.mem_primeFactorsList hs.ne_zero).mp (sub.subset hp)
    exact hH (small_prime_cancels hs hg hprime hd hh)
  have hempty : l.filter (small n) = [] := List.filter_eq_nil_iff.mpr (fun p hp => by simp [hall p hp])
  have hfull : l.filter (fun p => !small n p) = l := List.filter_eq_self.mpr (fun p hp => by simp [hall p hp])
  rw [native_factorization hs hg sub]
  simp [signedWeight,bigWeight,hempty,hfull,term,Box.mass]

theorem coordinate_sum {n : ℕ} (hn : 1<n) : (n.primeFactorsList.map (coord n)).sum = 1 := by
  change Box.mass _ _ = 1
  rw [log_mass (.refl _),Nat.prod_primeFactorsList (by omega),div_self (Real.log_pos (by exact_mod_cast hn)).ne']

@[simp] private theorem term_empty : term [] = 1 := by norm_num [term,β,ε,g0]
@[simp] private theorem term_one (a : ℝ) : term [a] = -single a := by
  simp [term,g0,single]
  norm_num [β,ε] at *
  grind
@[simp] private theorem term_two (a b : ℝ) : term [a,b] = pair a b := by
  simp [term,g0,pair]
  norm_num [β,ε] at *
  grind
@[simp] private theorem term_more (a b c : ℝ) (l : List ℝ) : term (a::b::c::l) = 0 := by simp [term,g0]

private def edges (x : ℝ) (v : List ℝ) := (v.map (pair x)).sum
def balance : List ℝ → ℝ
  | [] => 1
  | x::v => balance v - single x + edges x v

private theorem pair_tail (a b : ℝ) (v : List ℝ) : (v.sublists'.map (fun l => term (a::b::l))).sum = pair a b := by
  induction v with
  | nil => simp [List.sublists'_nil]
  | cons x v ih =>
    simp [List.sublists'_cons,List.map_map,Function.comp_def,ih]

private theorem single_tail (a : ℝ) (v : List ℝ) : (v.sublists'.map (fun l => term (a::l))).sum = -single a+edges a v := by
  induction v with
  | nil => simp [List.sublists'_nil,edges]
  | cons x v ih =>
    simp only [List.sublists'_cons,List.map_append,List.sum_append,List.map_map,Function.comp_def,ih,pair_tail]
    simp [edges]; ring

theorem balance_exact (v : List ℝ) : profileSum v = balance v := by
  induction v with
  | nil => simp [profileSum,balance,List.sublists'_nil]
  | cons a v ih =>
    change (List.map term (a::v).sublists').sum = _
    change (v.sublists'.map term).sum = balance v at ih
    simp only [List.sublists'_cons,List.map_append,List.sum_append,List.map_map,Function.comp_def,
      single_tail,ih,balance]
    ring


private theorem three (a b c : ℝ) (ha : Direct.lowerEdge<a) (hab : a≤b) (hbc : b≤c)
    (ht : a+b+c=1) (hpos : 0<balance [a,b,c]) :
    b≤1/5 ∧ 3/5≤c ∧ balance [a,b,c]=1 := by
  simp [balance,edges,pair,single] at hpos ⊢
  norm_num [Direct.lowerEdge,β,ε] at *
  grind (splits := 32)

private theorem four (a b c d : ℝ) (ha : Direct.lowerEdge<a) (hab : a≤b) (hbc : b≤c)
    (hcd : c≤d) (ht : a+b+c+d=1) : balance [a,b,c,d] ≤ 0 := by
  simp [balance,edges,pair,single]
  norm_num [Direct.lowerEdge,β,ε] at *
  grind (splits := 32)

private theorem five (a b c d f : ℝ) (ha : Direct.lowerEdge<a) (hab : a≤b) (hbc : b≤c)
    (hcd : c≤d) (hdf : d≤f) (ht : a+b+c+d+f=1) :
    balance [a,b,c,d,f] ≤ 3 ∧
    (a-Direct.lowerEdge)+(b-Direct.lowerEdge)+(c-Direct.lowerEdge)+(d-Direct.lowerEdge)+(f-Direct.lowerEdge)=5*ε := by
  constructor
  · simp [balance,edges,pair,single]
    norm_num [Direct.lowerEdge,β,ε] at *
    grind (splits := 32)
  · unfold Direct.lowerEdge
    linarith

private theorem check2 (u v : ℝ) (ho : u≤v) (ht : u+v=1) :
    balance [u,v] = if 1/5<u ∧ u≤β then 0 else 1 := by
  have hv : ¬ v≤β := by unfold β ε; linarith
  have hpair : ¬u+v≤β := by unfold β ε; linarith
  simp [balance,edges,single,pair,hv,hpair]
  split_ifs <;> norm_num

private theorem ordered (n : ℕ) : (n.primeFactorsList.map (coord n)).Pairwise (· ≤ ·) := by
  apply List.pairwise_map.mpr
  apply (Nat.primeFactorsList_sorted n).pairwise.imp
  intro p q hpq
  unfold coord
  apply div_le_div_of_nonneg_right _ (Real.log_natCast_nonneg _)
  by_cases hp : p=0
  · simp [hp,Real.log_natCast_nonneg]
  · exact Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hp) (by exact_mod_cast hpq)

private theorem first_lower {n : ℕ} {a : ℝ} {v : List ℝ} (hs : Squarefree n)
    (hg : Direct.good n) (hh : kernelH n ≠ 0) (hf : n.primeFactorsList.map (coord n)=a::v) :
    Direct.lowerEdge<a := by
  have ha : a ∈ n.primeFactorsList.map (coord n) := by simp [hf]
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp ha
  exact active_coordinate hs hg hh hp

theorem rank_three_collar {n : ℕ} (hs : Squarefree n) (hg : Direct.good n) (hh : 0<kernelH n)
    {a b c : ℝ} (hf : n.primeFactorsList.map (coord n)=[a,b,c]) :
    Direct.lowerEdge<a ∧ a≤1/5 ∧ Direct.lowerEdge<b ∧ b≤1/5 ∧ 3/5≤c ∧ kernelH n=1 := by
  have ha := first_lower hs hg hh.ne' hf
  have ho := ordered n
  simp [hf] at ho
  have ht := coordinate_sum hg.1
  simp [hf] at ht
  have hv := active_kernel hs hg hh.ne'
  rw [hf,balance_exact] at hv
  have h := three a b c ha (by grind) (by grind) (by linarith only [ht]) (by linarith only [hh,hv])
  grind

theorem rank_four_nonpositive {n : ℕ} (hs : Squarefree n) (hg : Direct.good n)
    {a b c d : ℝ} (hf : n.primeFactorsList.map (coord n)=[a,b,c,d]) : kernelH n ≤ 0 := by
  by_contra! hh
  have ha := first_lower hs hg hh.ne' hf
  have ho := ordered n
  simp [hf] at ho
  have ht := coordinate_sum hg.1
  simp [hf] at ht
  have hv := active_kernel hs hg hh.ne'
  rw [hf,balance_exact] at hv
  exact (not_le.mpr hh) (hv ▸ four a b c d ha (by grind) (by grind) (by grind) (by linarith only [ht]))

theorem rank_five_simplex {n : ℕ} (hs : Squarefree n) (hg : Direct.good n) (hh : kernelH n ≠ 0)
    {a b c d f : ℝ} (hf : n.primeFactorsList.map (coord n)=[a,b,c,d,f]) :
    (∀ t ∈ [a,b,c,d,f], Direct.lowerEdge<t) ∧ max (kernelH n) 0 ≤ 3 ∧
    (a-Direct.lowerEdge)+(b-Direct.lowerEdge)+(c-Direct.lowerEdge)+(d-Direct.lowerEdge)+(f-Direct.lowerEdge)=5*ε := by
  have ha := first_lower hs hg hh hf
  have ho := ordered n
  simp [hf] at ho
  have ht := coordinate_sum hg.1
  simp [hf] at ht
  have hv := active_kernel hs hg hh
  rw [hf,balance_exact] at hv
  have h := five a b c d f ha (by grind) (by grind) (by grind) (by grind) (by linarith only [ht])
  exact ⟨by intro t hmem; simp at hmem; grind,max_le (hv ▸ h.1) (by norm_num),h.2⟩

theorem rank_two_collar {n : ℕ} (hs : Squarefree n) (hg : Direct.good n) (hh : 0<kernelH n)
    {u v : ℝ} (hf : n.primeFactorsList.map (coord n)=[u,v]) :
    (Direct.lowerEdge<u ∧ u≤1/5) ∨ (β<u ∧ u≤1/2) := by
  have h := active_kernel hs hg hh.ne'
  rw [hf,balance_exact] at h
  have hu : u ∈ n.primeFactorsList.map (coord n) := by simp [hf]
  obtain ⟨p,hp,he⟩ := List.mem_map.mp hu
  have hlow := he ▸ active_coordinate hs hg hh.ne' hp
  have ht := coordinate_sum hg.1
  rw [hf] at ht
  simp only [List.sum_cons,List.sum_nil,add_zero] at ht
  have ho := ordered n
  simp [hf] at ho
  rw [check2 _ _ ho ht] at h
  split_ifs at h <;> grind

end
end REAL1B.FM.Collar
#print axioms REAL1B.FM.Collar.active_coordinate
#print axioms REAL1B.FM.Collar.active_kernel
#print axioms REAL1B.FM.Collar.coordinate_sum
#print axioms REAL1B.FM.Collar.balance_exact
#print axioms REAL1B.FM.Collar.rank_two_collar
#print axioms REAL1B.FM.Collar.rank_three_collar
#print axioms REAL1B.FM.Collar.rank_four_nonpositive
#print axioms REAL1B.FM.Collar.rank_five_simplex
