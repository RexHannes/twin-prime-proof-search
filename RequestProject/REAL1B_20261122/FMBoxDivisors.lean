import RequestProject.REAL1B_20261122.FMBoxGeometry

/-! Enumerate the actual divisors of a squarefree boxed output through its ordered
prime sublists. Cutoffs are tested on each divisor before the signed sum. -/
namespace REAL1B.FM.Box
open Source Analytic Vaughan ArithmeticFunction Filter
noncomputable section
open Classical

private theorem recover {n : ℕ} {l : List ℕ} (h : l.Sublist n.primeFactorsList) :
    l.prod.primeFactorsList = l := by
  have hperm := Nat.primeFactorsList_unique (n:=l.prod) rfl (fun p hp => Nat.prime_of_mem_primeFactorsList (h.subset hp))
  exact (List.Perm.eq_of_pairwise (fun _ _ _ _ => Nat.le_antisymm)
    ((Nat.primeFactorsList_sorted n).pairwise.sublist h)
    (Nat.primeFactorsList_sorted _).pairwise hperm).symm

theorem H_sublists {n : ℕ} (hs : Squarefree n) : kernelH n =
    (n.primeFactorsList.sublists'.map (fun l => divisorCoefficient n l.prod)).sum := by
  rw [← List.sum_toFinset _ (List.nodup_sublists'.mpr hs.nodup_primeFactorsList)]
  apply Finset.sum_bij (fun d _ => d.primeFactorsList)
  · intro d hd
    exact List.mem_toFinset.mpr (List.mem_sublists'.mpr (Nat.primeFactorsList_sublist_of_dvd
      (Nat.mem_divisors.mp hd).1 hs.ne_zero))
  · intro d hd e he h
    simpa [Nat.prod_primeFactorsList (Nat.pos_of_mem_divisors hd).ne',
      Nat.prod_primeFactorsList (Nat.pos_of_mem_divisors he).ne'] using congrArg List.prod h
  · intro l hl
    have h := List.mem_sublists'.mp (List.mem_toFinset.mp hl)
    exact ⟨l.prod, Nat.mem_divisors.mpr ⟨by simpa [Nat.prod_primeFactorsList hs.ne_zero] using h.prod_dvd_prod,hs.ne_zero⟩,recover h⟩
  · intro d hd
    rw [Nat.prod_primeFactorsList (Nat.pos_of_mem_divisors hd).ne']

def coord (n p : ℕ) := Real.log p / Real.log n
def mass (n : ℕ) (l : List ℕ) := (l.map (coord n)).sum

private theorem source_profile (n : ℕ) (l : List ℕ) : profile n l = l.map (coord n) := by
  unfold profile
  change (l.flatMap (fun p : ℕ => [(p:ℝ)])).map _ = _
  rw [← List.map_eq_flatMap,List.map_map]
  rfl

private theorem log_mass {n : ℕ} {l : List ℕ} (h : l.Sublist n.primeFactorsList) :
    mass n l = Real.log (l.prod:ℕ) / Real.log n := by
  induction l with
  | nil => simp [mass]
  | cons p l ih =>
    have hp := Nat.prime_of_mem_primeFactorsList (h.subset List.mem_cons_self)
    have hl := (List.sublist_cons_self p l).trans h
    have hn : l.prod ≠ 0 := fun he => (Nat.prime_of_mem_primeFactorsList (hl.subset (List.prod_eq_zero_iff.mp he))).ne_zero rfl
    simp only [mass,List.map_cons,List.sum_cons,List.prod_cons,Nat.cast_mul]
    rw [show (l.map (coord n)).sum = _ from ih hl, Real.log_mul (by exact_mod_cast hp.ne_zero) (by exact_mod_cast hn)]
    unfold coord
    ring

private theorem mu_sublist {n : ℕ} (hs : Squarefree n) {l : List ℕ} (h : l.Sublist n.primeFactorsList) :
    mu l.prod = (-1:ℝ)^l.length := by
  have hd : l.prod ∣ n := by simpa [Nat.prod_primeFactorsList hs.ne_zero] using h.prod_dvd_prod
  rw [mu,moebius_apply_of_squarefree (hs.squarefree_of_dvd hd),cardFactors_apply,recover h]
  push_cast
  rfl

private theorem g0_sign (ts : List ℝ) (h : ∀ t ∈ ts, 1/5 < t) (hl : ts.sum ≤ β) :
    g0 ts = (-1:ℝ)^ts.length := by
  have hb : β < 1/2 := by norm_num [β,ε]
  have hsum := hl.trans_lt hb
  rcases ts with _ | ⟨t,ts⟩
  · rfl
  rcases ts with _ | ⟨u,ts⟩
  · have h₁ := h t (by simp)
    have h₂ : t ≤ 1/2 := by simpa only [List.sum_cons,List.sum_nil,add_zero] using hsum.le
    rw [g0,if_pos ⟨h₁,h₂⟩]; norm_num
  rcases ts with _ | ⟨v,ts⟩
  · have h₂ : t+u < 1/2 := by simpa only [List.sum_cons,List.sum_nil,add_zero] using hsum
    rw [g0,if_pos ⟨h t (by simp),h u (by simp),h₂⟩]; norm_num
  · have hrest := List.sum_nonneg (l:=ts) (fun y hy => by linarith only [h y (by simp [hy])])
    simp only [List.sum_cons] at hsum
    linarith only [hsum,h t (by simp),h u (by simp),h v (by simp),hrest]

/-- For separated prime coordinates the true H divisor coefficient is 0 or the
Möbius sign of its complete prime list, with both original cutoffs retained. -/
theorem coefficient {n : ℕ} (hs : Squarefree n)
    (hsep : ∀ p ∈ n.primeFactorsList, (n:ℝ)^ν ≤ p → 1/5 < coord n p)
    {l : List ℕ} (hl : l.Sublist n.primeFactorsList) :
    divisorCoefficient n l.prod =
    if (l.prod:ℝ) ≤ (n:ℝ)^γ ∧ mass n (l.filter (fun p : ℕ => decide ((n:ℝ)^ν ≤ (p:ℝ)))) ≤ β
    then (-1:ℝ)^l.length else 0 := by
  let a := l.filter (fun p : ℕ => decide ((p:ℝ) < (n:ℝ)^ν))
  let b := l.filter (fun p : ℕ => decide ((n:ℝ)^ν ≤ (p:ℝ)))
  have ha : a.Sublist n.primeFactorsList := List.filter_sublist.trans hl
  have hlen : a.length+b.length = l.length := by
    dsimp [a,b]
    clear ha hl a b
    induction l with
    | nil => simp
    | cons p l ih =>
      by_cases h : (p:ℝ)<(n:ℝ)^ν
      · simp [h,not_le.mpr h]; omega
      · simp [h,le_of_not_gt h]; omega
  unfold divisorCoefficient
  simp only [recover hl,source_profile]
  change (if (l.prod:ℝ) ≤ (n:ℝ)^γ ∧ mass n b ≤ β then mu a.prod * g0 (b.map (coord n)) else 0) = _
  split_ifs with h
  · have hbig (t : ℝ) (ht : t ∈ b.map (coord n)) : 1/5<t := by
      obtain ⟨p,hp,rfl⟩ := List.mem_map.mp ht
      have hp' := List.mem_filter.mp hp
      exact hsep p (hl.subset hp'.1) (of_decide_eq_true hp'.2)
    rw [mu_sublist hs ha,g0_sign _ hbig h.2,List.length_map,← pow_add,hlen]
  · rfl

private theorem filter_mass (n : ℕ) (f : ℕ → Bool) (l : List ℕ) :
    mass n (l.filter f) ≤ mass n l := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    have hp : 0 ≤ coord n p := div_nonneg (Real.log_natCast_nonneg _) (Real.log_natCast_nonneg _)
    by_cases hf : f p <;> simp [mass,hf] at ih ⊢ <;> linarith

private theorem mass_cut {n : ℕ} (hn : 1<n) {l : List ℕ} (hl : l.Sublist n.primeFactorsList) :
    ((l.prod:ℝ) ≤ (n:ℝ)^γ) ↔ mass n l ≤ γ := by
  have hx : (0:ℝ) < n := by exact_mod_cast (show 0<n by omega)
  have hp : l.prod ≠ 0 := fun he => (Nat.prime_of_mem_primeFactorsList (hl.subset (List.prod_eq_zero_iff.mp he))).ne_zero rfl
  have hL := Real.log_pos (by exact_mod_cast hn : (1:ℝ) < n)
  rw [log_mass hl,div_le_iff₀ hL,← Real.log_le_log_iff (by exact_mod_cast Nat.pos_of_ne_zero hp)
    (Real.rpow_pos_of_pos hx γ),Real.log_rpow hx]

structure TermRules {α : Type} (v : α → ℝ) (L : List α) (W : List α → ℝ) : Prop where
  small : ∀ s, s.Sublist L → (s.map v).sum < 0.49 → W s = (-1:ℝ)^s.length
  large : ∀ s, s.Sublist L → 0.51 < (s.map v).sum → W s = 0
  sign : ∀ s, s.Sublist L → W s = 0 ∨ W s = (-1:ℝ)^s.length

theorem native_rules {n : ℕ} (hn : 1<n) (hs : Squarefree n)
    (hsep : ∀ p ∈ n.primeFactorsList, (n:ℝ)^ν ≤ p → 1/5 < coord n p) :
    TermRules (coord n) n.primeFactorsList (fun l => divisorCoefficient n l.prod) := by
  constructor
  · intro s h hm
    rw [coefficient hs hsep h, if_pos]
    have h₁ : mass n s < 0.49 := hm
    refine ⟨(mass_cut hn h).mpr (h₁.le.trans (by norm_num [γ,ε])),?_⟩
    exact (filter_mass n _ s).trans (h₁.le.trans (by norm_num [β,ε]))
  · intro s h hm
    rw [coefficient hs hsep h, if_neg]
    intro hh
    have hi := (mass_cut hn h).mp hh.1
    have h₁ : 0.51 < mass n s := hm
    unfold γ ε at hi
    linarith only [hi,h₁]
  · intro s h
    rw [coefficient hs hsep h]
    split_ifs <;> simp

private theorem coordinate_order {n p q : ℕ} (hp : p.Prime) (h : p ≤ q) : coord n p ≤ coord n q :=
  div_le_div_of_nonneg_right (Real.log_le_log (by exact_mod_cast hp.pos) (by exact_mod_cast h)) (Real.log_natCast_nonneg _)

private theorem coord_cut {n p : ℕ} (hn : 1<n) (h : (n:ℝ)^ν ≤ p) :
    ν ≤ coord n p := by
  have hpos : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hlog := Real.log_le_log (Real.rpow_pos_of_pos hpos ν) h
  rw [Real.log_rpow hpos] at hlog
  exact (le_div_iff₀ (Real.log_pos (by exact_mod_cast hn))).mpr hlog
local macro "on_five" : tactic => `(tactic| repeat' first | exact List.nil_sublist _ | apply List.Sublist.cons₂ | apply List.Sublist.cons)
local macro "box_mass" : tactic => `(tactic|
  (simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero] <;> linarith))

/-- Eight pairs below .49 have eight complementary triples above .51.
Only the pairs (3,5), (4,5) and their two complements can still vary. -/
theorem five_expand {α : Type} {v : α → ℝ} {W : List α → ℝ} {a b c d e : α}
    (h : TermRules v [a,b,c,d,e] W)
    (ha : 0 < v a) (hab : v a ≤ v b) (hbc : v b ≤ v c) (hcd : v c ≤ v d) (hde : v d ≤ v e)
    (hsum : v a+v b+v c+v d+v e = 1) (hbe : v b+v e < 0.49) (hcd' : v c+v d < 0.49) :
    (([a,b,c,d,e].sublists').map W).sum = 4 + W [c,e] + W [d,e] + W [a,b,d] + W [a,b,c] := by
  simp only [List.sublists'_cons,List.sublists'_nil,List.map_cons,List.map_nil,
    List.cons_append,List.nil_append,List.sum_cons,List.sum_nil,add_zero]
  rw [h.small [] (by on_five) (by box_mass),
    h.small [a] (by on_five) (by box_mass),
    h.small [b] (by on_five) (by box_mass),
    h.small [c] (by on_five) (by box_mass),
    h.small [d] (by on_five) (by box_mass),
    h.small [e] (by on_five) (by box_mass),
    h.small [a,b] (by on_five) (by box_mass),
    h.small [a,c] (by on_five) (by box_mass),
    h.small [a,d] (by on_five) (by box_mass),
    h.small [a,e] (by on_five) (by box_mass),
    h.small [b,c] (by on_five) (by box_mass),
    h.small [b,d] (by on_five) (by box_mass),
    h.small [b,e] (by on_five) (by box_mass),
    h.small [c,d] (by on_five) (by box_mass),
    h.large [a,b,e] (by on_five) (by box_mass),
    h.large [a,c,d] (by on_five) (by box_mass),
    h.large [a,c,e] (by on_five) (by box_mass),
    h.large [a,d,e] (by on_five) (by box_mass),
    h.large [b,c,d] (by on_five) (by box_mass),
    h.large [b,c,e] (by on_five) (by box_mass),
    h.large [b,d,e] (by on_five) (by box_mass),
    h.large [c,d,e] (by on_five) (by box_mass),
    h.large [a,b,c,d] (by on_five) (by box_mass),
    h.large [a,b,c,e] (by on_five) (by box_mass),
    h.large [a,b,d,e] (by on_five) (by box_mass),
    h.large [a,c,d,e] (by on_five) (by box_mass),
    h.large [b,c,d,e] (by on_five) (by box_mass),
    h.large [a,b,c,d,e] (by on_five) (by box_mass)]
  norm_num only [List.length_cons,List.length_nil,pow_zero,pow_succ,mul_neg,mul_one,neg_neg]
  ring

theorem five_sum {α : Type} {v : α → ℝ} {W : List α → ℝ} {a b c d e : α}
    (h : TermRules v [a,b,c,d,e] W)
    (ha : 0 < v a) (hab : v a ≤ v b) (hbc : v b ≤ v c) (hcd : v c ≤ v d) (hde : v d ≤ v e)
    (hsum : v a+v b+v c+v d+v e = 1) (hbe : v b+v e < 0.49) (hcd' : v c+v d < 0.49) :
    2 ≤ (([a,b,c,d,e].sublists').map W).sum ∧ (([a,b,c,d,e].sublists').map W).sum ≤ 6 := by
  have pair (s : List α) (hm : s.Sublist [a,b,c,d,e]) (hl : s.length = 2) : 0 ≤ W s ∧ W s ≤ 1 := by
    rcases h.sign s hm with he | he <;> norm_num [he,hl]
  have triple (s : List α) (hm : s.Sublist [a,b,c,d,e]) (hl : s.length = 3) : -1 ≤ W s ∧ W s ≤ 0 := by
    rcases h.sign s hm with he | he <;> norm_num [he,hl]
  have p₁ := pair [c,e] (by on_five) rfl
  have p₂ := pair [d,e] (by on_five) rfl
  have t₁ := triple [a,b,d] (by on_five) rfl
  have t₂ := triple [a,b,c] (by on_five) rfl
  rw [five_expand h ha hab hbc hcd hde hsum hbe hcd']
  constructor <;> linarith only [p₁.1,p₁.2,p₂.1,p₂.2,t₁.1,t₁.2,t₂.1,t₂.2]

private theorem cell_gap {n p i : ℕ} (h : Closing.inCell n p i) (hi : i+1 ≤ 19 ∨ 21 ≤ i) :
    coord n p < 0.19 ∨ 0.21 < coord n p := by
  rcases hi with h₁ | h₂
  · have hh : (i:ℝ)+1 ≤ 19 := by exact_mod_cast h₁
    left; unfold coord; linarith only [h.2,hh]
  · have hh : (21:ℝ) ≤ i := by exact_mod_cast h₂
    right; unfold coord; linarith only [h.1,hh]

private theorem cutoff_iff {n p : ℕ} (hn : 1<n) (hp : p.Prime) :
    ((n:ℝ)^ν ≤ p) ↔ ν ≤ coord n p := by
  have hn' : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  rw [← Real.log_le_log_iff (Real.rpow_pos_of_pos hn' _) (by exact_mod_cast hp.pos),
    Real.log_rpow hn',coord,le_div_iff₀ (Real.log_pos (by exact_mod_cast hn))]

private theorem face_arithmetic (P T δ : ℝ) (h : P+T=1) :
    (if P ≤ 1/2-δ then (1:ℝ) else 0) + (if T ≤ γ then -1 else 0) =
    (if 1/2+δ ≤ T then 1 else 0) + (if 1/2-ε < T then 1 else 0) - 1 := by
  have hh : P ≤ 1/2-δ ↔ 1/2+δ ≤ T := by constructor <;> intro <;> linarith
  simp only [hh,γ]
  split_ifs <;> norm_num <;> linarith

/-- A pair and its complementary triple contribute exactly the two original
indicator faces minus one, including equality at either cutoff. -/
private theorem complementary_face {n p q w u t : ℕ} (hn : 1<n) (hs : Squarefree n)
    (sep : ∀ v ∈ n.primeFactorsList, (n:ℝ)^ν ≤ v → 1/5 < coord n v)
    (pair : [u,t].Sublist n.primeFactorsList) (triple : [p,q,w].Sublist n.primeFactorsList)
    (small : 0.04 < coord n p ∧ coord n p < 0.19)
    (big : 0.21 < coord n t ∧ coord n t < 0.49)
    (sum : coord n u + coord n t + mass n [p,q,w] = 1) :
    divisorCoefficient n [u,t].prod + divisorCoefficient n [p,q,w].prod =
      Direct.face (coord n u) (mass n [p,q,w]) - 1 := by
  have prime {v} (hv : v ∈ n.primeFactorsList) := Nat.prime_of_mem_primeFactorsList hv
  have hp := prime (triple.subset (by simp : p ∈ [p,q,w]))
  have hu := prime (pair.subset (by simp : u ∈ [u,t]))
  have ht := prime (pair.subset (by simp : t ∈ [u,t]))
  have hp' : ¬(n:ℝ)^ν ≤ p := fun h => by have := (cutoff_iff hn hp).mp h; unfold ν ε at this; linarith [small.2]
  have ht' : (n:ℝ)^ν ≤ t := (cutoff_iff hn ht).mpr (by unfold ν ε; linarith [big.1])
  let b := fun v : ℕ => decide ((n:ℝ)^ν ≤ (v:ℝ))
  have htr : mass n [p,q,w] ≤ γ →
      mass n ([p,q,w].filter b) ≤ β := by
    intro h
    have h₁ := filter_mass n b [q,w]
    have hz : [p,q,w].filter b = [q,w].filter b := by simp [List.filter_cons,b,hp']
    rw [hz]
    have hwhole : mass n [p,q,w] = coord n p + mass n [q,w] := rfl
    unfold γ at h; unfold β ε
    unfold ε at h
    linarith only [h,hwhole,h₁,small.1]
  have htr' : divisorCoefficient n [p,q,w].prod = if mass n [p,q,w] ≤ γ then -1 else 0 := by
    simp only [coefficient hs sep triple,mass_cut hn triple]
    by_cases h : mass n [p,q,w] ≤ γ
    · rw [if_pos ⟨h,htr h⟩,if_pos h]; norm_num
    · simp [h]
  simp only [htr',coefficient hs sep pair,mass_cut hn pair,show (-1:ℝ)^([u,t].length) = 1 by norm_num]
  have hpair : mass n [u,t] = coord n u + coord n t := by simp [mass]
  have h₁ : β ≤ γ := by norm_num [β,γ,ε]
  by_cases hbig : (n:ℝ)^ν ≤ u
  · have hcoord := sep u (pair.subset (by simp)) hbig
    simp only [List.filter_cons,decide_eq_true_eq,if_pos hbig,if_pos ht',List.filter_nil]
    simp only [show (mass n [u,t] ≤ γ ∧ mass n [u,t] ≤ β) ↔ mass n [u,t] ≤ β from
      ⟨And.right, fun h => ⟨h.trans h₁,h⟩⟩]
    simp only [Direct.face,if_pos hcoord,hpair]
    exact face_arithmetic _ _ (2*ε) sum
  · have hcoord : ¬1/5 < coord n u := by
      intro h
      exact hbig ((cutoff_iff hn hu).mpr (by unfold ν ε; linarith))
    have hβ : mass n [t] ≤ β := by simp only [mass,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]; unfold β ε; linarith [big.2]
    simp only [List.filter_cons,decide_eq_true_eq,if_neg hbig,if_pos ht',List.filter_nil,hβ,and_true,
      Direct.face,if_neg hcoord,hpair,one_mul]
    exact face_arithmetic _ _ ε sum

theorem H_formula {n p q r s t i j k l : ℕ} (hn : 1<n) (hs : Squarefree n)
    (hf : n.primeFactorsList = [p,q,r,s,t]) (had : Closing.admissible i j k l)
    (hp : Closing.inCell n p i) (hq : Closing.inCell n q j) (hr : Closing.inCell n r k) (hS : Closing.inCell n s l) :
    kernelH n = Direct.profileH ![coord n p,coord n q,coord n r,coord n s] := by
  have hi := Closing.first_index_lower had
  obtain ⟨_,_,_,_,_,hfirst,ci,cj,ck,cl,_,hfifth,_,hodd,hpair⟩ := had
  have hsum : coord n p + coord n q + coord n r + coord n s + coord n t = 1 := by
    have h := log_mass (n:=n) (List.Sublist.refl n.primeFactorsList)
    rw [Nat.prod_primeFactorsList hs.ne_zero,div_self (Real.log_pos (by exact_mod_cast hn)).ne'] at h
    simp only [mass,hf,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero] at h
    linarith only [h]
  have htotal : (i:ℝ)+j+k+l+21 ≤ 96 := by exact_mod_cast hfifth
  have hodd' : (51:ℝ) ≤ i+k+l := by exact_mod_cast hodd
  have hpair' : (k:ℝ)+l+2 ≤ 49 := by exact_mod_cast hpair
  have ha := hp.1
  have hc := hr.1
  have hd := hS.1
  have ht : 0.21 < coord n t := by
    unfold coord at hsum ⊢
    linarith only [hsum,htotal,hp.2,hq.2,hr.2,hS.2]
  have sep (u : ℕ) (hu : u ∈ n.primeFactorsList) (hcut : (n:ℝ)^ν ≤ u) : 1/5 < coord n u := by
    have ht' := coord_cut hn hcut
    have hgap : coord n u < 0.19 ∨ 0.21 < coord n u := by
      rw [hf] at hu
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hu
      rcases hu with rfl | rfl | rfl | rfl | rfl
      · exact cell_gap hp ci
      · exact cell_gap hq cj
      · exact cell_gap hr ck
      · exact cell_gap hS cl
      · exact Or.inr ht
    unfold ν ε at ht'
    rcases hgap with h | h <;> linarith only [ht',h]
  have rules := native_rules hn hs sep
  have hpr (u : ℕ) (hu : u ∈ [p,q,r,s,t]) : u.Prime := Nat.prime_of_mem_primeFactorsList (hf ▸ hu)
  have hsort := (Nat.primeFactorsList_sorted n).pairwise
  rw [hf] at hsort rules
  simp only [List.pairwise_cons,List.mem_cons,List.not_mem_nil,or_false] at hsort
  have hab := coordinate_order (n:=n) (hpr p (by simp)) (hsort.1 q (by simp))
  have hbc := coordinate_order (n:=n) (hpr q (by simp)) (hsort.2.1 r (by simp))
  have hcd := coordinate_order (n:=n) (hpr r (by simp)) (hsort.2.2.1 s (by simp))
  have hde := coordinate_order (n:=n) (hpr s (by simp)) (hsort.2.2.2.1 t (by simp))
  have hpos : 0 < coord n p := div_pos (Real.log_pos (by exact_mod_cast (hpr p (by simp)).one_lt))
    (Real.log_pos (by exact_mod_cast hn))
  have hbe : coord n q + coord n t < 0.49 := by
    unfold coord at hsum ⊢
    linarith only [hsum,ha,hc,hd,hodd']
  have hcd' : coord n r + coord n s < 0.49 := by
    unfold coord
    linarith only [hr.2,hS.2,hpair']
  have hsmall : 0.04 < coord n p ∧ coord n p < 0.19 := by
    have h₁ : (4:ℝ) ≤ i := by exact_mod_cast hi
    have h₂ : (i:ℝ)+1 ≤ 19 := by exact_mod_cast hfirst
    unfold coord; constructor <;> linarith only [hp.1,hp.2,h₁,h₂]
  have hbig : 0.21 < coord n t ∧ coord n t < 0.49 := ⟨ht,by linarith only [hbe,hpos,hab]⟩
  have face₁ := complementary_face (u:=r) (t:=t) (p:=p) (q:=q) (w:=s) hn hs sep
    (by rw [hf]; on_five) (by rw [hf]; on_five) hsmall hbig (by simp [mass]; linarith only [hsum])
  have face₂ := complementary_face (u:=s) (t:=t) (p:=p) (q:=q) (w:=r) hn hs sep
    (by rw [hf]; on_five) (by rw [hf]; on_five) hsmall hbig (by simp [mass]; linarith only [hsum])
  rw [H_sublists hs,hf,five_expand rules hpos hab hbc hcd hde hsum hbe hcd']
  simp only [mass,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero] at face₁ face₂
  change _ = 2 + Direct.face (coord n r) (coord n p + coord n q + coord n s) +
    Direct.face (coord n s) (coord n p + coord n q + coord n r)
  simp only [add_assoc] at face₁ face₂ ⊢
  linarith only [face₁,face₂]

theorem H_range {n : ℕ} (hn : 1<n) (hb : Closing.boxes n) : 2 ≤ kernelH n ∧ kernelH n ≤ 6 := by
  obtain ⟨hs,_,_,_,_,_,_,_,_,_,hf,had,hp,hq,hr,hS⟩ := hb
  rw [H_formula hn hs hf had hp hq hr hS]
  unfold Direct.profileH Direct.face
  split_ifs <;> norm_num

theorem psi_range {x : ℝ} (hx : 4 ≤ x) {n : ℕ} (hn : n ∈ interval (x/2)) (hb : Closing.boxes n) :
    2 ≤ Direct.psi x n ∧ Direct.psi x n ≤ 6 := by
  rw [box_phi_eq_H hx hn hb]
  exact H_range (by have := (window hn).2.2; omega) hb

/-- Values outside the five-prime support are zero. The four independent
coordinates come from the actual ordered prime factors of n. -/
def coordinates (n : ℕ) (j : Fin 4) := coord n (n.primeFactorsList[j.val]?.getD 1)
def profileWeight (n : ℕ) : ℝ := if Closing.boxes n then Direct.profileH (coordinates n) else 0

theorem psi_profile {x : ℝ} (hx : 4 ≤ x) {n : ℕ} (hn : n ∈ interval (x/2)) :
    Direct.psi x n = profileWeight n := by
  unfold profileWeight
  by_cases hb : Closing.boxes n
  · rw [if_pos hb,box_phi_eq_H hx hn hb]
    obtain ⟨hs,p,q,r,s,t,_,_,_,_,hf,had,hp,hq,hr,hS⟩ := hb
    rw [H_formula (by have := (window hn).2.2; omega) hs hf had hp hq hr hS]
    congr 1
    funext j
    fin_cases j <;> simp [coordinates,hf]
  · simp [Direct.psi,hb]

theorem psi_nonneg : ∀ᶠ x : ℝ in atTop, ∀ n ∈ interval (x/2), 0 ≤ Direct.psi x n := by
  filter_upwards [eventually_ge_atTop (4:ℝ)] with x hx n hn
  by_cases hb : Closing.boxes n
  · linarith only [(psi_range hx hn hb).1]
  · simp [Direct.psi,hb]

theorem source_profile_sum {x : ℝ} (hx : 4 ≤ x) (w : ℕ → ℝ) :
    total (x/2) (fun n => w n * Direct.psi x n) = total (x/2) (fun n => w n * profileWeight n) :=
  Finset.sum_congr rfl (fun n hn => congrArg (fun z => w n*z) (psi_profile hx hn))

end
end REAL1B.FM.Box
#print axioms REAL1B.FM.Box.H_sublists
#print axioms REAL1B.FM.Box.coefficient
#print axioms REAL1B.FM.Box.native_rules
#print axioms REAL1B.FM.Box.five_sum
#print axioms REAL1B.FM.Box.H_range
#print axioms REAL1B.FM.Box.psi_range
#print axioms REAL1B.FM.Box.H_formula
#print axioms REAL1B.FM.Box.psi_profile
#print axioms REAL1B.FM.Box.psi_nonneg
#print axioms REAL1B.FM.Box.source_profile_sum
