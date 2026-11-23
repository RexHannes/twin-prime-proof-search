import RequestProject.REAL1B_20261122.FMDirect

/-! Compare the fundamental-vector and strict rank-assignment presentations. -/
namespace REAL1B.FM.Direct
open Source Filter
noncomputable section
open Classical

private def tiny (v : List ℝ) := (v.map (fun t => if t < ε then t else 0)).sum
private def countBig (v : List ℝ) := (v.map (fun t => if t < ε then (0:ℕ) else 1)).sum

private theorem edges : 0 < ε ∧ 2*ε < lowerEdge ∧ lowerEdge < upperEdge ∧
    upperEdge < 1 ∧ 1 < 6*lowerEdge := by norm_num [lowerEdge, upperEdge, ε]

private theorem tiny_mono {u v : List ℝ} (h : u.Sublist v) (hp : ∀ t ∈ v, 0 ≤ t) :
    tiny u ≤ tiny v := by
  induction h with
  | slnil => rfl
  | cons x h ih =>
    have h' := ih (fun t ht => hp t (by simp [ht]))
    have h0 := hp x (by simp)
    simp only [tiny, List.map_cons, List.sum_cons] at *
    split_ifs <;> linarith
  | cons₂ x h ih =>
    simpa [tiny] using ih (fun t ht => hp t (by simp [ht]))

private theorem fundamental_shape (v : List ℝ) :
    fundamental v ↔ v.sum = 1 ∧ (∀ t ∈ v, 0 < t ∧ t < upperEdge ∧ (t < ε ∨ lowerEdge < t)) ∧
      tiny v < ε := by
  have h₁ : ε + ν = lowerEdge := by unfold ν lowerEdge; ring
  have h₂ : 1-γ = upperEdge := by unfold γ upperEdge; ring
  constructor
  · rintro ⟨hs, ht, hsub⟩
    have gap (w : List ℝ) (hw : w.Sublist v) : w.sum < ε ∨ lowerEdge < w.sum := by
      by_cases he : w = []
      · simpa [he] using Or.inl edges.1
      by_cases hlt : w.length < v.length
      · simpa [h₁] using hsub w hw he hlt
      · rw [hw.eq_of_length_le (le_of_not_gt hlt), hs]
        exact Or.inr (edges.2.2.1.trans edges.2.2.2.1)
    refine ⟨hs, fun t h => ⟨(ht t h).1, h₂ ▸ (ht t h).2, ?_⟩, ?_⟩
    · simpa using gap [t] (List.singleton_sublist.mpr h)
    · have small (w : List ℝ) (hw : w.Sublist v) (htiny : ∀ t ∈ w, t < ε) : w.sum < ε := by
        induction w with
        | nil => simpa using edges.1
        | cons t w ih =>
          have hh := htiny t (by simp)
          have hsum := ih ((List.sublist_cons_self t w).trans hw) (fun q hq => htiny q (by simp [hq]))
          rcases gap (t::w) hw with h | h
          · exact h
          · simp only [List.sum_cons] at *
            linarith only [hh, hsum, h, edges.2.1]
      have eqv (w : List ℝ) : tiny w = (w.filter (fun t => decide (t < ε))).sum := by
        induction w with
        | nil => rfl
        | cons t w ih => by_cases h : t < ε <;> simp_all [tiny]
      rw [eqv]
      exact small _ List.filter_sublist (fun t h => of_decide_eq_true (List.mem_filter.mp h).2)
  · rintro ⟨hs, ht, hcost⟩
    refine ⟨hs, fun t h => ⟨(ht t h).1, h₂.symm ▸ (ht t h).2.1⟩, ?_⟩
    intro w hsub _ _
    rw [h₁]
    by_cases h : ∀ t ∈ w, t < ε
    · have he : tiny w = w.sum := by
        unfold tiny
        congr 1
        exact (List.map_congr_left (g := id) (fun t ht => if_pos (h t ht))).trans (List.map_id w)
      exact Or.inl (he ▸ (tiny_mono hsub (fun t h => (ht t h).1.le)).trans_lt hcost)
    · push_neg at h
      obtain ⟨t, htw, hte⟩ := h
      have hbig := ((ht t (hsub.subset htw)).2.2).resolve_left (not_lt.mpr hte)
      exact Or.inr (hbig.trans_le (List.single_le_sum (fun y hy => (ht y (hsub.subset hy)).1.le) _ htw))

/-- Explicit positive tiny allocations and strictly interior equal macro pieces.
This formulation makes the strict upper face of a fundamental coordinate visible. -/
def allocations {N : ℕ} (t : Fin N → ℝ) : Prop :=
  ∃ (r : Fin N → ℕ) (d : Fin N → ℝ), ∑ i, r i ≤ 5 ∧ ∑ i, d i < ε ∧
    ∀ i, 0 < d i ∧ (if r i = 0 then d i = t i else
      r i * lowerEdge < t i - d i ∧ t i - d i < r i * upperEdge)

theorem rank_iff_allocations {N : ℕ} {t : Fin N → ℝ} (ht : ∀ i, 0 < t i) :
    rankTest t ↔ allocations t := by
  constructor
  · rintro ⟨r,hr,hl,hc⟩
    let c := fun i => tinyCost (t i) (r i)
    let η := (ε - ∑ i, c i) / ((N:ℝ)+1)
    have hden : 0 < (N:ℝ)+1 := by positivity
    have hη : 0 < η := div_pos (sub_pos.mpr hc) hden
    let bonus := fun i => if r i = 0 then 0 else min η ((t i - c i - r i * lowerEdge)/2)
    have room (i) (hi : r i ≠ 0) : r i * lowerEdge < t i - c i := by
      have h₁ := hl i (Nat.pos_of_ne_zero hi)
      have h₂ := mul_lt_mul_of_pos_left edges.2.2.1 (by exact_mod_cast Nat.pos_of_ne_zero hi : 0 < (r i:ℝ))
      simp only [c, tinyCost, if_neg hi]
      rcases le_total (t i - r i * upperEdge) 0 with h|h
      · rw [max_eq_right h]; linarith
      · rw [max_eq_left h]; linarith
    refine ⟨r, fun i => c i + bonus i, hr, ?_, ?_⟩
    · have hb : ∑ i, bonus i ≤ ∑ _ : Fin N, η := Finset.sum_le_sum (fun i _ => by
        by_cases h : r i = 0 <;> simp [bonus, h, hη.le])
      have heta : η*((N:ℝ)+1) = ε - ∑ i, c i := div_mul_cancel₀ _ hden.ne'
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hb
      rw [Finset.sum_add_distrib]
      linarith only [hb, heta, hη]
    · intro i
      by_cases hi : r i = 0
      · simp [bonus, c, tinyCost, hi, ht i]
      · have hroom := room i hi
        have hb : 0 < bonus i := by simp [bonus, hi, hη, show 0 < (t i-c i-r i*lowerEdge)/2 by linarith]
        have hb' : bonus i ≤ (t i-c i-r i*lowerEdge)/2 := by simp [bonus, hi]
        have hc₀ : 0 ≤ c i := by simp [c, tinyCost, hi]
        have hc₁ : t i - r i*upperEdge ≤ c i := by simp [c, tinyCost, hi]
        simp only [if_neg hi]
        exact ⟨by linarith, by linarith, by linarith⟩
  · rintro ⟨r,d,hr,hd,h⟩
    refine ⟨r, hr, fun i hi => ?_, lt_of_le_of_lt (Finset.sum_le_sum (fun i _ => ?_)) hd⟩
    · have hh := (h i).2
      rw [if_neg (Nat.ne_of_gt hi)] at hh
      linarith only [(h i).1, hh.1]
    · have hh := (h i).2
      by_cases hi : r i = 0
      · rw [if_pos hi] at hh
        simpa [tinyCost, hi] using hh.symm.le
      · rw [if_neg hi] at hh
        simp only [tinyCost, if_neg hi, max_le_iff]
        exact ⟨by linarith only [hh.2], (h i).1.le⟩

private def Shape (v : List ℝ) : Prop := ∀ t ∈ v, 0 < t ∧ t < upperEdge ∧ (t < ε ∨ lowerEdge < t)

private theorem block_stats (v : List ℝ) (h : Shape v) :
    0 ≤ tiny v ∧ countBig v * lowerEdge ≤ v.sum - tiny v ∧
    (countBig v = 0 ∨ countBig v * lowerEdge < v.sum - tiny v) ∧
    v.sum - tiny v ≤ countBig v * upperEdge := by
  induction v with
  | nil => simp [tiny, countBig]
  | cons t v ih =>
    obtain ⟨hpos,hupper,hgap⟩ := h t (by simp)
    obtain ⟨ht,hl,hs,hu⟩ := ih (fun y hy => h y (by simp [hy]))
    by_cases he : t < ε
    · have a : tiny (t::v) = t + tiny v := by simp [tiny, he]
      have b : countBig (t::v) = countBig v := by simp [countBig, he]
      rw [a,b,List.sum_cons]
      exact ⟨by linarith, by linarith, hs.imp_right (by intro; linarith), by linarith⟩
    · have a : tiny (t::v) = tiny v := by simp [tiny, he]
      have b : countBig (t::v) = 1 + countBig v := by simp [countBig, he]
      have hg := hgap.resolve_left he
      rw [a,b,List.sum_cons,Nat.cast_add,Nat.cast_one]
      exact ⟨ht, by linarith, Or.inr (by linarith), by linarith⟩

private theorem tiny_flat (v : List (List ℝ)) : tiny v.flatten = (v.map tiny).sum := by
  induction v with
  | nil => rfl
  | cons b v ih => simpa [tiny, List.sum_append] using congrArg (fun s => tiny b + s) ih

private theorem sum_blocks {N : ℕ} (B : Fin N → List ℝ) :
    (List.ofFn B).flatten.sum = ∑ i, (B i).sum := by
  simp [List.sum_flatten, List.map_ofFn, Function.comp_def, List.sum_ofFn]

private theorem cost_blocks {N : ℕ} (B : Fin N → List ℝ) :
    tiny (List.ofFn B).flatten = ∑ i, tiny (B i) := by
  simp [tiny_flat, List.map_ofFn, Function.comp_def, List.sum_ofFn]

private theorem rank_of_blocks {N : ℕ} {t : Fin N → ℝ} (B : Fin N → List ℝ)
    (hB : fundamental (List.ofFn B).flatten) (he : ∀ i, (B i).sum = t i) : rankTest t := by
  obtain ⟨ht,hs,hc⟩ := (fundamental_shape _).mp hB
  have stats i := block_stats (B i) (fun y hy => hs y (List.mem_flatten.mpr
    ⟨B i, List.mem_ofFn.mpr ⟨i,rfl⟩, hy⟩))
  have hbudget : (∑ i, (countBig (B i):ℝ)) * lowerEdge ≤ 1 := by
    rw [← ht, sum_blocks, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i _
    linarith only [(stats i).2.1, (stats i).1]
  refine ⟨fun i => countBig (B i), ?_, ?_, ?_⟩
  · by_contra! h
    have h6 : 6 ≤ ∑ i, (countBig (B i):ℝ) := by exact_mod_cast h
    have hpos : 0 < lowerEdge := by linarith only [edges.1, edges.2.1]
    linarith only [mul_le_mul_of_nonneg_right h6 hpos.le, edges.2.2.2.2, hbudget]
  · intro i hi
    rw [← he i]
    linarith only [((stats i).2.2.1.resolve_left hi.ne'), (stats i).1]
  · rw [cost_blocks] at hc
    refine lt_of_le_of_lt (Finset.sum_le_sum (fun i _ => ?_)) hc
    rw [← he i]
    by_cases h : countBig (B i) = 0
    · have h' := (stats i).2.2.2
      simpa [tinyCost, h] using (show (B i).sum ≤ tiny (B i) by simpa [h] using h')
    · simpa [tinyCost, h] using And.intro
        (show (B i).sum - (countBig (B i):ℝ)*upperEdge ≤ tiny (B i) by linarith only [(stats i).2.2.2])
        (stats i).1

private theorem blocks_of_rank {N : ℕ} {t : Fin N → ℝ} (ht : ∀ i, 0 < t i)
    (htot : ∑ i, t i = 1) (h : rankTest t) :
    ∃ B : Fin N → List ℝ, (∀ i, B i ≠ []) ∧ fundamental (List.ofFn B).flatten ∧
      ∀ i, (B i).sum = t i := by
  obtain ⟨r, d, _, hd, hw⟩ := (rank_iff_allocations ht).mp h
  let v := fun i => (t i - d i) / r i
  let B := fun i => List.replicate (r i) (v i) ++ [d i]
  have hsmall i : d i < ε :=
    (Finset.single_le_sum (fun j _ => (hw j).1.le) (Finset.mem_univ i)).trans_lt hd
  have hmacro i (hi : r i ≠ 0) : lowerEdge < v i ∧ v i < upperEdge := by
    have hp : (0:ℝ) < r i := by exact_mod_cast Nat.pos_of_ne_zero hi
    have hh := (hw i).2
    rw [if_neg hi] at hh
    exact ⟨(lt_div_iff₀ hp).mpr (by linarith only [hh.1]), (div_lt_iff₀ hp).mpr (by linarith only [hh.2])⟩
  have hsum i : (B i).sum = t i := by
    by_cases hi : r i = 0
    · simpa [B, hi] using (show d i = t i by simpa [hi] using (hw i).2)
    · simp [B, v, List.sum_replicate, nsmul_eq_mul, mul_div_cancel₀, hi]
  have hshape i : Shape (B i) := by
    intro y hy
    simp only [B, List.mem_append, List.mem_replicate, List.mem_singleton] at hy
    rcases hy with ⟨hi,rfl⟩ | rfl
    · have hh := hmacro i hi
      exact ⟨by linarith only [edges.1, edges.2.1, hh.1], hh.2, Or.inr hh.1⟩
    · exact ⟨(hw i).1, by linarith only [hsmall i, edges.1, edges.2.1, edges.2.2.1], Or.inl (hsmall i)⟩
  have hcost i : tiny (B i) = d i := by
    by_cases hi : r i = 0
    · simp [B, tiny, hi, hsmall]
    · have hm : ¬ v i < ε := by linarith only [(hmacro i hi).1, edges.1, edges.2.1]
      simp [B, tiny, List.sum_replicate, hm, hsmall]
  refine ⟨B, fun i => by simp [B], (fundamental_shape _).mpr ⟨?_, ?_, ?_⟩, hsum⟩
  · simpa only [sum_blocks, hsum] using htot
  · intro y hy
    obtain ⟨b, hb, hy⟩ := List.mem_flatten.mp hy
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hb
    exact hshape i y hy
  · simpa only [cost_blocks, hcost] using hd

/-- For a positive normalized vector, the older existential block test is
equivalent to the strict per-coordinate rank test, including both endpoints. -/
theorem coagulation_iff_rank {N : ℕ} {t : Fin N → ℝ} (ht : ∀ i, 0 < t i)
    (hsum : ∑ i, t i = 1) :
    (∃ b : List (List ℝ), (∀ w ∈ b, w ≠ []) ∧ fundamental b.flatten ∧
      (b.map List.sum).Perm (List.ofFn t)) ↔ rankTest t := by
  constructor
  · rintro ⟨b, _, hf, hp⟩
    have order : ∃ w : List (List ℝ), List.ofFn t = w.map List.sum ∧ w.Perm b := by
      change Relation.Comp (fun x y => x = List.map List.sum y) List.Perm (List.ofFn t) b
      rw [List.eq_map_comp_perm]
      exact hp.symm
    obtain ⟨w, hw, hp'⟩ := order
    have hflat : w.flatten.Perm b.flatten := by simpa only [List.flatMap_id] using hp'.flatMap_right id
    obtain ⟨hs, hshape, hc⟩ := (fundamental_shape _).mp hf
    have hwf : fundamental w.flatten := (fundamental_shape _).mpr
      ⟨hflat.sum_eq.trans hs, fun x hx => hshape x (hflat.mem_iff.mp hx),
        (hflat.map (fun y => if y < ε then y else 0)).sum_eq.trans_lt hc⟩
    obtain ⟨K, B, rfl⟩ : ∃ K, ∃ B : Fin K → List ℝ, List.ofFn B = w :=
      ⟨w.length, w.get, List.ofFn_get w⟩
    have hn : N = K := by simpa using congrArg List.length hw
    subst K
    apply rank_of_blocks B hwf
    intro i
    have hmap : List.ofFn t = List.ofFn (fun j => (B j).sum) := by simpa [List.map_ofFn, Function.comp_def] using hw
    exact (congrFun (List.ofFn_injective hmap) i).symm
  · intro h
    obtain ⟨B, hn, hf, he⟩ := blocks_of_rank ht hsum h
    refine ⟨List.ofFn B, ?_, hf, ?_⟩
    · exact List.forall_mem_ofFn_iff.mpr hn
    · simp [List.map_ofFn, Function.comp_def, he]

private theorem normalized {n : ℕ} (hn : 1 < n) :
    ∑ i : Fin n.primeFactorsList.length, Real.log (n.primeFactorsList.get i) / Real.log n = 1 := by
  have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn)
  rw [← Finset.sum_div, div_eq_one_iff_eq hlog.ne']
  have h : ∀ x ∈ n.primeFactorsList.map (fun p : ℕ => (p:ℝ)), x ≠ 0 := by
    intro x hx
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hx
    exact_mod_cast (Nat.prime_of_mem_primeFactorsList hp).ne_zero
  have hh := Real.log_list_prod h
  rw [← Nat.cast_list_prod, Nat.prod_primeFactorsList (by omega)] at hh
  rw [← List.sum_ofFn, hh, List.map_map]
  exact congrArg List.sum ((List.map_ofFn n.primeFactorsList.get (fun p : ℕ => Real.log p)).symm.trans
    (by rw [List.ofFn_get]; rfl))

theorem good_iff_rank_good (n : ℕ) : Source.good n ↔ Direct.good n := by
  unfold Source.good Direct.good
  refine and_congr_right (fun hn => and_congr_right (fun _ => ?_))
  let t := fun i : Fin n.primeFactorsList.length => Real.log (n.primeFactorsList.get i) / Real.log n
  have hp i : 0 < t i := div_pos (Real.log_pos (by exact_mod_cast
    (Nat.prime_of_mem_primeFactorsList (List.get_mem n.primeFactorsList i)).one_lt))
    (Real.log_pos (by exact_mod_cast hn))
  have hd : List.ofFn t = profile n n.primeFactorsList := by
    unfold profile
    change List.ofFn t = (n.primeFactorsList.flatMap (fun p : ℕ => [(p:ℝ)])).map _
    rw [← List.map_eq_flatMap, List.map_map]
    exact (List.map_ofFn n.primeFactorsList.get (fun p : ℕ => Real.log p / Real.log n)).symm.trans
      (by rw [List.ofFn_get]; rfl)
  rw [← hd]
  exact coagulation_iff_rank hp (normalized hn)

theorem phi_eq_legacy {n : ℕ} {x : ℝ} (hn : n ∈ Vaughan.interval (x/2)) :
    phi x n = Closing.phi x n := by
  simp [phi, Closing.phi, F, G, Closing.F, Closing.G, hn, good_iff_rank_good]

theorem whole_eq_legacy (a x : ℝ) : whole a x = Closing.largeProduct a x := by
  unfold whole largeSum Closing.largeProduct Vaughan.total
  apply Finset.sum_congr rfl
  intro n hn
  simp only [Closing.term, phi_eq_legacy hn]

theorem lower_of_covariance {a : ℝ} (hl : Closing.LowerLedger) (hr : Closing.Reduction a) :
    LowerLedger a := by
  intro e he
  have h : 0 < e/2 := by linarith
  filter_upwards [hl _ h, hr _ h] with x hL hR
  rw [whole_eq_legacy]
  linarith only [hL, (abs_le.mp hR).2]

theorem infinite_of_profile_and_outside {a : Set.Ioo (0:ℝ) 1} {κ : ℝ} (hk : 0 < κ)
    (hl : Closing.LowerLedger) (hr : Closing.Reduction a)
    (hc : Calibration a) (hp : ProfileUpper) (hj : J ≤ enclosure)
    (ho : OutsideBound a κ) (hs : ∀ᶠ x : ℝ in Filter.atTop, 0 < Sb x) :
    Set.Infinite {p : ℕ | p.Prime ∧ (p+2).Prime} :=
  infinite_of_direct hk (lower_of_covariance hl hr) (box_payment hc hp hj hs) ho hs

end
end REAL1B.FM.Direct
#print axioms REAL1B.FM.Direct.rank_iff_allocations
#print axioms REAL1B.FM.Direct.coagulation_iff_rank
#print axioms REAL1B.FM.Direct.good_iff_rank_good
#print axioms REAL1B.FM.Direct.phi_eq_legacy
#print axioms REAL1B.FM.Direct.whole_eq_legacy
#print axioms REAL1B.FM.Direct.lower_of_covariance
#print axioms REAL1B.FM.Direct.infinite_of_profile_and_outside
