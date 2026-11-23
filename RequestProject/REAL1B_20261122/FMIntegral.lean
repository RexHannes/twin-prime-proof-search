import RequestProject.REAL1B_20261122.FMDirect
import RequestProject.REAL1B_20261122.FMGridData

/-! Direct domination of the actual four-dimensional integral by the finite
outward-rounded cubature. Closed mesh cells cover the open box interiors. -/
namespace REAL1B.FM.Grid
open Direct Source MeasureTheory
noncomputable section
open Classical

def Coord.atFin (p : Coord) : Fin 4 → ℕ := ![p.a, p.b, p.c, p.d]

private def lower (m : Coord) (i : Fin 4) : ℝ := m.atFin i / 800
private def upper (m : Coord) (i : Fin 4) : ℝ := (m.atFin i + 1 : ℝ)/800
private def cell (m : Coord) := Set.Icc (lower m) (upper m)
private def product5 (t : Fin 4 → ℝ) := (∏ i, t i) * (1-∑ i, t i)
private def weight (m : Coord) : ℝ := height m / product5 (lower m)
def densityAt (t : Fin 4 → ℝ) := if boxDomain t then profileH t / product5 t else 0

private theorem valid_iff (p : Coord) : valid p = true ↔ Closing.admissible p.a p.b p.c p.d := by
  simp only [valid, decide_eq_true_eq, Closing.admissible]

private theorem bin_mem (p : Coord) : p ∈ bins ↔ valid p = true := by
  constructor
  · intro h
    simp only [bins, List.mem_flatMap] at h
    obtain ⟨d,_,c,_,h⟩ := h
    unfold atPair at h
    split at h
    · obtain ⟨_, _, h⟩ := List.mem_flatMap.mp h
      exact (List.mem_filter.mp h).2
    · simp at h
  · intro h
    have hh := (valid_iff p).mp h
    unfold Closing.admissible at hh
    obtain ⟨_,hab,hbc,hcd,hd,_,_,_,_,_,_,_,_,_,hcut⟩ := hh
    simp only [bins, List.mem_flatMap, List.mem_range]
    refine ⟨p.d, by omega, p.c,hcd,?_⟩
    simp only [atPair, if_pos hcut, List.mem_flatMap, List.mem_filter, List.mem_range, List.mem_map]
    exact ⟨p.b,hbc,⟨p.a,hab,by cases p; rfl⟩,h⟩

private theorem sub_mem {m p : Coord} (h : m ∈ subcells p) :
    ∀ i, 8 * p.atFin i ≤ m.atFin i ∧ m.atFin i+1 ≤ 8*(p.atFin i+1) := by
  simp only [subcells, List.mem_flatMap, List.mem_map, List.mem_range] at h
  obtain ⟨a,ha,b,hb,c,hc,d,hd,rfl⟩ := h
  intro i
  fin_cases i <;> simp [Coord.atFin] <;> omega

private theorem cover {t : Fin 4 → ℝ} (ht : boxDomain t) :
    ∃ p ∈ bins, ∃ m ∈ subcells p, t ∈ cell m := by
  obtain ⟨b, h, hb⟩ := ht
  let p := Coord.mk (b 0) (b 1) (b 2) (b 3)
  have hcoord (i : Fin 4) : p.atFin i = b i := by fin_cases i <;> rfl
  let v := fun i => 800*t i - 8*b i
  have h0 i : 0 ≤ v i := by dsimp [v]; linarith only [(hb i).1]
  have h8 i : ⌊v i⌋₊ < 8 := (Nat.floor_lt (h0 i)).mpr (by dsimp [v]; linarith only [(hb i).2])
  let m := Coord.mk (8*p.a+⌊v 0⌋₊) (8*p.b+⌊v 1⌋₊) (8*p.c+⌊v 2⌋₊) (8*p.d+⌊v 3⌋₊)
  have hm (i) : m.atFin i = 8 * b i + ⌊v i⌋₊ := by fin_cases i <;> rfl
  refine ⟨p, (bin_mem p).mpr ((valid_iff p).mpr h), m, ?_, ?_⟩
  · simp only [subcells, List.mem_flatMap, List.mem_range, List.mem_map]
    exact ⟨_, h8 0, _, h8 1, _, h8 2, _, h8 3,rfl⟩
  · constructor <;> intro i <;> simp only [lower, upper, hm, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    · linarith only [Nat.floor_le (h0 i)]
    · have hh := Nat.lt_floor_add_one (v i)
      dsimp [v] at hh
      linarith

private theorem ordered_cell {p m : Coord} (hp : p ∈ bins) (hm : m ∈ subcells p) :
    (∀ i, 0 < lower m i) ∧ ∀ i, upper m i ≤ 1 - ∑ j, upper m j := by
  have ha := (valid_iff p).mp ((bin_mem p).mp hp)
  unfold Closing.admissible at ha
  have s := sub_mem hm
  obtain ⟨ha,hb,hc,hd,_,_,_,_,_,_,hf,_⟩ := ha
  have coord (i : Fin 4) : 3 ≤ p.atFin i ∧ p.atFin i ≤ p.d := by
    fin_cases i <;> simp [Coord.atFin] <;> omega
  constructor
  · intro i
    have hpos : 0 < m.atFin i := by have := (s i).1; have := (coord i).1; omega
    exact div_pos (by exact_mod_cast hpos) (by norm_num)
  · intro i
    have hi : m.atFin i+1 + (m.a+1) + (m.b+1) + (m.c+1) + (m.d+1) ≤ 800 := by
      have h := (s i).2
      have h' := (coord i).2
      have h₁ := (s 0).2; have h₂ := (s 1).2; have h₃ := (s 2).2; have h₄ := (s 3).2
      change m.a+1 ≤ 8*(p.a+1) at h₁
      change m.b+1 ≤ 8*(p.b+1) at h₂
      change m.c+1 ≤ 8*(p.c+1) at h₃
      change m.d+1 ≤ 8*(p.d+1) at h₄
      omega
    have hr : (m.atFin i:ℝ)+1+((m.a:ℝ)+1)+(m.b+1)+(m.c+1)+(m.d+1) ≤ 800 := by exact_mod_cast hi
    simp only [Fin.sum_univ_four, upper]
    change ((m.atFin i:ℝ)+1)/800 ≤ 1-(((m.a:ℝ)+1)/800+((m.b:ℝ)+1)/800+
      ((m.c:ℝ)+1)/800+((m.d:ℝ)+1)/800)
    linarith

private theorem product_mono {l t : Fin 4 → ℝ} (hp : ∀ i, 0 < l i) (hle : l ≤ t)
    (ho : ∀ i, t i ≤ 1-∑ j, t j) : product5 l ≤ product5 t := by
  have hq (i) : 0 ≤ t i := (hp i).le.trans (hle i)
  have step (q Q y z w : ℝ) (h : q ≤ Q) (hr : q+Q+y+z+w ≤ 1) (hyzw : 0 ≤ y*z*w) :
      q*y*z*w*(1-(q+y+z+w)) ≤ Q*y*z*w*(1-(Q+y+z+w)) := by
    have hh := mul_nonneg (sub_nonneg.mpr h) (sub_nonneg.mpr hr)
    nlinarith only [mul_nonneg hh hyzw]
  have H (i) := ho i
  simp only [Fin.sum_univ_four] at H
  have h₀ := hle 0; have h₁ := hle 1; have h₂ := hle 2; have h₃ := hle 3
  have a := step _ _ (l 1) (l 2) (l 3) h₀ (by linarith only [H 0,h₀,h₁,h₂,h₃])
    (mul_nonneg (mul_nonneg (hp 1).le (hp 2).le) (hp 3).le)
  have b := step _ _ (t 0) (l 2) (l 3) h₁ (by linarith only [H 1,h₁,h₂,h₃])
    (mul_nonneg (mul_nonneg (hq 0) (hp 2).le) (hp 3).le)
  have c := step _ _ (t 0) (t 1) (l 3) h₂ (by linarith only [H 2,h₂,h₃])
    (mul_nonneg (mul_nonneg (hq 0) (hq 1)) (hp 3).le)
  have d := step _ _ (t 0) (t 1) (t 2) h₃ (by linarith only [H 3,h₃])
    (mul_nonneg (mul_nonneg (hq 0) (hq 1)) (hq 2))
  simp only [product5, Fin.prod_univ_four, Fin.sum_univ_four]
  linarith only [a,b,c,d]

private theorem face_le {v s : ℝ} {k : ℕ} (h : s ≤ (k:ℝ)/800) :
    face v s ≤ faceCount k := by
  have he : 0 < (if (1:ℝ)/5 < v then 2 else 1) * ε := by
    split_ifs <;> norm_num [ε]
  have h₁ (hpos : 1/2 + (if (1:ℝ)/5 < v then 2 else 1) * ε ≤ s) : 400 < k := by
    exact_mod_cast (show (400:ℝ) < k by linarith)
  have h₂ (hpos : 1/2 - ε < s) : 400 ≤ k := by
    by_contra! hk
    have h' : (k:ℝ) ≤ 399 := by exact_mod_cast (show k ≤ 399 by omega)
    norm_num [ε] at hpos
    linarith
  have gate (P Q : Prop) [Decidable P] [Decidable Q] (hh : P → Q) :
      (if P then (1:ℝ) else 0) ≤ (Nat.cast (if Q then 1 else 0 : ℕ) : ℝ) := by
    by_cases a : P
    · simp [a,hh a]
    · by_cases b : Q <;> simp [a,b]
  unfold face faceCount
  rw [Nat.cast_add]
  exact add_le_add (gate _ _ h₁) (gate _ _ h₂)

private theorem cell_height {t : Fin 4 → ℝ} {m : Coord} (h : t ∈ cell m) :
    profileH t ≤ height m := by
  have hu (i) := h.2 i
  have hs (i j k) : t i + t j + t k ≤ ((m.atFin i + m.atFin j + m.atFin k + 3 : ℕ):ℝ)/800 := by
    have a := hu i; have b := hu j; have c := hu k
    dsimp only [upper] at a b c
    push_cast
    linarith
  have a := face_le (v := t 2) (hs 0 1 3)
  have b := face_le (v := t 3) (hs 0 1 2)
  change face (t 2) _ ≤ (faceCount (m.a+m.b+m.d+3):ℝ) at a
  change face (t 3) _ ≤ (faceCount (m.a+m.b+m.c+3):ℝ) at b
  unfold height profileH
  push_cast
  linarith

private theorem grid_pos {m p : Coord} (hp : p ∈ bins) (hm : m ∈ subcells p) :
    0 < den m ∧ product5 (lower m) = (den m:ℝ)/800^5 := by
  obtain ⟨hpos, htop⟩ := ordered_cell hp hm
  have hcoord (i) : 0 < m.atFin i := by
    have hh := hpos i
    dsimp [lower] at hh
    exact_mod_cast (show (0:ℝ) < m.atFin i by linarith)
  have hsum : m.a+m.b+m.c+m.d < 800 := by
    have hh := htop 0
    simp only [Fin.sum_univ_four, upper] at hh
    change ((m.a:ℝ)+1)/800 ≤ 1-(((m.a:ℝ)+1)/800+((m.b:ℝ)+1)/800+
      ((m.c:ℝ)+1)/800+((m.d:ℝ)+1)/800) at hh
    exact_mod_cast (show (m.a:ℝ)+m.b+m.c+m.d < 800 by linarith [show (0:ℝ) ≤ m.a by positivity])
  refine ⟨Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (hcoord 0) (hcoord 1)) (hcoord 2))
    (hcoord 3)) (Nat.sub_pos_of_lt hsum), ?_⟩
  simp only [den, Nat.cast_mul, Nat.cast_sub hsum.le, Nat.cast_add, Nat.cast_ofNat,
    product5, Fin.sum_univ_four, Fin.prod_univ_four, lower]
  change _ * (1 - ((m.a:ℝ)/800 + (m.b:ℝ)/800 + (m.c:ℝ)/800 + (m.d:ℝ)/800)) = _
  change (m.a:ℝ)/800*((m.b:ℝ)/800)*((m.c:ℝ)/800)*((m.d:ℝ)/800)*_ = _
  ring

private theorem prod_pos {m p : Coord} (hp : p ∈ bins) (hm : m ∈ subcells p) :
    0 < product5 (lower m) := by
  obtain ⟨h, he⟩ := grid_pos hp hm
  rw [he]
  positivity

private theorem height_nonneg (t : Fin 4 → ℝ) : 0 ≤ profileH t := by
  unfold profileH face
  split_ifs <;> norm_num

private theorem inside_denom {m p : Coord} {t : Fin 4 → ℝ} (hp : p ∈ bins)
    (hm : m ∈ subcells p) (ht : t ∈ cell m) : product5 (lower m) ≤ product5 t := by
  obtain ⟨h,ho⟩ := ordered_cell hp hm
  have hs : ∑ i, t i ≤ ∑ i, upper m i := Finset.sum_le_sum (fun i _ => ht.2 i)
  exact product_mono h ht.1 (fun i => (ht.2 i).trans ((ho i).trans (by linarith)))

private def value (m : Coord) := (cell m).indicator (fun _ => weight m)

private theorem value_nonneg {p m : Coord} (hp : p ∈ bins) (hm : m ∈ subcells p) (t) :
    0 ≤ value m t := by
  apply Set.indicator_nonneg
  intro _ _
  exact div_nonneg (Nat.cast_nonneg _) (prod_pos hp hm).le

private theorem value_upper {p m : Coord} {t : Fin 4 → ℝ} (hp : p ∈ bins)
    (hm : m ∈ subcells p) (ht : t ∈ cell m) (hb : boxDomain t) : densityAt t ≤ value m t := by
  rw [value, Set.indicator_of_mem ht, densityAt, if_pos hb, weight]
  exact div_le_div₀ (by positivity) (cell_height ht) (prod_pos hp hm) (inside_denom hp hm ht)

private theorem cell_vol (m : Coord) : MeasureTheory.volume.real (cell m) = (1/800:ℝ)^4 := by
  have h : lower m ≤ upper m := fun i => by dsimp [lower, upper]; linarith
  rw [Measure.real, cell, Real.volume_Icc_pi_toReal h]
  simp [lower, upper, show ∀ a : ℝ, (a+1)/800-a/800=1/800 by intro; ring]

private theorem integrable_value (m : Coord) : Integrable (value m) := by
  apply (integrable_indicator_iff measurableSet_Icc).mpr
  exact integrableOn_const (measure_Icc_lt_top).ne

private theorem integral_value {p m : Coord} (hp : p ∈ bins) (hm : m ∈ subcells p) :
    (∫ t, value m t) ≤ (upperNumerator m:ℝ)/scale := by
  obtain ⟨h,he⟩ := grid_pos hp hm
  have ceil_bound : height m * 800 * scale ≤ upperNumerator m * den m := by
    have hmod := Nat.mod_lt (height m * 800 * scale + den m - 1) h
    have hdiv := Nat.mod_add_div (height m * 800 * scale + den m - 1) (den m)
    unfold upperNumerator
    rw [Nat.mul_comm (den m)] at hdiv
    omega
  have hr : (height m:ℝ)*800*scale ≤ (upperNumerator m:ℝ)*den m := by exact_mod_cast ceil_bound
  rw [value, integral_indicator_const _ (show MeasurableSet (cell m) from measurableSet_Icc), cell_vol, smul_eq_mul, weight, he]
  have hd : (0:ℝ) < den m := by exact_mod_cast h
  have hs : (0:ℝ) < scale := by norm_num [scale]
  field_simp
  linarith only [hr]

private theorem flatten_sum {α β : Type*} (s : List α) (f : α → List β) (g : β → ℕ) :
    ((s.flatMap f).map g).sum = (s.map (fun x => ((f x).map g).sum)).sum := by
  induction s with
  | nil => rfl
  | cons _ _ ih => simp [ih]

private theorem mesh_total : ((bins.flatMap subcells).map upperNumerator).sum = totalUpper := by
  simp only [flatten_sum, bins]
  rfl

theorem domain_measurable : MeasurableSet {t | boxDomain t} := by
  change MeasurableSet {t : Fin 4 → ℝ | ∃ b : Fin 4 → ℕ, Closing.admissible (b 0) (b 1) (b 2) (b 3) ∧
    ∀ i, (b i : ℝ)/100 < t i ∧ t i < ((b i : ℝ)+1)/100}
  rw [Set.setOf_exists]
  apply MeasurableSet.iUnion
  intro b
  apply MeasurableSet.inter (MeasurableSet.const _)
  change MeasurableSet {t : Fin 4 → ℝ | ∀ i, (b i : ℝ)/100 < t i ∧ t i < ((b i:ℝ)+1)/100}
  rw [Set.setOf_forall]
  apply MeasurableSet.iInter
  intro i
  exact (measurableSet_lt measurable_const (measurable_pi_apply i)).inter
    (measurableSet_lt (measurable_pi_apply i) measurable_const)

theorem measurable_profileH : Measurable profileH := by
  have mf {v s : (Fin 4 → ℝ) → ℝ} (hv : Measurable v) (hs : Measurable s) :
      Measurable (fun t => face (v t) (s t)) := by
    have hcut : Measurable (fun t => if (1:ℝ)/5 < v t then (2:ℝ) else 1) :=
      Measurable.ite (measurableSet_lt measurable_const hv) measurable_const measurable_const
    have hface : Measurable (fun t => (1:ℝ)/2 + (if (1:ℝ)/5 < v t then (2:ℝ) else 1)*ε) :=
      measurable_const.add (hcut.mul measurable_const)
    exact (Measurable.ite (measurableSet_le hface hs) measurable_const measurable_const).add
      (Measurable.ite (measurableSet_lt measurable_const hs) measurable_const measurable_const)
  have ha := mf (measurable_pi_apply (2 : Fin 4)) (s:=fun t => t 0+t 1+t 3) (by fun_prop)
  have hb := mf (measurable_pi_apply (3 : Fin 4)) (s:=fun t => t 0+t 1+t 2) (by fun_prop)
  exact (measurable_const.add ha).add hb

theorem measurable_densityAt : Measurable densityAt := by
  unfold densityAt
  exact Measurable.ite domain_measurable (measurable_profileH.div (by unfold product5; fun_prop)) measurable_const

theorem densityAt_nonneg (t : Fin 4 → ℝ) : 0 ≤ densityAt t := by
  unfold densityAt
  split_ifs with h
  · obtain ⟨p,hp,m,hm,ht⟩ := cover h
    exact div_nonneg (height_nonneg t) ((prod_pos hp hm).trans_le (inside_denom hp hm ht)).le
  · rfl

/-- The actual integral is bounded by a closed expression over natural numbers.
Every retained centile box is subdivided in each of its four free coordinates. -/
private theorem density_certificate : Integrable densityAt ∧ J ≤ (totalUpper : ℝ)/scale := by
  let L := bins.flatMap subcells
  let f := fun t => (L.map (fun m => value m t)).sum
  have hm {m} (h : m ∈ L) : ∃ p ∈ bins, m ∈ subcells p := List.mem_flatMap.mp h
  have hn (t) : ∀ y ∈ L.map (fun m => value m t), 0 ≤ y := by
    intro y hy
    obtain ⟨m,h,rfl⟩ := List.mem_map.mp hy
    obtain ⟨p,hp,hc⟩ := hm h
    exact value_nonneg hp hc t
  have hbound (t) : 0 ≤ densityAt t ∧ densityAt t ≤ f t := by
    by_cases hb : boxDomain t
    · obtain ⟨p,hp,m,hc,ht⟩ := cover hb
      refine ⟨?_, (value_upper hp hc ht hb).trans (List.single_le_sum (hn t) _ ?_)⟩
      · rw [densityAt, if_pos hb]
        exact div_nonneg (height_nonneg t)
          ((prod_pos hp hc).trans_le (inside_denom hp hc ht)).le
      · exact List.mem_map.mpr ⟨m, List.mem_flatMap.mpr ⟨p,hp,hc⟩,rfl⟩
    · simp only [densityAt, if_neg hb, le_refl, true_and]
      exact List.sum_nonneg (hn t)
  have sumBound (s : List Coord) (h : ∀ m ∈ s, m ∈ L) :
      Integrable (fun t => (s.map (fun m => value m t)).sum) ∧
        (∫ t, (s.map (fun m => value m t)).sum) ≤ ((s.map upperNumerator).sum:ℝ)/scale := by
    induction s with
    | nil => simp
    | cons m s ih =>
      obtain ⟨p,hp,hc⟩ := hm (h m (by simp))
      obtain ⟨hg,hs⟩ := ih (fun m hm => h m (by simp [hm]))
      simp only [List.map_cons, List.sum_cons, Nat.cast_add, add_div]
      exact ⟨(integrable_value m).add hg, by
        rw [integral_add (integrable_value m) hg]
        exact add_le_add (integral_value hp hc) hs⟩
  obtain ⟨hg,hs⟩ := sumBound L (fun _ => id)
  have hd : Integrable densityAt := hg.mono' measurable_densityAt.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun t => by
      rw [Real.norm_eq_abs,abs_of_nonneg (hbound t).1]
      exact (hbound t).2))
  refine ⟨hd,?_⟩
  change (∫ t, densityAt t) ≤ _
  rw [← mesh_total]
  exact (integral_mono hd hg (fun t => (hbound t).2)).trans hs

theorem integrable_densityAt : Integrable densityAt := density_certificate.1

theorem integral_le_mesh : J ≤ (totalUpper : ℝ)/scale := density_certificate.2

private def witness : Fin 4 → ℕ := ![4,5,8,39]
private def leftCorner (i : Fin 4) : ℝ := (witness i : ℝ)/100 + 1/400
private def rightCorner (i : Fin 4) : ℝ := (witness i : ℝ)/100 + 3/400

/-- A closed interior rectangle of side 1/200 in the admissible (4,5,8,39) box. -/
theorem integral_lower_witness : (1/200:ℝ)^4 ≤ J := by
  let W := Set.Icc leftCorner rightCorner
  have hrect : leftCorner ≤ rightCorner := fun i => by dsimp [leftCorner,rightCorner]; linarith
  have hdom {t} (ht : t ∈ W) : boxDomain t := by
    refine ⟨witness,?_,fun i => ?_⟩
    · change Closing.admissible 4 5 8 39
      norm_num [Closing.admissible]
    · have hl := ht.1 i
      have hu := ht.2 i
      dsimp [leftCorner,rightCorner] at hl hu
      constructor <;> linarith
  have hp {t} (h : boxDomain t) : 0 < product5 t := by
    obtain ⟨p,hp,m,hm,ht⟩ := cover h
    exact (prod_pos hp hm).trans_le (inside_denom hp hm ht)
  have hbound (t) : W.indicator (fun _ => (1:ℝ)) t ≤ densityAt t := by
    by_cases ht : t ∈ W
    · rw [Set.indicator_of_mem ht,densityAt,if_pos (hdom ht)]
      have hmin (i) : 0 ≤ t i := by
        have h := ht.1 i
        exact (show 0 ≤ leftCorner i by unfold leftCorner; positivity).trans h
      have hmax (i) : t i ≤ 1 := (ht.2 i).trans (by fin_cases i <;> change (_:ℝ)/100+3/400 ≤ 1 <;> norm_num [witness,Matrix.cons_val_fin_one,Matrix.cons_val_succ])
      have h1 : (∏ i, t i) ≤ 1 := Finset.prod_le_one (fun i _ => hmin i) (fun i _ => hmax i)
      have h2 : 1 - ∑ i, t i ≤ 1 := by linarith only [Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => hmin i)]
      have h3 : product5 t ≤ 1 := (mul_le_mul_of_nonneg_left h2 (Finset.prod_nonneg (fun i _ => hmin i))).trans (by simpa using h1)
      have hh : 2 ≤ profileH t := by unfold profileH face; split_ifs <;> norm_num
      exact (one_le_div (hp (hdom ht))).mpr (by linarith)
    · rw [Set.indicator_of_notMem ht,densityAt]
      split_ifs with h
      · exact div_nonneg (height_nonneg t) (hp h).le
      · rfl
  have hw : Integrable (W.indicator (fun _ => (1:ℝ))) :=
    (integrable_indicator_iff measurableSet_Icc).mpr (integrableOn_const measure_Icc_lt_top.ne)
  have hh := integral_mono hw integrable_densityAt hbound
  change _ ≤ ∫ t, densityAt t
  rw [integral_indicator_const _ (show MeasurableSet W from measurableSet_Icc),smul_eq_mul,mul_one,
    Measure.real,Real.volume_Icc_pi_toReal hrect] at hh
  simp [leftCorner,rightCorner] at hh
  norm_num at hh ⊢
  exact hh

theorem integral_pos : 0 < J := lt_of_lt_of_le (by norm_num : 0 < (1/200:ℝ)^4) integral_lower_witness

end
end REAL1B.FM.Grid
#print axioms REAL1B.FM.Grid.domain_measurable
#print axioms REAL1B.FM.Grid.measurable_densityAt
#print axioms REAL1B.FM.Grid.integrable_densityAt
#print axioms REAL1B.FM.Grid.integral_lower_witness
#print axioms REAL1B.FM.Grid.integral_pos
#print axioms REAL1B.FM.Grid.integral_le_mesh
