import RequestProject.REAL1B_20261122.FMCollarIntegral

/-! Gold 4.58, Part V §9. The four projected coordinates of an active
five-prime output occupy a translated simplex. The change of variables preserves
Lebesgue measure and the fifth coordinate is determined by the other four. -/
namespace REAL1B.FM.Collar
open MeasureTheory Finset
noncomputable section
open Classical

def slackSimplex (n : ℕ) (h : ℝ) : Set (Fin n → ℝ) := {t | (∀ i, 0 ≤ t i) ∧ ∑ i, t i ≤ h}

private theorem simplex_measurable (n : ℕ) (h : ℝ) : MeasurableSet (slackSimplex n h) := by
  change MeasurableSet ({t : Fin n → ℝ | ∀ i, 0 ≤ t i} ∩ {t | ∑ i, t i ≤ h})
  apply MeasurableSet.inter _ (measurableSet_le (by fun_prop) measurable_const)
  change MeasurableSet {t : Fin n → ℝ | ∀ i, 0 ≤ t i}
  rw [Set.setOf_forall]
  exact MeasurableSet.iInter (fun i => measurableSet_le measurable_const (measurable_pi_apply i))

private theorem simplex_sub (n : ℕ) (h : ℝ) : slackSimplex n h ⊆ Set.Icc (fun _ => (0:ℝ)) (fun _ => h) := by
  intro t ht
  exact ⟨ht.1,fun i => (single_le_sum (f:=t) (fun i _ => ht.1 i) (mem_univ i)).trans ht.2⟩

private theorem simplex_finite (n : ℕ) (h : ℝ) : volume (slackSimplex n h) < ⊤ :=
  (measure_mono (simplex_sub n h)).trans_lt measure_Icc_lt_top

/-- Lebesgue volume of the nonnegative coordinate simplex of side length h. -/
theorem simplex_volume (n : ℕ) {h : ℝ} (hh : 0≤h) :
    volume.real (slackSimplex n h) = h^n/(n.factorial:ℝ) := by
  induction n generalizing h with
  | zero =>
    have he : slackSimplex 0 h = Set.Icc (fun _ => (0:ℝ)) (fun _ => h) := by
      apply Set.Subset.antisymm (simplex_sub _ _)
      intro t ht
      exact ⟨ht.1,by simpa using hh⟩
    rw [he,Measure.real,Real.volume_Icc_pi_toReal (fun _ => hh)]
    simp
  | succ n ih =>
    let E := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0
    have mp : MeasurePreserving E volume volume := volume_preserving_piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0
    let F := (slackSimplex (n+1) h).indicator (fun _ => (1:ℝ))
    let G : ℝ × (Fin n → ℝ) → ℝ := fun p => if p.1 ∈ Set.Icc 0 h then
      (slackSimplex n (h-p.1)).indicator (fun _ => (1:ℝ)) p.2 else 0
    have heq (t : Fin (n+1) → ℝ) : G (E t) = F t := by
      have hsplit : t ∈ slackSimplex (n+1) h ↔ t 0 ∈ Set.Icc 0 h ∧ (fun i : Fin n => t i.succ) ∈ slackSimplex n (h-t 0) := by
        constructor
        · intro ht
          have hl := ht.2
          rw [Fin.sum_univ_succ] at hl
          exact ⟨⟨ht.1 0,(simplex_sub _ _ ht).2 0⟩,fun i => ht.1 i.succ,by linarith⟩
        · rintro ⟨ht,htail⟩
          refine ⟨fun i => Fin.cases ht.1 (fun j => htail.1 j) i,?_⟩
          rw [Fin.sum_univ_succ]
          linarith only [htail.2]
      change (if t 0 ∈ Set.Icc 0 h then (slackSimplex n (h-t 0)).indicator (fun _ => (1:ℝ)) _ else 0) = _
      simp only [Set.indicator,F,hsplit]
      have htail : (E t).2 = (fun j : Fin n => t j.succ) := by
        funext j
        change t ((0 : Fin (n+1)).succAbove j) = t j.succ
        simp
      rw [htail]
      split_ifs <;> tauto
    have hf : Integrable F := (integrable_indicator_iff (simplex_measurable _ _)).mpr (integrableOn_const (simplex_finite _ _).ne)
    have hg : Integrable G := (mp.integrable_comp_emb E.measurableEmbedding).mp (by simpa only [Function.comp_def,heq] using hf)
    have hsection (x : ℝ) : (∫ t, G (x,t)) = (Set.Icc 0 h).indicator (fun x => (h-x)^n/(n.factorial:ℝ)) x := by
      by_cases hx : x ∈ Set.Icc 0 h
      · simp only [G,hx,if_true,Set.indicator_of_mem hx]
        rw [integral_indicator_const _ (simplex_measurable _ _),smul_eq_mul,mul_one,ih (sub_nonneg.mpr hx.2)]
      · simp only [G,if_neg hx,Set.indicator_of_notMem hx,integral_zero]
    calc
      _ = ∫ t, F t := by rw [show (∫ t, F t) = _ from integral_indicator_const _ (simplex_measurable _ _),smul_eq_mul,mul_one]
      _ = ∫ p, G p := by simpa only [heq] using mp.integral_comp' G
      _ = ∫ x, ∫ t, G (x,t) := integral_prod _ hg
      _ = ∫ x in (0:ℝ)..h, (h-x)^n/(n.factorial:ℝ) := by
        simp_rw [hsection]
        rw [integral_indicator measurableSet_Icc,integral_Icc_eq_integral_Ioc,intervalIntegral.integral_of_le hh]
      _ = _ := by
        rw [intervalIntegral.integral_div,intervalIntegral.integral_comp_sub_left (fun x => x^n) h,sub_self,sub_zero,integral_pow]
        rw [Nat.factorial_succ,Nat.cast_mul,Nat.cast_succ]
        simp only [zero_pow (Nat.succ_ne_zero _),sub_zero]
        field_simp

def fiveDomain : Set (Fin 4 → ℝ) :=
  {t | (∀ i, Direct.lowerEdge ≤ t i) ∧ ∑ i, t i ≤ 1-Direct.lowerEdge}

def fifthProduct (t : Fin 4 → ℝ) := (∏ i, t i)*(1-∑ i, t i)

/-- The original ordered prime coordinates satisfy the projected collar inequalities. -/
theorem native_five_domain {n : ℕ} (hs : Squarefree n) (hg : Direct.good n)
    (hh : Source.kernelH n ≠ 0) {t : Fin 4 → ℝ} {f : ℝ}
    (hf : n.primeFactorsList.map (Box.coord n) = [t 0, t 1, t 2, t 3, f]) :
    t ∈ fiveDomain ∧ f = 1 - ∑ i, t i ∧ max (Source.kernelH n) 0 ≤ 3 := by
  obtain ⟨hl, hheight, _⟩ := rank_five_simplex hs hg hh hf
  have hsum := coordinate_sum hg.1
  rw [hf] at hsum
  simp only [List.sum_cons, List.sum_nil, add_zero] at hsum
  have hf' : Direct.lowerEdge < f := hl f (by simp)
  have heq : f = 1 - ∑ i, t i := by
    simp [Fin.sum_univ_succ]
    linarith
  refine ⟨⟨?_, by linarith only [hf', heq]⟩, heq, hheight⟩
  intro i
  exact (hl (t i) (by fin_cases i <;> simp)).le

private theorem five_measurable : MeasurableSet fiveDomain := by
  change MeasurableSet ({t : Fin 4 → ℝ | ∀ i, Direct.lowerEdge ≤ t i} ∩ {t | ∑ i, t i ≤ 1-Direct.lowerEdge})
  apply MeasurableSet.inter _ (measurableSet_le (by fun_prop) measurable_const)
  rw [Set.setOf_forall]
  exact MeasurableSet.iInter (fun i => measurableSet_le measurable_const (measurable_pi_apply i))

/-- Translation by the lower edge preserves four-dimensional Lebesgue volume. -/
theorem rank_five_volume : volume.real fiveDomain = (5*Source.ε)^4/(Nat.factorial 4:ℝ) := by
  let A : Fin 4 → ℝ := fun _ => Direct.lowerEdge
  have hpre : (fun t => t+A) ⁻¹' fiveDomain = slackSimplex 4 (5*Source.ε) := by
    ext t
    have hsum : ∑ i, (t+A) i = (∑ i, t i)+4*Direct.lowerEdge := by
      simp [Pi.add_apply,A,Finset.sum_add_distrib]
    change ((∀ i, Direct.lowerEdge ≤ t i+Direct.lowerEdge) ∧ ∑ i, (t+A) i ≤ 1-Direct.lowerEdge) ↔
      (∀ i, 0≤t i) ∧ ∑ i, t i ≤ 5*Source.ε
    rw [hsum]
    simp only [le_add_iff_nonneg_left,and_congr_right_iff]
    intro _
    unfold Direct.lowerEdge
    constructor <;> intro <;> linarith
  have hp := (measurePreserving_add_right volume A).measure_preimage five_measurable.nullMeasurableSet
  rw [hpre] at hp
  exact (congrArg ENNReal.toReal hp).symm.trans (simplex_volume 4 (by norm_num [Source.ε]))

theorem rank_five_integral :
    IntegrableOn (fun t => 3/fifthProduct t) fiveDomain ∧
    (∫ t in fiveDomain, 3/fifthProduct t)/(Nat.factorial 5:ℝ) ≤
      3*(5*Source.ε)^4/((Nat.factorial 5:ℝ)*Nat.factorial 4*Direct.lowerEdge^5) := by
  let a := Direct.lowerEdge
  have ha : 0<a := by norm_num [a,Direct.lowerEdge,Source.ε]
  have hprod (t) (ht : t ∈ fiveDomain) : a^5 ≤ fifthProduct t := by
    have h₁ : a^4 ≤ ∏ i, t i := by
      calc
        _ = ∏ _ : Fin 4, a := by simp
        _ ≤ _ := Finset.prod_le_prod (fun _ _ => ha.le) (fun i _ => ht.1 i)
    rw [pow_succ]
    exact mul_le_mul h₁ (by linarith only [ht.2]) ha.le (Finset.prod_nonneg (fun i _ => ha.le.trans (ht.1 i)))
  have hb : 0<a^5 := pow_pos ha _
  have hfinite : volume fiveDomain ≠ ⊤ := by
    have hsub : fiveDomain ⊆ Set.Icc (fun _ => (0:ℝ)) (fun _ => (1:ℝ)) := by
      intro t ht
      have nonneg (i) := ha.le.trans (ht.1 i)
      exact ⟨nonneg,fun i => (single_le_sum (f:=t) (fun j _ => nonneg j) (mem_univ i)).trans
        (by linarith only [ht.2,ha] : (∑ j, t j) ≤ 1)⟩
    exact ((measure_mono hsub).trans_lt measure_Icc_lt_top).ne
  have hm (t) (ht : t∈fiveDomain) : 3/fifthProduct t ≤ 3/a^5 :=
    div_le_div_of_nonneg_left (by norm_num) hb (hprod t ht)
  have hi : IntegrableOn (fun t => 3/fifthProduct t) fiveDomain := by
    apply (integrableOn_const (C:=3/a^5) hfinite).mono'
    · exact (show Measurable (fun t => (3:ℝ)/fifthProduct t) by unfold fifthProduct; fun_prop).aestronglyMeasurable
    filter_upwards [ae_restrict_mem five_measurable] with t ht
    rw [Real.norm_eq_abs,abs_of_nonneg (div_nonneg (by norm_num) (hb.le.trans (hprod t ht)))]
    exact hm t ht
  have hh := setIntegral_mono_on hi (integrableOn_const hfinite) five_measurable hm
  rw [setIntegral_const,rank_five_volume,smul_eq_mul] at hh
  refine ⟨hi,?_⟩
  calc
    _ ≤ _ := div_le_div_of_nonneg_right hh (show (0:ℝ)≤Nat.factorial 5 by positivity)
    _ = _ := by dsimp [a]; ring

end
end REAL1B.FM.Collar
#print axioms REAL1B.FM.Collar.simplex_volume
#print axioms REAL1B.FM.Collar.native_five_domain
#print axioms REAL1B.FM.Collar.rank_five_volume
#print axioms REAL1B.FM.Collar.rank_five_integral
