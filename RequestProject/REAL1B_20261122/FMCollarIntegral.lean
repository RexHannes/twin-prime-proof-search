import RequestProject.REAL1B_20261122.FMCollar

/-! Continuous reference integrals for the rank-two and rank-three positive
collars in Gold 4.58 Part V §9, equations (8) and (9). -/
namespace REAL1B.FM.Collar
open Source MeasureTheory
noncomputable section
open Classical

def pairIntegral (l u : ℝ) := ∫ t in Set.Icc l u, 1/(t*(1-t))

theorem pair_band {l u : ℝ} (hl : 0<l) (hlu : l≤u) (hu : u≤1/2) :
    IntegrableOn (fun t : ℝ => 1/(t*(1-t))) (Set.Icc l u) ∧
    pairIntegral l u ≤ (u-l)/(l*(1-l)) := by
  have hd (t : ℝ) (ht : t ∈ Set.Icc l u) : 0<t*(1-t) :=
    mul_pos (hl.trans_le ht.1) (by linarith only [ht.2,hu])
  have hi : IntegrableOn (fun t : ℝ => 1/(t*(1-t))) (Set.Icc l u) :=
    ContinuousOn.integrableOn_compact isCompact_Icc (continuousOn_const.div (by fun_prop) (fun t ht => (hd t ht).ne'))
  refine ⟨hi,?_⟩
  have hm : ∀ t ∈ Set.Icc l u, 1/(t*(1-t)) ≤ 1/(l*(1-l)) := by
    intro t ht
    apply one_div_le_one_div_of_le (mul_pos hl (by linarith))
    nlinarith only [mul_nonneg (sub_nonneg.mpr ht.1) (show 0 ≤ 1-l-t by linarith only [ht.2,hlu,hu])]
  have hh := setIntegral_mono_on hi (integrableOn_const measure_Icc_lt_top.ne) measurableSet_Icc hm
  rw [setIntegral_const,Real.volume_real_Icc_of_le hlu,smul_eq_mul] at hh
  simpa only [pairIntegral,div_eq_mul_inv,one_mul] using hh

theorem two_bands :
    pairIntegral Direct.lowerEdge (1/5) + pairIntegral β (1/2) ≤
    ε/(Direct.lowerEdge*(1-Direct.lowerEdge)) + 2*ε/(β*(1-β)) := by
  have h₁ := (pair_band (l:=Direct.lowerEdge) (u:=1/5) (by norm_num [Direct.lowerEdge,ε])
    (by norm_num [Direct.lowerEdge,ε]) (by norm_num)).2
  have h₂ := (pair_band (l:=β) (u:=1/2) (by norm_num [β,ε]) (by norm_num [β,ε]) (by norm_num)).2
  rw [show (1:ℝ)/5-Direct.lowerEdge=ε by unfold Direct.lowerEdge; ring] at h₁
  rw [show (1:ℝ)/2-β=2*ε by unfold β; ring] at h₂
  exact add_le_add h₁ h₂

def tripleRect := Set.Icc (fun _ : Fin 2 => Direct.lowerEdge) (fun _ => (1:ℝ)/5)
def tripleDensity (t : Fin 2 → ℝ) := 1/(t 0*t 1*(1-t 0-t 1))

theorem triple_band : IntegrableOn tripleDensity tripleRect ∧
    (∫ t in tripleRect, tripleDensity t)/2 ≤ ε^2/(2*Direct.lowerEdge^2*(3/5)) := by
  let a := Direct.lowerEdge
  have ha : 0<a := by norm_num [a,Direct.lowerEdge,ε]
  have hle : a ≤ 1/5 := by norm_num [a,Direct.lowerEdge,ε]
  have hlo {t : Fin 2 → ℝ} (ht : t ∈ tripleRect) : a^2*(3/5) ≤ t 0*t 1*(1-t 0-t 1) := by
    have h0 := ht.1 0; have h1 := ht.1 1; have u0 := ht.2 0; have u1 := ht.2 1
    change a≤t 0 at h0; change a≤t 1 at h1
    change t 0≤1/5 at u0; change t 1≤1/5 at u1
    exact mul_le_mul (by simpa only [pow_two] using mul_le_mul h0 h1 ha.le (ha.le.trans h0)) (by linarith) (by norm_num) (mul_nonneg (ha.le.trans h0) (ha.le.trans h1))
  have hd : 0<a^2*(3/5) := by positivity
  have hi : IntegrableOn tripleDensity tripleRect :=
    ContinuousOn.integrableOn_compact isCompact_Icc (continuousOn_const.div (by fun_prop) (fun t ht => (hd.trans_le (hlo ht)).ne'))
  refine ⟨hi,?_⟩
  have hh := setIntegral_mono_on hi (integrableOn_const measure_Icc_lt_top.ne) measurableSet_Icc
    (fun t ht => one_div_le_one_div_of_le hd (hlo ht))
  have hv : volume.real tripleRect = ε^2 := by
    change (volume (Set.Icc (fun _ : Fin 2 => a) (fun _ => (1:ℝ)/5))).toReal = _
    rw [Real.volume_Icc_pi_toReal (fun _ => hle)]
    simp [a,Direct.lowerEdge]
  rw [setIntegral_const,hv,smul_eq_mul] at hh
  change _ ≤ ε^2/(2*a^2*(3/5))
  calc
    _ ≤ (ε^2*(1/(a^2*(3/5))))/2 := div_le_div_of_nonneg_right hh (by norm_num)
    _ = _ := by ring

end
end REAL1B.FM.Collar
#print axioms REAL1B.FM.Collar.pair_band
#print axioms REAL1B.FM.Collar.two_bands
#print axioms REAL1B.FM.Collar.triple_band
