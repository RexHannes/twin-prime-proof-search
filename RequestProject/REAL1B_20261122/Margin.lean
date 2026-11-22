import RequestProject.REAL1B_20261122.H2Source

/-! A rational upper bound on the ordered triple integral is sufficient to
certify strict positivity. No decimal approximation to that integral is used. -/
namespace REAL1B.H2
open MeasureTheory Filter Set
noncomputable section

private def poly (t u : ℝ) := 208*t^2 + 208*t*u - 208*t + 208*u^2 - 208*u + 97
private def outer (t : ℝ) := -468*t^3 + 468*t^2 - 395*t/2 + 187/6

private theorem reciprocal_simplex {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hs : x+y+z=1) :
    64 / ((1+x)*(1+y)*(1+z)) ≤ 32 - 13*(x*y+y*z+x*z) := by
  let s := x*y+y*z+x*z
  let q := x*y*z
  have hs0 : 0 ≤ s := by dsimp [s]; positivity
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hsq : s ≤ 1/3 := by
    dsimp [s]
    nlinarith [sq_nonneg (x-y), sq_nonneg (y-z), sq_nonneg (x-z),
      congrArg (fun t : ℝ => t^2) hs]
  have hq : 3*q ≤ s := by
    dsimp [q,s]
    nlinarith [mul_nonneg (mul_nonneg hx hy) (show 0 ≤ 1-z by linarith),
      mul_nonneg (mul_nonneg hx hz) (show 0 ≤ 1-y by linarith),
      mul_nonneg (mul_nonneg hy hz) (show 0 ≤ 1-x by linarith)]
  have hfac : (1+x)*(1+y)*(1+z) = 2+s+q := by dsimp [s,q]; linarith only [hs]
  apply (div_le_iff₀ (by positivity)).mpr
  change 64 ≤ (32-13*s) * _
  rw [hfac]
  nlinarith [mul_nonneg hs0 (show 0 ≤ 32-13*(2+s+q) by linarith)]

private theorem reciprocal_le (t u : ℝ) (ht : 1/4 ≤ t) (hu : t ≤ u) (hv : u ≤ (1-t)/2) :
    1 / (t*u*(1-t-u)) ≤ poly t u := by
  have h := reciprocal_simplex (x := 4*t-1) (y := 4*u-1) (z := 4*(1-t-u)-1)
    (by linarith) (by linarith) (by linarith) (by ring)
  have he : (1+(4*t-1))*(1+(4*u-1))*(1+(4*(1-t-u)-1)) = 64*(t*u*(1-t-u)) := by ring
  rw [he] at h
  have hden : 0 < t*u*(1-t-u) := by
    have : 0 < 1-t-u := by linarith
    have : 0 < t := by linarith
    have : 0 < u := by linarith
    positivity
  apply (div_le_iff₀ hden).mpr
  have h' := (div_le_iff₀ (by positivity : 0 < 64*(t*u*(1-t-u)))).mp h
  unfold poly
  linarith only [h']

private theorem eval_inner (t : ℝ) :
    (∫ u in t..(1-t)/2, poly t u) = outer t := by
  let A := fun u : ℝ => (208*t^2-208*t+97)*u + (104*t-104)*u^2 + (208/3)*u^3
  have hd (u : ℝ) : HasDerivAt A (poly t u) u := by
    unfold A poly
    convert (((hasDerivAt_id u).const_mul (208*t^2-208*t+97)).add
      (((hasDerivAt_id u).pow 2).const_mul (104*t-104))).add
      (((hasDerivAt_id u).pow 3).const_mul (208/3)) using 1
    simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := A) (fun u _ => hd u)
    (by unfold poly; exact Continuous.intervalIntegrable (by fun_prop) _ _)]
  unfold A outer
  ring

private theorem eval_outer : (∫ t in (1/4:ℝ)..(1/3), outer t) = 115/768 := by
  let A := fun t : ℝ => (-117)*t^4 + 156*t^3 + (-395/4)*t^2 + (187/6)*t
  have hd (t : ℝ) : HasDerivAt A (outer t) t := by
    unfold A outer
    convert (((((hasDerivAt_id t).pow 4).const_mul (-117)).add
      (((hasDerivAt_id t).pow 3).const_mul 156)).add
      (((hasDerivAt_id t).pow 2).const_mul (-395/4))).add
      ((hasDerivAt_id t).const_mul (187/6)) using 1
    simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := A) (fun t _ => hd t)
    (by unfold outer; exact Continuous.intervalIntegrable (by fun_prop) _ _)]
  norm_num [A]

def tripleSlice (t : ℝ) := ∫ u : ℝ in Ioo t ((1-t)/2), 1 / (t*u*(1-t-u))

private theorem inner_bounds {t : ℝ} (ht : t ∈ Ioo (1/4:ℝ) (1/3)) :
    0 ≤ tripleSlice t ∧ tripleSlice t ≤ outer t := by
  have hb : t ≤ (1-t)/2 := by linarith [ht.2]
  have hpos (u : ℝ) (h : u ∈ Ioo t ((1-t)/2)) : 0 ≤ 1 / (t*u*(1-t-u)) := by
    have : 0 < t := by linarith [ht.1]
    have : 0 < u := by linarith [h.1]
    have : 0 < 1-t-u := by linarith [h.2,ht.2]
    positivity
  unfold tripleSlice
  constructor
  · exact integral_nonneg_of_ae ((ae_restrict_iff' measurableSet_Ioo).mpr
      (Eventually.of_forall hpos))
  · rw [← eval_inner, intervalIntegral.integral_of_le hb, integral_Ioc_eq_integral_Ioo]
    apply integral_mono_of_nonneg ((ae_restrict_iff' measurableSet_Ioo).mpr
      (Eventually.of_forall hpos))
    · exact ((show Continuous (poly t) by unfold poly; fun_prop).continuousOn.integrableOn_compact
        isCompact_Icc).mono_set Ioo_subset_Icc_self
    · exact (ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall (fun u hu =>
        reciprocal_le t u ht.1.le hu.1.le hu.2.le))

/-- Both bounded simplex integrals exist as ordinary Lebesgue integrals. -/
theorem triple_integrability :
    (∀ t ∈ Ioo (1/4:ℝ) (1/3), IntegrableOn (fun u : ℝ => 1/(t*u*(1-t-u))) (Ioo t ((1-t)/2))) ∧
    IntegrableOn tripleSlice (Ioo (1/4:ℝ) (1/3)) := by
  constructor
  · intro t ht
    have hc : ContinuousOn (fun u : ℝ => 1/(t*u*(1-t-u))) (Icc t ((1-t)/2)) := by
      apply continuousOn_const.div (by fun_prop)
      intro u hu
      have : 0 < t := by linarith [ht.1]
      have : 0 < u := by linarith [hu.1]
      have : 0 < 1-t-u := by linarith [hu.2,ht.2]
      positivity
    exact (hc.integrableOn_compact isCompact_Icc).mono_set Ioo_subset_Icc_self
  · have hm : Measurable tripleSlice := by
      unfold tripleSlice
      simp_rw [← integral_indicator measurableSet_Ioo]
      apply StronglyMeasurable.measurable
      apply StronglyMeasurable.integral_prod_right
      apply Measurable.stronglyMeasurable
      classical
      simp only [Function.uncurry_def, Set.indicator_apply]
      apply Measurable.ite _ (by fun_prop) (by fun_prop)
      exact (measurableSet_lt measurable_fst measurable_snd).inter
        (measurableSet_lt measurable_snd (show Measurable (fun p : ℝ × ℝ => (1-p.1)/2) by fun_prop))
    have ho : IntegrableOn outer (Ioo (1/4:ℝ) (1/3)) volume := ((show Continuous outer by unfold outer; fun_prop).continuousOn.integrableOn_compact
      (isCompact_Icc (α := ℝ) (a := 1/4) (b := 1/3))).mono_set Ioo_subset_Icc_self
    apply ho.mono' hm.aestronglyMeasurable
    apply (ae_restrict_iff' measurableSet_Ioo).mpr
    apply Eventually.of_forall
    intro t ht
    simpa [Real.norm_eq_abs, abs_of_nonneg (inner_bounds ht).1] using (inner_bounds ht).2

theorem triple_integral_upper : I3 ≤ 115/768 := by
  rw [← eval_outer, intervalIntegral.integral_of_le (by norm_num : (1/4:ℝ) ≤ 1/3),
    integral_Ioc_eq_integral_Ioo]
  change (∫ t in Ioo (1/4:ℝ) (1/3), tripleSlice t) ≤ _
  apply integral_mono_of_nonneg
  · exact (ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall (fun _ h => (inner_bounds h).1))
  · exact ((show Continuous outer by unfold outer; fun_prop).continuousOn.integrableOn_compact
      isCompact_Icc).mono_set Ioo_subset_Icc_self
  · exact (ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall (fun _ h => (inner_bounds h).2))

theorem margin_floor : 1/4000 < margin := by
  have h : (2:ℝ)^84 < 3^53 := by norm_num
  have hl := Real.log_lt_log (by positivity) h
  rw [Real.log_pow, Real.log_pow] at hl
  norm_num1 at hl
  unfold margin cB rho3 tripleCoeff
  linarith only [hl, Real.log_two_lt_d9, triple_integral_upper]

theorem margin_positive : 0 < margin :=
  lt_trans (by norm_num : (0:ℝ) < 1/4000) margin_floor

end
end REAL1B.H2

#print axioms REAL1B.H2.triple_integrability
#print axioms REAL1B.H2.triple_integral_upper
#print axioms REAL1B.H2.margin_floor
#print axioms REAL1B.H2.margin_positive
