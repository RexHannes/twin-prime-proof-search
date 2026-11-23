import RequestProject.REAL1B_20261122.FMProfileTransfer
import RequestProject.REAL1B_20261122.FMIntegral

/-! Physical five-prime profile tests with unit weights. Two copies of the full
box supply its constant height. The four other tests retain both original faces. -/
namespace REAL1B.FM.Profile
open Filter MeasureTheory Source Vaughan Analytic Direct
noncomputable section
open Classical

def weakFace (v s : ℝ) : Prop := 1/2 + (if 1/5 < v then 2 else 1)*ε ≤ s
def strictFace (s : ℝ) : Prop := 1/2 - ε < s

def test (j : Fin 6) (t : Fin 4 → ℝ) : Prop :=
  ![True,True,weakFace (t 2) (t 0+t 1+t 3),strictFace (t 0+t 1+t 3),
    weakFace (t 3) (t 0+t 1+t 2),strictFace (t 0+t 1+t 2)] j

private theorem test_measurable (j : Fin 6) : MeasurableSet {t | test j t} := by
  have weak {v s : (Fin 4 → ℝ) → ℝ} (hv : Measurable v) (hs : Measurable s) :
      MeasurableSet {t | weakFace (v t) (s t)} := by
    have hcut : Measurable (fun t => if (1:ℝ)/5 < v t then (2:ℝ) else 1) :=
      Measurable.ite (measurableSet_lt measurable_const hv) measurable_const measurable_const
    exact measurableSet_le (measurable_const.add (hcut.mul measurable_const)) hs
  fin_cases j
  · exact MeasurableSet.const True
  · exact MeasurableSet.const True
  · exact weak (measurable_pi_apply _) (by fun_prop)
  · exact measurableSet_lt measurable_const (show Measurable (fun t : Fin 4 → ℝ => t 0+t 1+t 3) by fun_prop)
  · exact weak (measurable_pi_apply _) (by fun_prop)
  · exact measurableSet_lt measurable_const (show Measurable (fun t : Fin 4 → ℝ => t 0+t 1+t 2) by fun_prop)

theorem height_from_tests (t : Fin 4 → ℝ) : ∑ j : Fin 6, (if test j t then (1:ℝ) else 0) = profileH t := by
  simp only [Fin.sum_univ_succ,test,Matrix.cons_val_zero,Matrix.cons_val_succ,Fin.sum_univ_zero,
    if_true,add_zero,weakFace,strictFace,profileH,face]
  ring

def sliceDensity (j : Fin 6) (t : Fin 4 → ℝ) := if test j t then Grid.densityAt t / profileH t else 0
def sliceIntegral (j : Fin 6) : ℝ := ∫ t, sliceDensity j t

private theorem height_two (t : Fin 4 → ℝ) : 2 ≤ profileH t := by unfold profileH face; split_ifs <;> norm_num

theorem integrable_slice (j : Fin 6) : Integrable (sliceDensity j) := by
  apply Grid.integrable_densityAt.mono'
  · exact (Measurable.ite (test_measurable j) (Grid.measurable_densityAt.div Grid.measurable_profileH) measurable_const).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro t
  have hd := Grid.densityAt_nonneg t
  have h₁ : 1 ≤ profileH t := le_trans (by norm_num) (height_two t)
  unfold sliceDensity
  split_ifs
  · rw [Real.norm_eq_abs,abs_of_nonneg (div_nonneg hd (by linarith))]
    exact div_le_self hd h₁
  · simpa using hd

theorem integral_from_tests : ∑ j : Fin 6, sliceIntegral j = J := by
  unfold sliceIntegral
  rw [← integral_finset_sum _ (fun j _ => integrable_slice j)]
  change (∫ t, ∑ j : Fin 6, sliceDensity j t) = ∫ t, Grid.densityAt t
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro t
  have hs : ∀ j, sliceDensity j t = (if test j t then (1:ℝ) else 0)*(Grid.densityAt t/profileH t) := by
    intro j; by_cases h : test j t <;> simp [sliceDensity,h]
  simp_rw [hs]
  rw [← Finset.sum_mul,height_from_tests]
  field_simp [show profileH t ≠ 0 by linarith only [height_two t]]

def unitWeight (j : Fin 6) (n : ℕ) : ℝ := if Closing.boxes n ∧ test j (Box.coordinates n) then 1 else 0

theorem weight_from_tests (n : ℕ) : ∑ j, unitWeight j n = Box.profileWeight n := by
  by_cases h : Closing.boxes n
  · simpa only [unitWeight,h,true_and,Box.profileWeight,if_true] using height_from_tests (Box.coordinates n)
  · simp [unitWeight,Box.profileWeight,h]

def countTest (w : ℕ → ℝ) (x : ℝ) (j : Fin 6) := total (x/2) (fun n => w n * unitWeight j n)

theorem count_recombination (x : ℝ) (w : ℕ → ℝ) :
    ∑ j, countTest w x j = total (x/2) (fun n => w n * Box.profileWeight n) := by
  unfold countTest total
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun n _ => by rw [← Finset.mul_sum,weight_from_tests])

theorem mean_of_unit_counts
    (h : ∀ j, negligible (fun x => H2.series*countTest (fun _ => 1) x j - sliceIntegral j*reference x) scale) :
    MeanDensity := by
  intro e he
  have ht : 0<e/6 := by linarith
  filter_upwards [Filter.eventually_all.mpr (fun j => h j _ ht)] with x hx
  have hh := Finset.sum_le_sum (s:=Finset.univ) (fun j _ => hx j)
  have htriangle := Finset.abs_sum_le_sum_abs (s:=Finset.univ) (fun j : Fin 6 =>
    H2.series*countTest (fun _ => 1) x j - sliceIntegral j*reference x)
  rw [Finset.sum_sub_distrib,← Finset.mul_sum,← Finset.sum_mul,integral_from_tests,count_recombination] at htriangle
  simp only [one_mul] at htriangle
  exact htriangle.trans (by simpa [Finset.sum_const,nsmul_eq_mul,← mul_assoc,show (6:ℝ)*(e/6)=e by ring] using hh)

def roughTest (x : ℝ) (j : Fin 6) := countTest (fun n => sieve (Closing.cutU x) (n-2)*Real.log (n-2:ℕ)) x j

theorem rough_of_unit_counts (h : ∀ j, ∀ e : ℝ, 0<e → ∀ᶠ x : ℝ in atTop,
    roughTest x j ≤ (cStar*sliceIntegral j+e)*reference x) : RoughDensity := by
  intro e he
  have ht : 0<e/6 := by linarith
  filter_upwards [Filter.eventually_all.mpr (fun j => h j _ ht)] with x hx
  have hh := Finset.sum_le_sum (s:=Finset.univ) (fun j _ => hx j)
  dsimp only [roughTest] at hh
  rw [count_recombination,← Finset.sum_mul,Finset.sum_add_distrib,← Finset.mul_sum,integral_from_tests] at hh
  simpa [Finset.sum_const,nsmul_eq_mul,profileRough,show (6:ℝ)*(e/6)=e by ring] using hh

end
end REAL1B.FM.Profile
#print axioms REAL1B.FM.Profile.height_from_tests
#print axioms REAL1B.FM.Profile.integrable_slice
#print axioms REAL1B.FM.Profile.integral_from_tests
#print axioms REAL1B.FM.Profile.weight_from_tests
#print axioms REAL1B.FM.Profile.count_recombination
#print axioms REAL1B.FM.Profile.mean_of_unit_counts
#print axioms REAL1B.FM.Profile.rough_of_unit_counts
