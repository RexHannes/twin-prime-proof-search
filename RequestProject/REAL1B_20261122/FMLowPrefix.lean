import RequestProject.REAL1B_20261122.FMProfileTransfer
import RequestProject.REAL1B_20261122.FMOwners
import RequestProject.REAL1B_20261122.FMCompleteLabel

namespace REAL1B.FM.Analytic
open Filter Vaughan Source Closing Direct
noncomputable section
open Classical

def lowPrefix (a x : ℝ) := total (x/2) (fun n => if clean x n then
  sieve (roughW a x) (n-2) * mu (n-2)^2 * (∑ l ∈ (n-2).divisors,
    if l.Prime ∧ cutU x < (l:ℝ) ∧ (l:ℝ) ≤ x^(0.2697:ℝ) then
      -(Real.log l * Owners.truncated (Owners.edge (cutU x) (cutD x) l) ((n-2)/l)) else 0) *
    outsideProfile x n else 0)

theorem low_prefix_source (a : ℝ) : ∀ᶠ x : ℝ in atTop, lowLabel a x = lowPrefix a x := by
  filter_upwards [small_power (by norm_num : (0.2697:ℝ) ≤ 1/2)] with x hx
  unfold lowLabel cleanSum lowPrefix total
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hc : clean x n
  · simp only [if_pos hc,labelSum]
    congr 2
    apply Finset.sum_congr rfl
    intro l hl
    split_ifs with h
    · have hnlt : (l:ℝ) < (n-2:ℕ) := lt_of_le_of_lt h.2.2 (hx n hn)
      have hq : (n-2)/l ≠ 1 := by
        intro he
        have hEq := Nat.div_mul_cancel (Nat.mem_divisors.mp hl).1
        rw [he,one_mul] at hEq
        exact (ne_of_lt hnlt) (by exact_mod_cast hEq)
      rw [Owners.owner_row h.1,if_neg hq]
      ring
    · rfl
  · simp [hc]

theorem log_saving {f : ℝ → ℝ} {C : ℝ}
    (h : ∀ᶠ x : ℝ in atTop, |f x| ≤ C * (x / (Real.log x)^2)) : negligible f scale := by
  intro e he
  filter_upwards [h,Real.tendsto_log_atTop.eventually_gt_atTop (C/e),eventually_gt_atTop (1:ℝ)]
    with x hf hL hx
  have hlog := Real.log_pos hx
  have hCe : C ≤ e*Real.log x := by linarith only [(div_lt_iff₀ he).mp hL]
  apply hf.trans
  unfold scale
  rw [← mul_div_assoc,← mul_div_assoc,div_le_div_iff₀ (sq_pos_of_pos hlog) hlog]
  nlinarith only [mul_le_mul_of_nonneg_right hCe (mul_nonneg (by linarith : 0 ≤ x) hlog.le)]

theorem low_label_of_prefix_saving {a C : ℝ} (hs : ScaleLower)
    (h : ∀ᶠ x : ℝ in atTop, |lowPrefix a x| ≤ C * (x/(Real.log x)^2)) : LowLabelEstimate a := by
  have h₁ := negligible_comparator (log_saving h) hs
  intro e he
  filter_upwards [low_prefix_source a,h₁ e he] with x hx hbound
  rwa [hx]

end
end REAL1B.FM.Analytic
#print axioms REAL1B.FM.Analytic.low_prefix_source
#print axioms REAL1B.FM.Analytic.log_saving
#print axioms REAL1B.FM.Analytic.low_label_of_prefix_saving
