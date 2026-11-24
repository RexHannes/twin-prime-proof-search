import Mathlib

namespace Gate1B.Gold50

open Finset
open scoped BigOperators

/-- The detector profile used by Gold 5.0. -/
def g (t : ℚ) : ℚ := 4 * t * (1 - t)

/-- Gold 5.0 cutpoints `u_j = 21/100 + j/2000`. -/
def cut (j : ℕ) : ℚ := 21 / 100 + j / 2000

/-- Gold 5.0 staircase weights `w_0, ..., w_150`. -/
def weight : ℕ → ℚ
  | 0 => g (cut 0)
  | j + 1 => g (cut (j + 1)) - g (cut j)

lemma cut_step (j : ℕ) : cut (j + 1) - cut j = (1 : ℚ) / 2000 := by
  have hcast : ((j + 1 : ℕ) : ℚ) = (j : ℚ) + 1 := by norm_num
  unfold cut
  rw [hcast]
  ring

lemma g_diff (a b : ℚ) : g a - g b = 4 * (a - b) * (1 - (a + b)) := by
  unfold g
  ring

/-- Every Gold 5.0 cut is positive. -/
lemma cut_pos (j : ℕ) : 0 < cut j := by
  unfold cut
  positivity

/-- For the indexed range used in Gold 5.0, all cuts stay below `1/2`. -/
lemma cut_lt_half_of_le150 {j : ℕ} (hj : j ≤ 150) : cut j < (1 : ℚ) / 2 := by
  have hj' : (j : ℚ) ≤ 150 := by exact_mod_cast hj
  have hdiv : (j : ℚ) / 2000 ≤ 150 / 2000 := by
    exact (div_le_div_of_nonneg_right hj' (by positivity : (0 : ℚ) ≤ 2000))
  unfold cut
  have hfinal : 21 / 100 + (j : ℚ) / 2000 ≤ 21 / 100 + 150 / 2000 := by
    linarith
  have hnum : 21 / 100 + (150 : ℚ) / 2000 = 57 / 200 := by norm_num
  have h57 : (57 : ℚ) / 200 < (1 : ℚ) / 2 := by norm_num
  calc
    21 / 100 + (j : ℚ) / 2000 ≤ 21 / 100 + (150 : ℚ) / 2000 := hfinal
    _ = 57 / 200 := hnum
    _ < (1 : ℚ) / 2 := h57

/-- Positivity of the initial weight. -/
lemma weight_zero_pos : 0 < weight 0 := by
  unfold weight g cut
  norm_num

/-- Positivity of every incremental weight up to index `150`. -/
lemma weight_succ_pos_of_lt150 {j : ℕ} (hj : j < 150) : 0 < weight (j + 1) := by
  have hj1 : j + 1 ≤ 150 := Nat.succ_le_of_lt hj
  have hj0 : j ≤ 150 := Nat.le_trans (Nat.le_succ j) hj1
  have hsum : cut (j + 1) + cut j < (1 : ℚ) := by
    have h1 : cut (j + 1) < (1 : ℚ) / 2 := cut_lt_half_of_le150 hj1
    have h0 : cut j < (1 : ℚ) / 2 := cut_lt_half_of_le150 hj0
    linarith
  have hfactor : 0 < 1 - (cut (j + 1) + cut j) := by linarith
  have hdiff : 0 < g (cut (j + 1)) - g (cut j) := by
    rw [g_diff, cut_step]
    have : 0 < 4 * ((1 : ℚ) / 2000) * (1 - (cut (j + 1) + cut j)) := by
      positivity
    simpa [mul_assoc] using this
  simpa [weight] using hdiff

/-- Nonnegativity of every weight in the Gold 5.0 staircase range. -/
theorem weight_nonneg_of_le150 {j : ℕ} (hj : j ≤ 150) : 0 ≤ weight j := by
  cases j with
  | zero => exact le_of_lt weight_zero_pos
  | succ k =>
      have hk : k < 150 := Nat.lt_of_succ_le hj
      exact le_of_lt (weight_succ_pos_of_lt150 hk)

/-- Telescoping identity for staircase weights. -/
theorem sum_weights_range_eq_g_cut (n : ℕ) :
    ∑ j ∈ range (n + 1), weight j = g (cut n) := by
  induction n with
  | zero =>
      simp [weight]
  | succ n ih =>
      rw [sum_range_succ, ih]
      simp [weight]

/-- Exact staircase representation for all Gold 5.0 cut indices. -/
theorem staircase_exact (j : ℕ) :
    g (cut j) = ∑ k ∈ range (j + 1), weight k := by
  symm
  exact sum_weights_range_eq_g_cut j

end Gate1B.Gold50
