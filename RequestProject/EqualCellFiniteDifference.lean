import RequestProject.P7Certificate

namespace HalfSieve

set_option maxHeartbeats 2000000

open scoped BigOperators

noncomputable section

def equalCellCoeff (r : ℕ) (P : ℚ → ℚ) : ℚ :=
  ∑ j ∈ Finset.range (r / 2 + 1),
    (-1 : ℚ) ^ j * Nat.choose r j * P ((j : ℚ) / r)

lemma p7_equalCell_six : equalCellCoeff 6 p7Rat = 0 := by
  norm_num [equalCellCoeff, p7Rat, q7Rat, p7N, p7a1, p7a3, p7a5, p7a7, Finset.sum_range_succ, Nat.choose]

lemma p7_equalCell_eight : equalCellCoeff 8 p7Rat = 0 := by
  norm_num [equalCellCoeff, p7Rat, q7Rat, p7N, p7a1, p7a3, p7a5, p7a7, Finset.sum_range_succ, Nat.choose]

lemma p7_equalCell_nine : equalCellCoeff 9 p7Rat = 0 := by
  norm_num [equalCellCoeff, p7Rat, q7Rat, p7N, p7a1, p7a3, p7a5, p7a7, Finset.sum_range_succ, Nat.choose]

lemma p7_equalCell_ten : equalCellCoeff 10 p7Rat = 0 := by
  norm_num [equalCellCoeff, p7Rat, q7Rat, p7N, p7a1, p7a3, p7a5, p7a7, Finset.sum_range_succ, Nat.choose]

lemma p7_equalCell_seven_exact :
    equalCellCoeff 7 p7Rat = -3284674560 / 66296035043 := by
  norm_num [equalCellCoeff, p7Rat, q7Rat, p7N, p7a1, p7a3, p7a5, p7a7, Finset.sum_range_succ, Nat.choose]

lemma p7_equalCell_twelve_exact :
    equalCellCoeff 12 p7Rat = -79951295 / 625975776 := by
  norm_num [equalCellCoeff, p7Rat, q7Rat, p7N, p7a1, p7a3, p7a5, p7a7, Finset.sum_range_succ, Nat.choose]

lemma p7_equalCell_fourteen_exact :
    equalCellCoeff 14 p7Rat = 135275555036 / 198888105129 := by
  norm_num [equalCellCoeff, p7Rat, q7Rat, p7N, p7a1, p7a3, p7a5, p7a7, Finset.sum_range_succ, Nat.choose]

lemma p7_equalCell_seven_neg : equalCellCoeff 7 p7Rat < 0 := by
  rw [p7_equalCell_seven_exact]
  norm_num

lemma p7_equalCell_twelve_neg : equalCellCoeff 12 p7Rat < 0 := by
  rw [p7_equalCell_twelve_exact]
  norm_num

lemma p7_equalCell_fourteen_pos : 0 < equalCellCoeff 14 p7Rat := by
  rw [p7_equalCell_fourteen_exact]
  norm_num

lemma p7_equalCell_twelve_ne_zero : equalCellCoeff 12 p7Rat ≠ 0 := by
  rw [p7_equalCell_twelve_exact]
  norm_num

lemma p7_equalCell_fourteen_ne_zero : equalCellCoeff 14 p7Rat ≠ 0 := by
  rw [p7_equalCell_fourteen_exact]
  norm_num


def q7Polynomial : Polynomial ℚ :=
  (p7a1 / p7N) • Polynomial.X + (p7a3 / p7N) • Polynomial.X^3 +
  (p7a5 / p7N) • Polynomial.X^5 + (p7a7 / p7N) • Polynomial.X^7

lemma q7Polynomial_eval (u : ℚ) : q7Polynomial.eval u = q7Rat u := by
  simp [q7Polynomial, q7Rat]
  ring

lemma q7Polynomial_odd : q7Polynomial.comp (-Polynomial.X) = -q7Polynomial := by
  apply Polynomial.funext
  intro u
  simp [q7Polynomial]
  ring

lemma q7Polynomial_natDegree_le : q7Polynomial.natDegree ≤ 7 := by
  unfold q7Polynomial
  apply Nat.le_trans (Polynomial.natDegree_add_le _ _)
  apply max_le
  · apply Nat.le_trans (Polynomial.natDegree_add_le _ _)
    apply max_le
    · apply Nat.le_trans (Polynomial.natDegree_add_le _ _)
      apply max_le
      · exact Nat.le_trans (Polynomial.natDegree_smul_le _ _) (by simp)
      · exact Nat.le_trans (Polynomial.natDegree_smul_le _ _) (by simp)
    · exact Nat.le_trans (Polynomial.natDegree_smul_le _ _) (by simp)
  · exact Nat.le_trans (Polynomial.natDegree_smul_le _ _) (by simp)

end

end HalfSieve
