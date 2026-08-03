import Mathlib

namespace NANC

/-- Exponent form of `H ≤ L²`: cancellation leaves precisely `a ≤ 2/3`. -/
theorem row_range_H_le_L2_iff (a b : ℚ) :
    a + 2 * b - (2 / 3 : ℚ) ≤ 2 * b ↔ a ≤ (2 / 3 : ℚ) := by
  constructor <;> intro h <;> linarith

/-- Exponent form of `HL ≤ M/R`. -/
theorem row_range_HL_le_MdivR_iff (a b : ℚ) :
    (a + 2 * b - (2 / 3 : ℚ)) + b ≤ (1 / 3 : ℚ) - a ↔ 2 * a + 3 * b ≤ 1 := by
  constructor <;> intro h <;> linarith

 theorem highP3_second_condition_lower_bound (a b : ℚ)
    (ha : (5 / 18 : ℚ) ≤ a) (hab : a ≤ b) : (25 / 18 : ℚ) ≤ 2 * a + 3 * b := by linarith

 theorem row_range_second_condition_fails_highP3 (a b : ℚ)
    (ha : (5 / 18 : ℚ) ≤ a) (hab : a ≤ b) : ¬ (2 * a + 3 * b ≤ 1) := by linarith

 theorem row_range_deficit_exponent_highP3 (a b : ℚ)
    (ha : (5 / 18 : ℚ) ≤ a) (hab : a ≤ b) : (7 / 18 : ℚ) ≤ 2 * a + 3 * b - 1 := by
  linarith

 theorem row_range_vertex_deficit :
    2 * (5 / 18 : ℚ) + 3 * (25 / 72 : ℚ) - 1 = 43 / 72 := by norm_num

end NANC
