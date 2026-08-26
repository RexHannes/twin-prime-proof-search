import RequestProject.Options
namespace TwinPrimeProject.NANC

theorem row_range_H_le_L2_iff (a b : ℚ) : a+2*b-2/3 ≤ 2*b ↔ a ≤ 2/3 := by
  constructor <;> intro h <;> linarith

theorem row_range_HL_le_MdivR_iff (a b : ℚ) :
    (a+2*b-2/3)+b ≤ 1/3-a ↔ 2*a+3*b ≤ 1 := by
  constructor <;> intro h <;> linarith

theorem row_range_second_condition_fails_highP3 (a b : ℚ)
    (ha : 5/18 ≤ a) (hb : a ≤ b) : 25/18 ≤ 2*a+3*b := by linarith

theorem row_bad_excess_at_least_seven_eighteenths (a b : ℚ)
    (ha : 5/18 ≤ a) (hb : a ≤ b) : 7/18 ≤ 2*a+3*b-1 := by linarith
end NANC
