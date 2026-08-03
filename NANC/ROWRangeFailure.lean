import NANC.ExponentLedger

namespace NANC

/-- The bad ROW range exceeds its admissible exponent by at least `7/18`. -/
theorem row_bad_excess_at_least_seven_eighteenths (a b : ℚ)
    (ha : (5 / 18 : ℚ) ≤ a) (hab : a ≤ b) :
    (7 / 18 : ℚ) ≤ 2 * a + 3 * b - 1 := by
  exact row_range_deficit_exponent_highP3 a b ha hab

end NANC
