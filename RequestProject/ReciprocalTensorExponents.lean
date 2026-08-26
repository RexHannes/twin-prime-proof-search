import Mathlib

/-! Exact exponent arithmetic for the naively Cauchy-bounded reciprocal tensor. -/

namespace ShiftedMobiusBank

/-- Under the external moment bounds, normalization contributes `R⁻¹`, the
`A`-moment contributes `R³`, and the square root of the `C`-moment contributes
`R^(5/2)`. Their exponent is exactly `9/2`. -/
theorem NAIVE_RECIPROCAL_TENSOR_EXPONENT :
    (-1 : ℚ) + 3 + 5 / 2 = 9 / 2 := by norm_num

/-- The naive exponent exceeds the desired cubic scale by exactly `3/2`. -/
theorem RECIPROCAL_TENSOR_GAP_THREE_HALVES :
    (9 / 2 : ℚ) - 3 = 3 / 2 := by norm_num

end ShiftedMobiusBank
