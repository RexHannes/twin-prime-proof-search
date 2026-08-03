import Mathlib

namespace NANC

/-- If each selected divisibility condition costs exponent `1/9`, then `u`
selected slots cost exactly `-u/9`. -/
theorem t0_h_divisibility_compensation_exponent (u : ℕ) :
    ∑ _i ∈ Finset.range u, (-(1 / 9 : ℚ)) = -(u : ℚ) / 9 := by
  simp
  ring

end NANC
