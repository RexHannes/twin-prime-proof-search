/-
# Gate 1B v8.5 — short-short exponent closure (capacity bookkeeping)

**Status: CAPACITY_ONLY (exact rational exponent arithmetic).**

All exponents are taken in the `Y`-scale, `Y = X^(1/9)`.  Write `pe` for the
exponent of `P`, so `P = Y^pe`.

Short-short input:  `P ≤ Y⁴`, i.e. `pe ≤ 4`;
capacity input:     `P > V > Y²`, i.e. `pe > 2` (so `P² ≥ Y` with large slack).

Then

    (1/P) · sqrt((P² + Y) · Y) · sqrt((P² + Y⁸) · Y⁸)
      ≍ (1/P) · sqrt(P² · Y) · sqrt(Y⁸ · Y⁸)
      = Y^(1/2) · Y^8 = Y^(17/2),

against the target scale `Y⁹`.  The margin is

    17/2 − 9 = −1/2,        Y^(−1/2) = X^(−1/18).

This is exponent bookkeeping, **not** an analytic theorem: see
`H7ScopeCountermodels.countermodelD_capacity_is_not_analytic`.
-/
import Mathlib
import Gate1B.SafeAlgebra.H7ShortShortScope

namespace Gate1B.SafeAlgebra

/-- `P ≤ Y⁴` in exponent form. -/
def ShortShortPrimeExponent (pe : ℚ) : Prop := 2 < pe ∧ pe ≤ 4

/-- `P ≤ Y⁴ ⟹ P² ≤ Y⁸`. -/
theorem h7_P2_le_Y8 {pe : ℚ} (h : pe ≤ 4) : 2 * pe ≤ 8 := by linarith

/-- `P > Y² ⟹ P² ≥ Y`, with slack `2·pe − 1 > 3`. -/
theorem h7_P2_ge_Y {pe : ℚ} (h : 2 < pe) : 1 ≤ 2 * pe ∧ 3 < 2 * pe - 1 := by
  constructor <;> linarith

/-- The capacity exponent of the compiler output in the `Y`-scale:

    −pe + (2·pe + 1)/2 + (8 + 8)/2. -/
def h7CapacityExponent (pe : ℚ) : ℚ := -pe + (2 * pe + 1) / 2 + (8 + 8) / 2

/-- **The capacity output is `Y^(17/2)`, uniformly in `pe`.** -/
theorem h7Capacity_eq (pe : ℚ) : h7CapacityExponent pe = 17 / 2 := by
  unfold h7CapacityExponent; ring

/-- The target scale exponent. -/
def h7TargetExponent : ℚ := 9

/-- **The margin in the `Y`-scale is `−1/2`.** -/
theorem h7ShortShort_margin_Y (pe : ℚ) :
    h7CapacityExponent pe - h7TargetExponent = -(1 / 2) := by
  rw [h7Capacity_eq]; unfold h7TargetExponent; norm_num

/-- **The margin in the `X`-scale is `−1/18`** (`Y = X^(1/9)`). -/
theorem h7ShortShort_margin_X (pe : ℚ) :
    yExponent * (h7CapacityExponent pe - h7TargetExponent) = -(1 / 18) := by
  rw [h7ShortShort_margin_Y]; unfold yExponent; norm_num

/-- The margin is strictly negative: a genuine power saving at the exponent
level (capacity only). -/
theorem h7ShortShort_margin_neg (pe : ℚ) :
    h7CapacityExponent pe - h7TargetExponent < 0 := by
  rw [h7ShortShort_margin_Y]; norm_num

/-- Consistency with the scope lock: in a short-short scope the exponent of `P`
in the `Y`-scale is `< 4`, so `ShortShortPrimeExponent` is the right window
whenever the lower capacity constraint `pe > 2` holds. -/
theorem h7_scope_gives_pe_lt_four (S : H7ShortShortScope) : S.beta / yExponent < 4 :=
  S.h7_P_lt_Y4_capacity

end Gate1B.SafeAlgebra
