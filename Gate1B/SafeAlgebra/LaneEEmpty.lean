/-
# Gate 1B v8.4 — Lane-E empty support

**Status: PROVED_ALGEBRAIC (exponent part) + PROVED_FINITE (divisibility part).**

The source exponent of the lane-E cutoff is

  `V = X ^ (5/18 - η/2) = Y ^ (5/2 - (9/2) η)`,  where `Y = X ^ (1/9)`.

For `0 ≤ η < 1/9` the `Y`-exponent of `V` exceeds `2`, so in the asymptotic
regime `V > Y ^ 2`.  Since the inducing cofactor satisfies `e ≤ Y ^ 2 < V < p`
for a lane-E prime `p`, one gets `p ∤ e`, i.e. lane E is empty.

The finite half (`0 < e < p → ¬ p ∣ e`) is unconditional; the passage from the
exponent inequality to `V > Y ^ 2` is stated as a monotonicity fact about the
formula, with `Y ≥ 1` supplied.
-/
import Mathlib

namespace Gate1B.SafeAlgebra

/-! ## Exponents -/

/-- The `Y`-exponent of the lane-E cutoff `V = X ^ (5/18 - η/2)`, where
`Y = X ^ (1/9)`. -/
def laneEVExponentY (eta : ℚ) : ℚ := 5 / 2 - (9 / 2) * eta

/-- Consistency of the two forms: `9 * (5/18 - η/2) = 5/2 - (9/2) η`. -/
theorem laneEVExponent_consistent (eta : ℚ) :
    9 * (5 / 18 - eta / 2) = laneEVExponentY eta := by
  unfold laneEVExponentY; ring

/-- **Exponent of `V` exceeds `2`** for `0 ≤ η < 1/9`. -/
theorem VExponent_gt_two {eta : ℚ} (h0 : 0 ≤ eta) (h1 : eta < 1 / 9) :
    2 < laneEVExponentY eta := by
  unfold laneEVExponentY; linarith

/-- Consequently `V > Y ^ 2` in the asymptotic regime: for `Y > 1`, a quantity
of size `Y ^ (laneEVExponentY η)` strictly exceeds `Y ^ 2`. -/
theorem V_gt_Ysq {Y : ℝ} (hY : 1 < Y) {eta : ℚ} (h0 : 0 ≤ eta) (h1 : eta < 1 / 9) :
    (Y : ℝ) ^ ((2 : ℚ) : ℝ) < Y ^ ((laneEVExponentY eta : ℚ) : ℝ) := by
  refine Real.rpow_lt_rpow_of_exponent_lt hY ?_
  exact_mod_cast VExponent_gt_two h0 h1

/-! ## The finite divisibility half -/

/-- A prime larger than a positive number cannot divide it. -/
theorem laneE_prime_not_dvd_e {p e : ℕ} (he : 0 < e) (hlt : e < p) : ¬ p ∣ e := by
  intro hdvd
  exact absurd (Nat.le_of_dvd he hdvd) (not_le.mpr hlt)

/-- **Lane E is empty.**  With the chain `e ≤ Y₂ < V < p` (all natural numbers,
`e` positive), the lane-E divisibility condition `p ∣ e` fails. -/
theorem laneE_empty {p e V Ysq : ℕ} (he : 0 < e) (h1 : e ≤ Ysq) (h2 : Ysq < V)
    (h3 : V < p) : ¬ p ∣ e :=
  laneE_prime_not_dvd_e he (lt_of_le_of_lt h1 (lt_trans h2 h3))

/-- Set form: no lane-E prime divides the cofactor. -/
theorem laneE_empty_setOf {e V Ysq : ℕ} (he : 0 < e) (h1 : e ≤ Ysq) (h2 : Ysq < V) :
    {p : ℕ | V < p ∧ p ∣ e} = ∅ := by
  ext p
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
  exact fun hp => laneE_empty he h1 h2 hp

end Gate1B.SafeAlgebra
