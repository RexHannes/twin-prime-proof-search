/-
# Gate 1B v13 — same-`q` discrepancy capacity arithmetic

**Status: CAPACITY_ONLY.  Rational/real exponent bookkeeping, nothing analytic.**

Assume *abstractly* (these are bookkeeping assumptions, not proved facts):

* the discrepancy exponent is `q^{1/2}`;
* `H = K = Q/Y`;
* `q ≍ Q`.

Then the relative exponent is

    q^{3/2} / (H K) = Y² / Q^{1/2},

proved as `discrepancy_relative_exponent`.  Substituting `Q = X^ω`,
`Y = X^{1/9}` gives `X^{2/9 − ω/2}` (`relative_exponent_in_X`), and for
`ω ≥ 13/18` we get the capacity margin

    2/9 − ω/2 ≤ −5/36.

**This is CAPACITY_ONLY.**  Nothing here concludes an analytic theorem: the
modular-hyperbola discrepancy input is not supplied by this bank.
-/
import Mathlib

namespace Gate1B.SafeAlgebra

/-- **Relative exponent identity**: `q^{3/2}/(HK) = Y²/Q^{1/2}` with
`H = K = Q/Y` and `q ≍ Q`. -/
theorem discrepancy_relative_exponent {Q Y : ℝ} (hQ : 0 < Q) (hY : 0 < Y) :
    Q ^ ((3 : ℝ) / 2) / ((Q / Y) * (Q / Y)) = Y ^ 2 / Q ^ ((1 : ℝ) / 2) := by
  have hhalf : (0 : ℝ) < Q ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos hQ _
  have hsq : Q ^ ((3 : ℝ) / 2) * Q ^ ((1 : ℝ) / 2) = Q ^ 2 := by
    rw [← Real.rpow_add hQ]
    norm_num
  field_simp
  nlinarith [hsq, hQ.le, hY.le, sq_nonneg Y, sq_nonneg Q]

/-- **Relative exponent in `X`**: with `Q = X^ω` and `Y = X^{1/9}`,
`Y²/Q^{1/2} = X^{2/9 − ω/2}`. -/
theorem relative_exponent_in_X {X omega : ℝ} (hX : 0 < X) :
    (X ^ ((1 : ℝ) / 9)) ^ 2 / (X ^ omega) ^ ((1 : ℝ) / 2)
      = X ^ ((2 : ℝ) / 9 - omega / 2) := by
  have h1 : (X ^ ((1 : ℝ) / 9)) ^ 2 = X ^ ((2 : ℝ) / 9) := by
    rw [show ((X ^ ((1 : ℝ) / 9)) ^ 2) = (X ^ ((1 : ℝ) / 9)) ^ ((2 : ℕ) : ℝ) by
      rw [Real.rpow_natCast]]
    rw [← Real.rpow_mul hX.le]
    norm_num
  have h2 : (X ^ omega) ^ ((1 : ℝ) / 2) = X ^ (omega / 2) := by
    rw [← Real.rpow_mul hX.le]
    ring_nf
  rw [h1, h2, ← Real.rpow_sub hX]

/-- **Capacity margin.**  For `ω ≥ 13/18` the relative exponent is at most
`−5/36`. -/
theorem sameQ_capacity_margin {omega : ℝ} (h : (13 : ℝ) / 18 ≤ omega) :
    (2 : ℝ) / 9 - omega / 2 ≤ -(5 : ℝ) / 36 := by
  linarith

/-- The margin is strictly negative, i.e. it is a genuine power saving in the
capacity bookkeeping. -/
theorem sameQ_capacity_margin_neg : -(5 : ℝ) / 36 < 0 := by norm_num

end Gate1B.SafeAlgebra
