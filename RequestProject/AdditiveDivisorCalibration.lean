import Mathlib

/-!
# Additive-divisor conductor-surplus calibration (§17)

Suppose an additive-divisor theorem gives power saving uniformly when the
conductor is at most `(size)^{2/3+κ}`.  In the current calibration the conductor
exponent is `2μ+2/3` and the size exponent is `μ+1`.

* `ADDITIVE_DIVISOR_SURPLUS_EXACT_CONDITION`: the exact equivalence.
* `ADDITIVE_DIVISOR_SURPLUS_SIMPLE_SUFFICIENT_CONDITION`: the merely sufficient
  shortcut, explicitly marked as sufficient (not equivalent).

Status: `LEAN_PROVED_CORE` (the analytic additive-divisor theorem is
`OPEN_INPUT`).
-/

namespace Banking.AdditiveDivisor

/-- `ADDITIVE_DIVISOR_SURPLUS_EXACT_CONDITION` (§17).

`2μ + 2/3 ≤ (2/3 + κ)(μ+1) ↔ 4μ/3 ≤ κ(μ+1)`. -/
theorem surplus_exact_condition (μ κ : ℝ) :
    (2 * μ + 2 / 3 ≤ (2 / 3 + κ) * (μ + 1)) ↔ (4 * μ / 3 ≤ κ * (μ + 1)) := by
  constructor <;> intro h <;> nlinarith [h]

/-- `ADDITIVE_DIVISOR_SURPLUS_SIMPLE_SUFFICIENT_CONDITION` (§17).

The shortcut `μ ≤ 3κ/4` is *sufficient* (not equivalent) for the exact
condition, when `μ ≥ 0`.  Indeed `4μ/3 ≤ κ ≤ κ(μ+1)` for `μ ≥ 0`. -/
theorem surplus_simple_sufficient (μ κ : ℝ) (hμ : 0 ≤ μ) (hκ : 0 ≤ κ)
    (h : μ ≤ 3 * κ / 4) :
    4 * μ / 3 ≤ κ * (μ + 1) := by
  have h1 : 4 * μ / 3 ≤ κ := by linarith
  nlinarith [mul_nonneg hκ hμ]

/-- The shortcut is genuinely *not* equivalent: there is a witness satisfying the
exact condition but violating the shortcut.  (Take `μ = 3/4`, `κ = 1/2`:
`4μ/3 = 1 ≤ κ(μ+1) = 7/8`? no — pick instead `μ = 1, κ = 1`: exact holds since
`4/3 ≤ 2`, shortcut `1 ≤ 3/4` fails.) -/
theorem surplus_shortcut_not_necessary :
    ∃ μ κ : ℝ, (4 * μ / 3 ≤ κ * (μ + 1)) ∧ ¬ (μ ≤ 3 * κ / 4) := by
  refine ⟨1, 1, by norm_num, by norm_num⟩

end Banking.AdditiveDivisor
