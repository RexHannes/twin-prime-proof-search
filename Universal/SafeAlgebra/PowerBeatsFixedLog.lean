/-
# Universal v8.5 — a fixed power beats a fixed power of the logarithm

**Status: PROVED (eventual real-analysis comparison, derived from mathlib).**

For `eps > 0` and fixed `A, K`,

    X^(-eps) · (log X)^K ≤ (log X)^(-A)

for all sufficiently large `X`.  Nothing here is axiomatised: the statement is
derived from `isLittleO_log_rpow_rpow_atTop`.

This is the *log-target compiler*: it converts a fixed power saving (the H7
short-short capacity margin `X^(-1/18)`) into an arbitrary fixed negative power
of `log X`.  The exponent margin itself is banked separately and does not depend
on this file.
-/
import Mathlib

namespace Universal.SafeAlgebra

open Filter Asymptotics Real

/-- Eventually, `(log X)^r ≤ X^eps` for any fixed `r` and any `eps > 0`. -/
theorem log_rpow_le_rpow_eventually {r eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ x : ℝ in atTop, Real.log x ^ r ≤ x ^ eps := by
  have h : (fun x : ℝ => Real.log x ^ r) =o[atTop] fun x : ℝ => x ^ eps :=
    isLittleO_log_rpow_rpow_atTop r heps
  have hb := h.bound (by norm_num : (0:ℝ) < 1)
  filter_upwards [hb, eventually_gt_atTop (0:ℝ)] with x hx hx0
  have h2 : ‖x ^ eps‖ = x ^ eps := by
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hx0.le _)]
  calc Real.log x ^ r ≤ ‖Real.log x ^ r‖ := le_abs_self _
    _ ≤ 1 * ‖x ^ eps‖ := hx
    _ = x ^ eps := by rw [one_mul, h2]

/-- **Power beats fixed log.**  For `eps > 0` and any fixed `A, K`,

    X^(-eps) · (log X)^K ≤ (log X)^(-A)

for all sufficiently large `X` (`^` is `Real.rpow` throughout). -/
theorem power_beats_fixed_log {eps A K : ℝ} (heps : 0 < eps) :
    ∀ᶠ x : ℝ in atTop, x ^ (-eps) * Real.log x ^ K ≤ Real.log x ^ (-A) := by
  filter_upwards [log_rpow_le_rpow_eventually (r := K + A) heps,
    eventually_gt_atTop (3:ℝ)] with x hx hx3
  have hx0 : (0:ℝ) < x := by linarith
  have hlog : (0:ℝ) < Real.log x := Real.log_pos (by linarith)
  have hxe : (0:ℝ) < x ^ eps := Real.rpow_pos_of_pos hx0 _
  have hlA : (0:ℝ) < Real.log x ^ A := Real.rpow_pos_of_pos hlog _
  have key : Real.log x ^ K * Real.log x ^ A ≤ x ^ eps := by
    rw [← Real.rpow_add hlog K A]; exact hx
  rw [Real.rpow_neg hx0.le, Real.rpow_neg hlog.le]
  have hpos : (0:ℝ) < x ^ eps * Real.log x ^ A := by positivity
  refine le_of_mul_le_mul_right ?_ hpos
  have e1 : (x ^ eps)⁻¹ * Real.log x ^ K * (x ^ eps * Real.log x ^ A)
      = Real.log x ^ K * Real.log x ^ A := by
    field_simp
  have e2 : (Real.log x ^ A)⁻¹ * (x ^ eps * Real.log x ^ A) = x ^ eps := by
    field_simp
  rw [e1, e2]
  exact key

end Universal.SafeAlgebra
