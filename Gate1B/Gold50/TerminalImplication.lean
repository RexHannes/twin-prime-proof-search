import Mathlib

namespace Gate1B.Gold50

/-- Terminal remainder from the Gold 5.0 brief. -/
def Remainder (Q3 c3 Npsi Mh : ℝ) : ℝ :=
  2 * (Q3 - c3 * Npsi) + Mh

/-- Conditional positivity implication: a one-sided bound on `R_h` forces `J_X > 0`. -/
theorem j_pos_of_remainder_lt
    {JX cstar eps Npsi Rh : ℝ}
    (hMain : JX ≥ (cstar - eps) * Npsi - Rh)
    (hRh : Rh < (cstar - eps) * Npsi) :
    0 < JX := by
  have hLower : 0 < (cstar - eps) * Npsi - Rh := by linarith
  exact lt_of_lt_of_le hLower hMain

/-- Non-strict variant used when only weak remainder control is available. -/
theorem j_nonneg_of_remainder_le
    {JX cstar eps Npsi Rh : ℝ}
    (hMain : JX ≥ (cstar - eps) * Npsi - Rh)
    (hRh : Rh ≤ (cstar - eps) * Npsi) :
    0 ≤ JX := by
  have hLower : 0 ≤ (cstar - eps) * Npsi - Rh := by linarith
  exact le_trans hLower hMain

end Gate1B.Gold50
