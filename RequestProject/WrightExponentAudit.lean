import Mathlib

/-!
# Wright five-term exponent inequalities (§12.4)

The IIIb Wright sector produces a small collection of exponent inequalities in the
two ratio-variables `a = T/s_-` and `b = T/s_+` (after normalisation `1 ≤ a ≤ b`).
This module machine-checks the two governing real-power inequalities, together
with the underlying cleared-denominator integer-power statements the master task
asked for.
-/

namespace ShiftedMobiusBank

open Real

/-- Cleared-denominator core inequality `a³ ≤ b³` (underlying the `3/16`
exponent gap). -/
theorem wright_cube_mono {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) : a ^ 3 ≤ b ^ 3 := by
  have h0 : (0:ℝ) ≤ a := by linarith
  gcongr

/-- Cleared-denominator core inequality `a⁷ ≤ b⁷` (underlying the `7/40`
exponent gap). -/
theorem wright_seventh_mono {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) : a ^ 7 ≤ b ^ 7 := by
  have h0 : (0:ℝ) ≤ a := by linarith
  gcongr

/-- §12.4, first Wright term:
`a^(1/2) · b^(1/8) ≤ (a·b)^(5/16)` for `1 ≤ a ≤ b`. -/
theorem wright_term_one {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    a ^ ((1:ℝ)/2) * b ^ ((1:ℝ)/8) ≤ (a * b) ^ ((5:ℝ)/16) := by
  have ha0 : (0:ℝ) < a := by linarith
  have hb0 : (0:ℝ) < b := by linarith
  rw [Real.mul_rpow (le_of_lt ha0) (le_of_lt hb0)]
  have key : a ^ ((3:ℝ)/16) ≤ b ^ ((3:ℝ)/16) :=
    Real.rpow_le_rpow (le_of_lt ha0) hab (by norm_num)
  have ea : a ^ ((5:ℝ)/16) * a ^ ((3:ℝ)/16) = a ^ ((1:ℝ)/2) := by
    rw [← Real.rpow_add ha0]; norm_num
  have eb : b ^ ((1:ℝ)/8) * b ^ ((3:ℝ)/16) = b ^ ((5:ℝ)/16) := by
    rw [← Real.rpow_add hb0]; norm_num
  have pa : (0:ℝ) ≤ a ^ ((5:ℝ)/16) := le_of_lt (Real.rpow_pos_of_pos ha0 _)
  have pb : (0:ℝ) ≤ b ^ ((1:ℝ)/8) := le_of_lt (Real.rpow_pos_of_pos hb0 _)
  calc a ^ ((1:ℝ)/2) * b ^ ((1:ℝ)/8)
      = a ^ ((5:ℝ)/16) * a ^ ((3:ℝ)/16) * b ^ ((1:ℝ)/8) := by rw [ea]
    _ ≤ a ^ ((5:ℝ)/16) * b ^ ((3:ℝ)/16) * b ^ ((1:ℝ)/8) := by
          apply mul_le_mul_of_nonneg_right _ pb
          exact mul_le_mul_of_nonneg_left key pa
    _ = a ^ ((5:ℝ)/16) * (b ^ ((1:ℝ)/8) * b ^ ((3:ℝ)/16)) := by ring
    _ = a ^ ((5:ℝ)/16) * b ^ ((5:ℝ)/16) := by rw [eb]

/-- §12.4, second Wright term:
`a^(1/5) · b^(-3/20) ≤ (a·b)^(1/40)` for `1 ≤ a ≤ b`. -/
theorem wright_term_two {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    a ^ ((1:ℝ)/5) * b ^ (-(3:ℝ)/20) ≤ (a * b) ^ ((1:ℝ)/40) := by
  have ha0 : (0:ℝ) < a := by linarith
  have hb0 : (0:ℝ) < b := by linarith
  rw [Real.mul_rpow (le_of_lt ha0) (le_of_lt hb0)]
  have key : a ^ ((7:ℝ)/40) ≤ b ^ ((7:ℝ)/40) :=
    Real.rpow_le_rpow (le_of_lt ha0) hab (by norm_num)
  have ea : a ^ ((1:ℝ)/40) * a ^ ((7:ℝ)/40) = a ^ ((1:ℝ)/5) := by
    rw [← Real.rpow_add ha0]; norm_num
  have eb : b ^ (-(3:ℝ)/20) * b ^ ((7:ℝ)/40) = b ^ ((1:ℝ)/40) := by
    rw [← Real.rpow_add hb0]; norm_num
  have pa : (0:ℝ) ≤ a ^ ((1:ℝ)/40) := le_of_lt (Real.rpow_pos_of_pos ha0 _)
  have pb : (0:ℝ) ≤ b ^ (-(3:ℝ)/20) := le_of_lt (Real.rpow_pos_of_pos hb0 _)
  calc a ^ ((1:ℝ)/5) * b ^ (-(3:ℝ)/20)
      = a ^ ((1:ℝ)/40) * a ^ ((7:ℝ)/40) * b ^ (-(3:ℝ)/20) := by rw [ea]
    _ ≤ a ^ ((1:ℝ)/40) * b ^ ((7:ℝ)/40) * b ^ (-(3:ℝ)/20) := by
          apply mul_le_mul_of_nonneg_right _ pb
          exact mul_le_mul_of_nonneg_left key pa
    _ = a ^ ((1:ℝ)/40) * (b ^ (-(3:ℝ)/20) * b ^ ((7:ℝ)/40)) := by ring
    _ = a ^ ((1:ℝ)/40) * b ^ ((1:ℝ)/40) := by rw [eb]

/-- Bundle of the two Wright-term inequalities. -/
theorem wright_term_exponent_inequalities {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    a ^ ((1:ℝ)/2) * b ^ ((1:ℝ)/8) ≤ (a * b) ^ ((5:ℝ)/16) ∧
    a ^ ((1:ℝ)/5) * b ^ (-(3:ℝ)/20) ≤ (a * b) ^ ((1:ℝ)/40) :=
  ⟨wright_term_one ha hab, wright_term_two ha hab⟩

end ShiftedMobiusBank
