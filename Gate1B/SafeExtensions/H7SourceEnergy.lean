/-
# Gate 1B v8.5 — source energy substitution

**Status: CONDITIONAL_FINITE (the source norms are explicit hypotheses).**

The compiler of `H7JointPrimeLargeSieveCompiler.lean` outputs

    ‖T‖ ≤ wBound * sqrt((P² + Y) E_D) * sqrt((P² + Y⁸) E_B).

This file performs the *substitution* of the supplied source energies

    E_D ≤ Y * L1,        E_B ≤ Y⁸ * L2

into that output, using only the capacity relations `Y ≤ P²` (i.e. `P > V > Y²`
in the short-short cell) and `P² ≤ Y⁸` (i.e. `P ≤ Y⁴`).

**No prime-density asymptotics are proved**: `L1`, `L2`, `E_D`, `E_B` are data.
-/
import Mathlib
import Gate1B.SafeExtensions.H7JointPrimeLargeSieveCompiler

namespace Gate1B.SafeExtensions

/-- Defect-side substitution: `sqrt((P² + Y) E_D) ≤ P * sqrt(2 Y L1)`. -/
theorem sqrt_defect_le {P Y E_D L1 : ℝ}
    (hP : 0 ≤ P) (hE : 0 ≤ E_D)
    (hYP : Y ≤ P ^ 2) (hED : E_D ≤ Y * L1) :
    Real.sqrt ((P ^ 2 + Y) * E_D) ≤ P * Real.sqrt (2 * Y * L1) := by
  have h1 : (P ^ 2 + Y) * E_D ≤ (2 * P ^ 2) * (Y * L1) := by
    have hPY : P ^ 2 + Y ≤ 2 * P ^ 2 := by linarith
    have h2 : (P ^ 2 + Y) * E_D ≤ (2 * P ^ 2) * E_D :=
      mul_le_mul_of_nonneg_right hPY hE
    have h3 : (2 * P ^ 2) * E_D ≤ (2 * P ^ 2) * (Y * L1) :=
      mul_le_mul_of_nonneg_left hED (by positivity)
    linarith
  calc Real.sqrt ((P ^ 2 + Y) * E_D) ≤ Real.sqrt ((2 * P ^ 2) * (Y * L1)) :=
        Real.sqrt_le_sqrt h1
    _ = P * Real.sqrt (2 * Y * L1) := by
        rw [show (2 * P ^ 2) * (Y * L1) = P ^ 2 * (2 * Y * L1) by ring,
          Real.sqrt_mul (by positivity), Real.sqrt_sq hP]

/-- Long-side substitution: `sqrt((P² + Y⁸) E_B) ≤ Y⁸ * sqrt(2 L2)`. -/
theorem sqrt_long_le {P Y E_B L2 : ℝ}
    (hE : 0 ≤ E_B)
    (hPY : P ^ 2 ≤ Y ^ 8) (hEB : E_B ≤ Y ^ 8 * L2) :
    Real.sqrt ((P ^ 2 + Y ^ 8) * E_B) ≤ Y ^ 8 * Real.sqrt (2 * L2) := by
  have h1 : (P ^ 2 + Y ^ 8) * E_B ≤ (2 * Y ^ 8) * (Y ^ 8 * L2) := by
    have hle : P ^ 2 + Y ^ 8 ≤ 2 * Y ^ 8 := by linarith
    have h2 : (P ^ 2 + Y ^ 8) * E_B ≤ (2 * Y ^ 8) * E_B :=
      mul_le_mul_of_nonneg_right hle hE
    have h3 : (2 * Y ^ 8) * E_B ≤ (2 * Y ^ 8) * (Y ^ 8 * L2) :=
      mul_le_mul_of_nonneg_left hEB (by positivity)
    linarith
  calc Real.sqrt ((P ^ 2 + Y ^ 8) * E_B) ≤ Real.sqrt ((2 * Y ^ 8) * (Y ^ 8 * L2)) :=
        Real.sqrt_le_sqrt h1
    _ = Y ^ 8 * Real.sqrt (2 * L2) := by
        rw [show (2 * Y ^ 8) * (Y ^ 8 * L2) = (Y ^ 8) ^ 2 * (2 * L2) by ring,
          Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]

/-- The product of the two substituted factors, in the normalised form: the
`P`-dependence cancels against the `1/P` weight and the output is
`2 * Y⁸ * sqrt(Y L1 L2)`, i.e. the capacity `Y^(17/2)` up to the supplied
source constants. -/
theorem substituted_product {P Y E_D E_B L1 L2 : ℝ}
    (hP : 0 < P) (hY : 0 ≤ Y) (hL1 : 0 ≤ L1)
    (hED0 : 0 ≤ E_D) (hEB0 : 0 ≤ E_B)
    (hYP : Y ≤ P ^ 2) (hPY : P ^ 2 ≤ Y ^ 8)
    (hED : E_D ≤ Y * L1) (hEB : E_B ≤ Y ^ 8 * L2) :
    (1 / P) * (Real.sqrt ((P ^ 2 + Y) * E_D) * Real.sqrt ((P ^ 2 + Y ^ 8) * E_B))
      ≤ 2 * (Y ^ 8 * Real.sqrt (Y * L1 * L2)) := by
  have h1 := sqrt_defect_le hP.le hED0 hYP hED
  have h2 := sqrt_long_le hEB0 hPY hEB
  have hprod : Real.sqrt ((P ^ 2 + Y) * E_D) * Real.sqrt ((P ^ 2 + Y ^ 8) * E_B)
      ≤ (P * Real.sqrt (2 * Y * L1)) * (Y ^ 8 * Real.sqrt (2 * L2)) :=
    mul_le_mul h1 h2 (Real.sqrt_nonneg _) (by positivity)
  have hsplit : (P * Real.sqrt (2 * Y * L1)) * (Y ^ 8 * Real.sqrt (2 * L2))
      = P * (Y ^ 8 * (2 * Real.sqrt (Y * L1 * L2))) := by
    have : Real.sqrt (2 * Y * L1) * Real.sqrt (2 * L2)
        = Real.sqrt (4 * (Y * L1 * L2)) := by
      rw [← Real.sqrt_mul (by positivity)]
      ring_nf
    rw [show (P * Real.sqrt (2 * Y * L1)) * (Y ^ 8 * Real.sqrt (2 * L2))
        = P * Y ^ 8 * (Real.sqrt (2 * Y * L1) * Real.sqrt (2 * L2)) by ring, this,
      show (4 : ℝ) * (Y * L1 * L2) = 2 ^ 2 * (Y * L1 * L2) by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
    ring
  have hfinal : (1 / P) * (Real.sqrt ((P ^ 2 + Y) * E_D) * Real.sqrt ((P ^ 2 + Y ^ 8) * E_B))
      ≤ (1 / P) * (P * (Y ^ 8 * (2 * Real.sqrt (Y * L1 * L2)))) := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [← hsplit]; exact hprod
  refine hfinal.trans_eq ?_
  field_simp

end Gate1B.SafeExtensions
