/-
# Gate 1B v12 — Möbius four-cycle: exact trace, determinant and discriminant

**Status: PROVED_ALGEBRAIC (symbolic 2×2 matrix algebra over a commutative ring).**

The four-step recurrence `z_{j+1} = h_j - a_{j-1} / z_j` is carried by the
matrices

    M1 = [[h1, -a4], [1, 0]]
    M2 = [[h2, -a1], [1, 0]]
    M3 = [[h3, -a2], [1, 0]]
    M4 = [[h4, -a3], [1, 0]]

and the four-cycle by `M = M1 * M4 * M3 * M2` (the order dictated by the
recurrence).  We prove by ring normalisation the exact trace, the exact
determinant, the fixed-point quadratic discriminant identity, and the
fixed-multiplier (`a_i = 1`) regression specialisation.

Nothing analytic occurs here: no character sum, no estimate.

Contents:

* `cycleMatrix` — the ordered product `M1 * M4 * M3 * M2`;
* `fourCycle_trace`, `fourCycle_det`;
* `fourCycleDisc`, `fixedPoint_quadratic_disc` (generic 2×2 identity);
* `fourCycle_disc_eq`;
* `fourCycle_trace_fixed_multiplier`, `fourCycle_disc_fixed_multiplier`.
-/
import Mathlib

namespace Gate1B.SafeAlgebra

open Matrix

variable {R : Type*} [CommRing R]

/-- The `j`-th step matrix of the recurrence `z ↦ h - a/z`. -/
def stepMatrix (h a : R) : Matrix (Fin 2) (Fin 2) R := !![h, -a; 1, 0]

/-- The ordered four-cycle matrix `M = M1 * M4 * M3 * M2`. -/
def cycleMatrix (a1 a2 a3 a4 h1 h2 h3 h4 : R) : Matrix (Fin 2) (Fin 2) R :=
  stepMatrix h1 a4 * stepMatrix h4 a3 * stepMatrix h3 a2 * stepMatrix h2 a1

/-- **Exact four-cycle trace.** -/
theorem fourCycle_trace (a1 a2 a3 a4 h1 h2 h3 h4 : R) :
    Matrix.trace (cycleMatrix a1 a2 a3 a4 h1 h2 h3 h4)
      = a1 * a3 - a1 * h3 * h4 + a2 * a4 - a2 * h1 * h4
        - a3 * h1 * h2 - a4 * h2 * h3 + h1 * h2 * h3 * h4 := by
  simp [cycleMatrix, stepMatrix, Matrix.trace_fin_two]
  ring

/-- **Exact four-cycle determinant.** -/
theorem fourCycle_det (a1 a2 a3 a4 h1 h2 h3 h4 : R) :
    Matrix.det (cycleMatrix a1 a2 a3 a4 h1 h2 h3 h4) = a1 * a2 * a3 * a4 := by
  simp [cycleMatrix, stepMatrix, Matrix.det_fin_two]
  ring

/-- The four-cycle discriminant `tr² − 4 det`. -/
def fourCycleDisc (a1 a2 a3 a4 h1 h2 h3 h4 : R) : R :=
  Matrix.trace (cycleMatrix a1 a2 a3 a4 h1 h2 h3 h4) ^ 2
    - 4 * Matrix.det (cycleMatrix a1 a2 a3 a4 h1 h2 h3 h4)

/-- **Fixed-point quadratic discriminant identity.**  For `M = [[A,B],[C,D]]` the
fixed-point equation of `z ↦ (Az+B)/(Cz+D)` is `C z² + (D−A) z − B = 0`, whose
discriminant `(D−A)² + 4BC` equals `tr(M)² − 4 det(M)`. -/
theorem fixedPoint_quadratic_disc (M : Matrix (Fin 2) (Fin 2) R) :
    (M 1 1 - M 0 0) ^ 2 + 4 * (M 0 1 * M 1 0)
      = Matrix.trace M ^ 2 - 4 * Matrix.det M := by
  simp [Matrix.trace_fin_two, Matrix.det_fin_two]
  ring

/-- **Exact four-cycle discriminant.** -/
theorem fourCycle_disc_eq (a1 a2 a3 a4 h1 h2 h3 h4 : R) :
    fourCycleDisc a1 a2 a3 a4 h1 h2 h3 h4
      = (a1 * a3 - a1 * h3 * h4 + a2 * a4 - a2 * h1 * h4
          - a3 * h1 * h2 - a4 * h2 * h3 + h1 * h2 * h3 * h4) ^ 2
        - 4 * (a1 * a2 * a3 * a4) := by
  unfold fourCycleDisc
  rw [fourCycle_trace, fourCycle_det]

/-- **Fixed-multiplier regression (trace).**  With `a1 = a2 = a3 = a4 = 1` the
trace collapses to the published fixed-`a` four-cycle polynomial. -/
theorem fourCycle_trace_fixed_multiplier (h1 h2 h3 h4 : R) :
    Matrix.trace (cycleMatrix (1 : R) 1 1 1 h1 h2 h3 h4)
      = h1 * h2 * h3 * h4 - (h1 + h3) * (h2 + h4) + 2 := by
  rw [fourCycle_trace]
  ring

/-- **Fixed-multiplier regression (discriminant).** -/
theorem fourCycle_disc_fixed_multiplier (h1 h2 h3 h4 : R) :
    fourCycleDisc (1 : R) 1 1 1 h1 h2 h3 h4
      = (h1 * h2 * h3 * h4 - (h1 + h3) * (h2 + h4) + 2) ^ 2 - 4 := by
  unfold fourCycleDisc
  rw [fourCycle_trace_fixed_multiplier, fourCycle_det]
  ring

/-- **Counterguard A (fixed ≠ moving multiplier).**  The four-cycle trace is not
a function of `(h1,h2,h3,h4)` alone: two multiplier tuples with the same `h`'s
give different traces.  Hence a fixed-multiplier four-cycle statement does not
cover the moving-multiplier family. -/
theorem fourCycle_trace_depends_on_multipliers :
    Matrix.trace (cycleMatrix (1 : ℚ) 1 1 1 0 0 0 0)
      ≠ Matrix.trace (cycleMatrix (2 : ℚ) 1 1 1 0 0 0 0) := by
  rw [fourCycle_trace, fourCycle_trace]
  norm_num

end Gate1B.SafeAlgebra
