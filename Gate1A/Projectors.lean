/-
# Gate-1A (A12): centered local projectors

Let `P_s` be an orthogonal projector (Hermitian idempotent) and `P_0 ≤ P_s`
a sub-projector (`P_0 P_s = P_s P_0 = P_0`).  The **centered** projector is

`P_s° := P_s - P_0`.

We prove, in the Loewner order on complex matrices:

* `centeredProjector_isProjector` — `P_s°` is again a Hermitian idempotent;
* `centeredProjector_posSemidef` — `P_s° ⪰ 0`;
* `centeredProjector_le` — `P_s° ≤ P_s`;
* `subProjector_le` — `P_0 ≤ P_s`.

Hostile test 8 (principal / `b = 0` mode) is exactly the statement that the
*centered* projector is what appears downstream, and that it is still
positive: the `b = 0` mode is removed, not silently ignored.
-/
import Mathlib

namespace Gate1A

namespace Projectors

open Matrix
open scoped ComplexOrder

variable {n : Type*} [Fintype n]

/-- A Hermitian idempotent (orthogonal projector). -/
structure IsProjector (P : Matrix n n ℂ) : Prop where
  herm : Pᴴ = P
  idem : P * P = P

/-- Any orthogonal projector is positive semidefinite. -/
theorem IsProjector.posSemidef {P : Matrix n n ℂ} (hP : IsProjector P) :
    P.PosSemidef := by
  have h : P = Pᴴ * P := by rw [hP.herm, hP.idem]
  rw [h]
  exact posSemidef_conjTranspose_mul_self P

/-- The centered projector `P_s° = P_s - P_0`. -/
def centered (Ps P0 : Matrix n n ℂ) : Matrix n n ℂ := Ps - P0

/-- **`centeredProjector_isProjector`.** -/
theorem centered_isProjector {Ps P0 : Matrix n n ℂ}
    (hPs : IsProjector Ps) (hP0 : IsProjector P0)
    (hle1 : P0 * Ps = P0) (hle2 : Ps * P0 = P0) :
    IsProjector (centered Ps P0) where
  herm := by
    simp [centered, Matrix.conjTranspose_sub, hPs.herm, hP0.herm]
  idem := by
    simp only [centered, Matrix.sub_mul, Matrix.mul_sub, hPs.idem, hP0.idem,
      hle1, hle2]
    abel

/-- **`centeredProjector_posSemidef`.**  `P_s° ⪰ 0`. -/
theorem centered_posSemidef {Ps P0 : Matrix n n ℂ}
    (hPs : IsProjector Ps) (hP0 : IsProjector P0)
    (hle1 : P0 * Ps = P0) (hle2 : Ps * P0 = P0) :
    (centered Ps P0).PosSemidef :=
  (centered_isProjector hPs hP0 hle1 hle2).posSemidef

/-- **`subProjector_le`.**  `P_0 ≤ P_s` in the Loewner order. -/
theorem subProjector_le {Ps P0 : Matrix n n ℂ}
    (hPs : IsProjector Ps) (hP0 : IsProjector P0)
    (hle1 : P0 * Ps = P0) (hle2 : Ps * P0 = P0) :
    (Ps - P0).PosSemidef :=
  centered_posSemidef hPs hP0 hle1 hle2

/-- **`centeredProjector_le`.**  `P_s° ≤ P_s`, since `P_s - P_s° = P_0 ⪰ 0`. -/
theorem centered_le {Ps P0 : Matrix n n ℂ}
    (hP0 : IsProjector P0) :
    (Ps - centered Ps P0).PosSemidef := by
  have h : Ps - centered Ps P0 = P0 := by simp [centered]
  rw [h]
  exact hP0.posSemidef

/-- The zero mode is genuinely removed: `P_s° P_0 = 0`. -/
theorem centered_mul_sub {Ps P0 : Matrix n n ℂ}
    (hP0 : IsProjector P0) (hle2 : Ps * P0 = P0) :
    centered Ps P0 * P0 = 0 := by
  simp [centered, Matrix.sub_mul, hle2, hP0.idem]

end Projectors

end Gate1A
