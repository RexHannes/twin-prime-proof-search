import Mathlib
import RequestProject.NANC.Gate1BDet2.PrimitiveDet2PairSurface

/-!
# Gate 1B / determinant-2 bank, Module 27: the unipotent matrix geometry

The common shift of the pair surface is right multiplication by a lower
unipotent matrix.  With

  `M = !![z, u; v, ℓ]`,  `N_h = !![1, 0; h, 1]`,

one has `det M = z ℓ − u v`, `det N_h = 1`, and

  `M N_h = !![z + u h, u; v + ℓ h, ℓ]`,

hence `det (M N_h) = det M`; in particular the determinant-2 shell is preserved.

This is exactly the matrix form of the translation stability already banked in
`Det2AffineLines` / `PrimitiveDet2PairSurface`; the point of this module is to
record the `2 × 2` group-theoretic statement itself.
-/

namespace TwinPrimeProject
namespace Gate1BDet2

open Matrix

/-- The pair matrix `!![z, u; v, ℓ]`. -/
def pairMatrix (z u v l : ℤ) : Matrix (Fin 2) (Fin 2) ℤ := !![z, u; v, l]

/-- The lower unipotent matrix `!![1, 0; h, 1]`. -/
def unipotent (h : ℤ) : Matrix (Fin 2) (Fin 2) ℤ := !![1, 0; h, 1]

/-- `det !![z, u; v, ℓ] = z ℓ − u v`. -/
theorem det_pairMatrix (z u v l : ℤ) : (pairMatrix z u v l).det = z * l - u * v := by
  simp [pairMatrix, Matrix.det_fin_two_of]

/-- `det !![1, 0; h, 1] = 1`. -/
theorem det_unipotent (h : ℤ) : (unipotent h).det = 1 := by
  simp [unipotent, Matrix.det_fin_two_of]

/-- **`det2_right_unipotent_action`.**  Right multiplication by `N_h` shifts the
first column by `h` times the second:
`!![z, u; v, ℓ] * !![1, 0; h, 1] = !![z + u h, u; v + ℓ h, ℓ]`. -/
theorem det2_right_unipotent_action (z u v l h : ℤ) :
    pairMatrix z u v l * unipotent h = pairMatrix (z + u * h) u (v + l * h) l := by
  simp only [pairMatrix, unipotent]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- **`det2_preserved_by_right_unipotent`.**  The determinant is unchanged by the
right unipotent action. -/
theorem det2_preserved_by_right_unipotent (z u v l h : ℤ) :
    (pairMatrix z u v l * unipotent h).det = (pairMatrix z u v l).det := by
  rw [Matrix.det_mul, det_unipotent, mul_one]

/-- In particular the determinant-2 shell is preserved: `det M = 2` implies
`det (M N_h) = 2`. -/
theorem det_eq_two_preserved {z u v l : ℤ} (h : ℤ) (hdet : (pairMatrix z u v l).det = 2) :
    (pairMatrix z u v l * unipotent h).det = 2 := by
  rw [det2_preserved_by_right_unipotent, hdet]

/-- The matrix statement in the coordinates of the pair surface: the shifted
entries again satisfy `ℓ z' − u v' = ℓ z − u v`. -/
theorem det_shifted_entries (z u v l h : ℤ) :
    (pairMatrix (z + u * h) u (v + l * h) l).det = (pairMatrix z u v l).det := by
  rw [← det2_right_unipotent_action, det2_preserved_by_right_unipotent]

/-- Compatibility with the determinant-2 line predicate of Module 4: `det` of the
pair matrix is `2` exactly when `(v, z)` lies on the shell (note the orientation
`det !![z,u;v,ℓ] = z ℓ − u v = ℓ z − u v`). -/
theorem onDet2Line_iff_det_pairMatrix (u l v z : ℤ) :
    OnDet2Line u l v z ↔ (pairMatrix z u v l).det = 2 := by
  rw [det_pairMatrix]
  unfold OnDet2Line
  constructor <;> intro h <;> linarith

end Gate1BDet2
end TwinPrimeProject
