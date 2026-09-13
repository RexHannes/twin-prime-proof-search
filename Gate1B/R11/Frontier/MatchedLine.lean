/-
# Gate1B / R11 / Frontier : matched-line two-copy algebra

This module is **pure exact algebra**: there is no analytic statement anywhere in it.

It reuses the affine parametrisation already banked in `Gate1B.R11.AffineParametrization`
(`B = B₀ + k t`, `d = d₀ + A t` are exactly the solutions of `A·B + 2 = k·d`) and records the
*two-copy* consequences at line parameters `t` and `t + h`:

```
d_{t+h} = d_t + A h,      B_{t+h} = B_t + k h,
d_t B_{t+h} − d_{t+h} B_t = 2 h.
```

The same content is banked in matrix form.  With the column vectors
`v_t = (d_t, B_t)ᵀ` and `u = (A, k)ᵀ`,

```
v_{t+h} = v_t + h u,
N_t = [v_t, u],      M_{t,h} = [v_t, v_{t+h}],
det N_t = 2,         M_{t,h} = N_t · [[1,1],[0,h]],      det M_{t,h} = 2 h.
```

Sign convention: the source determinant is `A·B − k·d = −2` (equivalently `A·B + 2 = k·d`
on naturals, as in `Gate1B.R11.Determinant`), so `det N_t = d_t k − A B_t = +2`.
-/
import Mathlib
import Gate1B.R11.AffineParametrization

namespace Gate1B.R11.Frontier

open Matrix

/-! ## 1. The two lines -/

/-- The `d`-line `d_t = d₀ + A t`. -/
def dLine (d0 A t : ℤ) : ℤ := d0 + A * t

/-- The `B`-line `B_t = B₀ + k t`. -/
def BLine (B0 k t : ℤ) : ℤ := B0 + k * t

/-- Shift law for the `d`-line: `d_{t+h} = d_t + A h`. -/
theorem dLine_shift (d0 A t h : ℤ) : dLine d0 A (t + h) = dLine d0 A t + A * h := by
  unfold dLine; ring

/-- Shift law for the `B`-line: `B_{t+h} = B_t + k h`. -/
theorem BLine_shift (B0 k t h : ℤ) : BLine B0 k (t + h) = BLine B0 k t + k * h := by
  unfold BLine; ring

/-- The determinant `A·B_t − k·d_t = −2` is preserved along the whole line. -/
theorem matched_det_line {A k d0 B0 : ℤ} (h0 : A * B0 - k * d0 = -2) (t : ℤ) :
    A * BLine B0 k t - k * dLine d0 A t = -2 := by
  unfold dLine BLine
  linear_combination h0

/-! ## 2. The two-copy determinant `2h` -/

/-- **TWO-COPY DETERMINANT.**  For two copies of the matched line at parameters `t` and
`t + h`, `d_t B_{t+h} − d_{t+h} B_t = 2 h`. -/
theorem twoCopy_det {A k d0 B0 : ℤ} (h0 : A * B0 - k * d0 = -2) (t h : ℤ) :
    dLine d0 A t * BLine B0 k (t + h) - dLine d0 A (t + h) * BLine B0 k t = 2 * h := by
  unfold dLine BLine
  linear_combination (-h) * h0

/-! ## 3. Matrix formulation -/

/-- The column vector `v_t = (d_t, B_t)ᵀ`, as a `2 × 1` matrix. -/
def vVec (d0 A B0 k t : ℤ) : Matrix (Fin 2) (Fin 1) ℤ :=
  !![dLine d0 A t; BLine B0 k t]

/-- The direction vector `u = (A, k)ᵀ`. -/
def uVec (A k : ℤ) : Matrix (Fin 2) (Fin 1) ℤ := !![A; k]

/-- `v_{t+h} = v_t + h · u`. -/
theorem vVec_shift (d0 A B0 k t h : ℤ) :
    vVec d0 A B0 k (t + h) = vVec d0 A B0 k t + h • uVec A k := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [vVec, uVec, dLine, BLine] <;> ring

/-- `N_t = [v_t, u]`, the `2 × 2` matrix with columns `v_t` and `u`. -/
def Nmat (d0 A B0 k t : ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![dLine d0 A t, A; BLine B0 k t, k]

/-- `M_{t,h} = [v_t, v_{t+h}]`, the `2 × 2` matrix with columns `v_t` and `v_{t+h}`. -/
def Mmat (d0 A B0 k t h : ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![dLine d0 A t, dLine d0 A (t + h); BLine B0 k t, BLine B0 k (t + h)]

/-- The columns of `Nmat` really are `v_t` and `u`. -/
theorem Nmat_col (d0 A B0 k t : ℤ) (i : Fin 2) :
    Nmat d0 A B0 k t i 0 = vVec d0 A B0 k t i 0 ∧ Nmat d0 A B0 k t i 1 = uVec A k i 0 := by
  fin_cases i <;> exact ⟨rfl, rfl⟩

/-- The columns of `Mmat` really are `v_t` and `v_{t+h}`. -/
theorem Mmat_col (d0 A B0 k t h : ℤ) (i : Fin 2) :
    Mmat d0 A B0 k t h i 0 = vVec d0 A B0 k t i 0 ∧
      Mmat d0 A B0 k t h i 1 = vVec d0 A B0 k (t + h) i 0 := by
  fin_cases i <;> exact ⟨rfl, rfl⟩

/-- **`det N_t = 2`.** -/
theorem det_Nmat {A k d0 B0 : ℤ} (h0 : A * B0 - k * d0 = -2) (t : ℤ) :
    (Nmat d0 A B0 k t).det = 2 := by
  rw [Nmat, det_fin_two_of]
  unfold dLine BLine
  linear_combination -h0

/-- **Hecke matrix factorisation** `M_{t,h} = N_t · [[1,1],[0,h]]`. -/
theorem Mmat_factorisation (d0 A B0 k t h : ℤ) :
    Mmat d0 A B0 k t h = Nmat d0 A B0 k t * !![1, 1; 0, h] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Mmat, Nmat, Matrix.mul_apply, Fin.sum_univ_succ, dLine, BLine] <;> ring

/-- **`det M_{t,h} = 2 h`**, both directly and through the factorisation. -/
theorem det_Mmat {A k d0 B0 : ℤ} (h0 : A * B0 - k * d0 = -2) (t h : ℤ) :
    (Mmat d0 A B0 k t h).det = 2 * h := by
  rw [Mmat, det_fin_two_of]
  exact twoCopy_det h0 t h

/-- The factorisation reproduces the determinant: `det M = det N · h = 2h`. -/
theorem det_Mmat_via_factorisation {A k d0 B0 : ℤ} (h0 : A * B0 - k * d0 = -2) (t h : ℤ) :
    (Mmat d0 A B0 k t h).det = (Nmat d0 A B0 k t).det * h := by
  rw [Mmat_factorisation, det_mul, det_fin_two_of, det_Nmat h0]
  ring

end Gate1B.R11.Frontier
