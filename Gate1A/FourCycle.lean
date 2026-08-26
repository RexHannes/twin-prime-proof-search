/-
# Gate-1A §13: the outer four-cycle functional-analytic lemma

We formalise the four-cycle inequality in the finite-matrix layer over `ℂ`,
which the prompt explicitly allows as "sufficient as a bankable algebraic
core", and then upgrade it to a genuine operator statement (an `ℓ²`
`mulVec` bound) which does not depend on Mathlib's operator-norm instance
for matrices.

The mathematical content:

* `outer_four_cycle_trace` — the **exact identity**
  `‖∑_m T_mᴴ T_m‖_HS² = ∑_{m,m'} ‖T_m T_{m'}ᴴ‖_HS²` (an equality, not merely
  an inequality: the two traces agree by cyclicity);
* `outer_four_cycle_matrix` — the same identity written with real
  Hilbert–Schmidt norms;
* `outer_four_cycle_operator` — the consequence
  `‖A x‖² ≤ (∑_{m,m'} ‖T_m T_{m'}ᴴ‖_HS²) · ‖x‖²` for `A = ∑_m T_mᴴ T_m`,
  i.e. `‖A‖_op² ≤ ∑_{m,m'} ‖T_m T_{m'}ᴴ‖_HS²`.
-/
import Mathlib

namespace Gate1A

namespace FourCycle

open Finset Matrix Complex

variable {ι K I : Type*} [Fintype ι] [Fintype K] [Fintype I]

/-- The (squared) Hilbert–Schmidt norm of a finite complex matrix. -/
noncomputable def hsNormSq {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℂ) : ℝ :=
  ∑ i : m, ∑ j : n, ‖A i j‖ ^ 2

/-- The Hilbert–Schmidt norm as a trace. -/
theorem hsNormSq_eq_trace {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℂ) :
    ((hsNormSq A : ℝ) : ℂ) = Matrix.trace (Aᴴ * A) := by
  classical
  simp only [hsNormSq, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Complex.ofReal_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj, Complex.star_def, mul_comm]

/-- The Gram operator `A = ∑_m T_mᴴ T_m` of a finite family. -/
noncomputable def gram (T : ι → Matrix K I ℂ) : Matrix I I ℂ := ∑ m : ι, (T m)ᴴ * T m

omit [Fintype I] in
/-- The Gram operator is self-adjoint. -/
theorem gram_conjTranspose (T : ι → Matrix K I ℂ) : (gram T)ᴴ = gram T := by
  simp [gram, Matrix.conjTranspose_sum, Matrix.conjTranspose_mul]

/-- **`outer_four_cycle_trace`.**  The exact four-cycle trace identity

`tr((∑_m T_mᴴ T_m)ᴴ (∑_m T_mᴴ T_m)) = ∑_{m,m'} tr((T_m T_{m'}ᴴ)ᴴ (T_m T_{m'}ᴴ))`. -/
theorem outer_four_cycle_trace (T : ι → Matrix K I ℂ) :
    Matrix.trace ((gram T)ᴴ * gram T)
      = ∑ m : ι, ∑ m' : ι,
          Matrix.trace ((T m * (T m')ᴴ)ᴴ * (T m * (T m')ᴴ)) := by
  classical
  rw [gram_conjTranspose]
  have hexpand : gram T * gram T
      = ∑ m : ι, ∑ m' : ι, ((T m)ᴴ * T m) * ((T m')ᴴ * T m') := by
    rw [gram, Matrix.sum_mul]
    exact Finset.sum_congr rfl fun m _ => by rw [Matrix.mul_sum]
  rw [hexpand, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Matrix.trace_sum]
  refine Finset.sum_congr rfl fun m' _ => ?_
  -- `tr(T_mᴴ T_m T_{m'}ᴴ T_{m'}) = tr(T_{m'} T_mᴴ T_m T_{m'}ᴴ)` by cyclicity
  have hassoc : ((T m)ᴴ * T m) * ((T m')ᴴ * T m')
      = (((T m)ᴴ * T m) * (T m')ᴴ) * T m' := by
    simp [Matrix.mul_assoc]
  rw [hassoc, Matrix.trace_mul_comm]
  congr 1
  simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]

/-- **`outer_four_cycle_matrix`.**  The four-cycle identity in Hilbert–Schmidt
norms: `‖∑_m T_mᴴ T_m‖_HS² = ∑_{m,m'} ‖T_m T_{m'}ᴴ‖_HS²`.

In particular `‖∑_m T_mᴴ T_m‖_HS² ≤ ∑_{m,m'} ‖T_m T_{m'}ᴴ‖_HS²`. -/
theorem outer_four_cycle_matrix (T : ι → Matrix K I ℂ) :
    hsNormSq (gram T) = ∑ m : ι, ∑ m' : ι, hsNormSq (T m * (T m')ᴴ) := by
  have h := outer_four_cycle_trace T
  rw [← hsNormSq_eq_trace] at h
  have h2 : ((hsNormSq (gram T) : ℝ) : ℂ)
      = ((∑ m : ι, ∑ m' : ι, hsNormSq (T m * (T m')ᴴ) : ℝ) : ℂ) := by
    rw [h]
    push_cast
    exact Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun m' _ =>
      (hsNormSq_eq_trace _).symm
  exact_mod_cast h2

/-! ### The operator layer -/

/-- Cauchy–Schwarz for the matrix action: `‖A x‖² ≤ ‖A‖_HS² ‖x‖²`. -/
theorem mulVec_normSq_le {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℂ) (x : n → ℂ) :
    (∑ i : m, ‖(A *ᵥ x) i‖ ^ 2) ≤ hsNormSq A * ∑ j : n, ‖x j‖ ^ 2 := by
  classical
  have hrow : ∀ i : m, ‖(A *ᵥ x) i‖ ^ 2
      ≤ (∑ j : n, ‖A i j‖ ^ 2) * ∑ j : n, ‖x j‖ ^ 2 := by
    intro i
    have h1 : ‖(A *ᵥ x) i‖ ≤ ∑ j : n, ‖A i j‖ * ‖x j‖ := by
      have hval : (A *ᵥ x) i = ∑ j : n, A i j * x j := by
        simp [Matrix.mulVec, dotProduct]
      rw [hval]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
      rw [norm_mul]
    calc ‖(A *ᵥ x) i‖ ^ 2 ≤ (∑ j : n, ‖A i j‖ * ‖x j‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ (∑ j : n, ‖A i j‖ ^ 2) * ∑ j : n, ‖x j‖ ^ 2 :=
          Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  calc (∑ i : m, ‖(A *ᵥ x) i‖ ^ 2)
      ≤ ∑ i : m, (∑ j : n, ‖A i j‖ ^ 2) * ∑ j : n, ‖x j‖ ^ 2 :=
        Finset.sum_le_sum fun i _ => hrow i
    _ = hsNormSq A * ∑ j : n, ‖x j‖ ^ 2 := by
        rw [hsNormSq, Finset.sum_mul]

/-- **`outer_four_cycle_operator`.**  For `A = ∑_m T_mᴴ T_m`,

`‖A x‖² ≤ (∑_{m,m'} ‖T_m T_{m'}ᴴ‖_HS²) · ‖x‖²`,

i.e. `‖A‖_op² ≤ ∑_{m,m'} ‖T_m T_{m'}ᴴ‖_HS²`. -/
theorem outer_four_cycle_operator (T : ι → Matrix K I ℂ) (x : I → ℂ) :
    (∑ i : I, ‖(gram T *ᵥ x) i‖ ^ 2)
      ≤ (∑ m : ι, ∑ m' : ι, hsNormSq (T m * (T m')ᴴ)) * ∑ j : I, ‖x j‖ ^ 2 := by
  rw [← outer_four_cycle_matrix]
  exact mulVec_normSq_le _ _

end FourCycle

end Gate1A
