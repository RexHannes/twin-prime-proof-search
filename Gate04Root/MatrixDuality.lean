/-
# Gate04Root.MatrixDuality

Exact finite fourth-moment duality for a finite rectangular complex matrix
`B : E → P → ℂ`.

With the row Gram kernel `H(e,f) = ∑_p B e p * conj (B f p)` and the column Gram
kernel `G(p₁,p₂) = ∑_e B e p₁ * conj (B e p₂)` we prove

* `trace_BBstar_sq_row_expansion` :  `tr((B Bᴴ)²) = ∑_{e,f} |H(e,f)|²`;
* `trace_BBstar_sq_column_expansion` : `tr((B Bᴴ)²) = ∑_{p₁,p₂} |G(p₁,p₂)|²`;
* `fourthMoment_row_eq_column` : the real form of the same identity;
* `column_pair_diagonal_offDiagonal_split` : the diagonal / off-diagonal split.

These are exact identities; no analytic input is involved.
-/
import Mathlib

open Finset Complex
open scoped Matrix

namespace Gate04Root

variable {E P : Type*} [Fintype E] [Fintype P]

/-- Row Gram kernel `H(e,f) = ∑_p B e p conj (B f p)`. -/
noncomputable def rowGram (B : E → P → ℂ) (e f : E) : ℂ := ∑ p, B e p * (starRingEnd ℂ) (B f p)

/-- Column Gram kernel `G(p₁,p₂) = ∑_e B e p₁ conj (B e p₂)`. -/
noncomputable def colGram (B : E → P → ℂ) (p₁ p₂ : P) : ℂ := ∑ e, B e p₁ * (starRingEnd ℂ) (B e p₂)

/-- The (real) fourth moment `∑_{e,f} |H(e,f)|²`. -/
noncomputable def fourthMoment (B : E → P → ℂ) : ℝ := ∑ e, ∑ f, ‖rowGram B e f‖ ^ 2

/-- The (real) column fourth moment `∑_{p₁,p₂} |G(p₁,p₂)|²`. -/
noncomputable def colFourthMoment (B : E → P → ℂ) : ℝ := ∑ p₁, ∑ p₂, ‖colGram B p₁ p₂‖ ^ 2

private theorem normSq_cast (z : ℂ) : ((‖z‖ ^ 2 : ℝ) : ℂ) = z * (starRingEnd ℂ) z := by
  rw [Complex.mul_conj]
  norm_cast
  exact (Complex.normSq_eq_norm_sq z).symm

omit [Fintype E] in
theorem rowGram_swap (B : E → P → ℂ) (e f : E) :
    rowGram B f e = (starRingEnd ℂ) (rowGram B e f) := by
  simp [rowGram, map_sum, mul_comm]

/-- Four-fold sum reordering used for the duality. -/
private theorem sum4_comm (T : E → E → P → P → ℂ) :
    ∑ e, ∑ f, ∑ p₁, ∑ p₂, T e f p₁ p₂ = ∑ p₁, ∑ p₂, ∑ e, ∑ f, T e f p₁ p₂ := by
  have h1 : ∑ e, ∑ f, ∑ p₁, ∑ p₂, T e f p₁ p₂
      = ∑ x : (E × E) × (P × P), T x.1.1 x.1.2 x.2.1 x.2.2 := by
    simp [Fintype.sum_prod_type]
  have h2 : ∑ p₁, ∑ p₂, ∑ e, ∑ f, T e f p₁ p₂
      = ∑ y : (P × P) × (E × E), T y.2.1 y.2.2 y.1.1 y.1.2 := by
    simp [Fintype.sum_prod_type]
  rw [h1, h2]
  exact Fintype.sum_equiv (Equiv.prodComm _ _) _ _ (fun _ => rfl)

/-- **(ROW-DUAL / PPD-DUAL, complex form)** both Gram expansions of the fourth
moment agree. -/
theorem rowGram_sq_eq_colGram_sq (B : E → P → ℂ) :
    ∑ e, ∑ f, rowGram B e f * (starRingEnd ℂ) (rowGram B e f)
      = ∑ p₁, ∑ p₂, colGram B p₁ p₂ * (starRingEnd ℂ) (colGram B p₁ p₂) := by
  have hL : ∑ e, ∑ f, rowGram B e f * (starRingEnd ℂ) (rowGram B e f)
      = ∑ e, ∑ f, ∑ p₁, ∑ p₂,
          (B e p₁ * (starRingEnd ℂ) (B f p₁)) *
            ((starRingEnd ℂ) (B e p₂) * B f p₂) := by
    refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun f _ => ?_
    simp only [rowGram, map_sum, map_mul, Complex.conj_conj]
    rw [Finset.sum_mul_sum]
  have hR : ∑ p₁, ∑ p₂, colGram B p₁ p₂ * (starRingEnd ℂ) (colGram B p₁ p₂)
      = ∑ p₁, ∑ p₂, ∑ e, ∑ f,
          (B e p₁ * (starRingEnd ℂ) (B f p₁)) *
            ((starRingEnd ℂ) (B e p₂) * B f p₂) := by
    refine Finset.sum_congr rfl fun p₁ _ => Finset.sum_congr rfl fun p₂ _ => ?_
    simp only [colGram, map_sum, map_mul, Complex.conj_conj]
    rw [Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun f _ => by ring
  rw [hL, hR]
  exact sum4_comm _

/-- **Real form of the duality**: `∑_{e,f} |H(e,f)|² = ∑_{p₁,p₂} |G(p₁,p₂)|²`. -/
theorem fourthMoment_row_eq_column (B : E → P → ℂ) :
    fourthMoment B = colFourthMoment B := by
  have h := rowGram_sq_eq_colGram_sq B
  have hL : ((fourthMoment B : ℝ) : ℂ)
      = ∑ e, ∑ f, rowGram B e f * (starRingEnd ℂ) (rowGram B e f) := by
    simp only [fourthMoment, Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun f _ => normSq_cast _
  have hR : ((colFourthMoment B : ℝ) : ℂ)
      = ∑ p₁, ∑ p₂, colGram B p₁ p₂ * (starRingEnd ℂ) (colGram B p₁ p₂) := by
    simp only [colFourthMoment, Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun p₁ _ => Finset.sum_congr rfl fun p₂ _ => normSq_cast _
  have : ((fourthMoment B : ℝ) : ℂ) = ((colFourthMoment B : ℝ) : ℂ) := by
    rw [hL, hR, h]
  exact_mod_cast this

section Trace

variable [DecidableEq E]

/-- `tr((B Bᴴ)²)` as an explicit double sum of Gram kernels. -/
theorem trace_BBstar_sq (B : E → P → ℂ) :
    Matrix.trace ((Matrix.of B * (Matrix.of B)ᴴ) ^ 2)
      = ∑ e, ∑ f, rowGram B e f * rowGram B f e := by
  simp [pow_two, Matrix.trace, Matrix.diag, Matrix.mul_apply, rowGram,
    Matrix.conjTranspose_apply, Finset.mul_sum, mul_comm]

/-- **(ROW-DUAL)**  `tr((B Bᴴ)²) = ∑_{e,f} |H(e,f)|²`. -/
theorem trace_BBstar_sq_row_expansion (B : E → P → ℂ) :
    Matrix.trace ((Matrix.of B * (Matrix.of B)ᴴ) ^ 2)
      = ((fourthMoment B : ℝ) : ℂ) := by
  rw [trace_BBstar_sq]
  simp only [fourthMoment, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun f _ => ?_
  rw [normSq_cast, rowGram_swap]
  simp [mul_comm]

/-- **(PPD-DUAL)**  `tr((B Bᴴ)²) = ∑_{p₁,p₂} |G(p₁,p₂)|²`. -/
theorem trace_BBstar_sq_column_expansion (B : E → P → ℂ) :
    Matrix.trace ((Matrix.of B * (Matrix.of B)ᴴ) ^ 2)
      = ((colFourthMoment B : ℝ) : ℂ) := by
  rw [trace_BBstar_sq_row_expansion, fourthMoment_row_eq_column]

end Trace

/-- **Diagonal / off-diagonal split of a double sum over pairs of columns.** -/
theorem column_pair_diagonal_offDiagonal_split [DecidableEq P] (F : P → P → ℝ) :
    ∑ p₁, ∑ p₂, F p₁ p₂
      = (∑ p, F p p) + ∑ x ∈ Finset.univ.filter (fun x : P × P => x.1 ≠ x.2), F x.1 x.2 := by
  have h1 : ∑ p₁, ∑ p₂, F p₁ p₂ = ∑ x : P × P, F x.1 x.2 := by
    simp [Fintype.sum_prod_type]
  have h2 : ∑ x : P × P, F x.1 x.2
      = (∑ x ∈ Finset.univ.filter (fun x : P × P => x.1 = x.2), F x.1 x.2)
        + ∑ x ∈ Finset.univ.filter (fun x : P × P => x.1 ≠ x.2), F x.1 x.2 :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have h3 : (∑ x ∈ Finset.univ.filter (fun x : P × P => x.1 = x.2), F x.1 x.2)
      = ∑ p, F p p := by
    refine Finset.sum_nbij' (fun x => x.1) (fun p => (p, p)) ?_ ?_ ?_ ?_ ?_ <;>
      simp +contextual [Finset.mem_filter, Prod.ext_iff, eq_comm]
  rw [h1, h2, h3]

/-- The off-diagonal column sum. -/
noncomputable def offDiagColSum (B : E → P → ℂ) [DecidableEq P] : ℝ :=
  ∑ x ∈ Finset.univ.filter (fun x : P × P => x.1 ≠ x.2), ‖colGram B x.1 x.2‖ ^ 2

/-- The repeated-`p` (diagonal) column sum. -/
noncomputable def diagColSum (B : E → P → ℂ) : ℝ := ∑ p, ‖colGram B p p‖ ^ 2

/-- The fourth moment splits exactly into repeated-`p` and off-diagonal parts. -/
theorem fourthMoment_split (B : E → P → ℂ) [DecidableEq P] :
    fourthMoment B = diagColSum B + offDiagColSum B := by
  rw [fourthMoment_row_eq_column, colFourthMoment,
    column_pair_diagonal_offDiagonal_split (fun p₁ p₂ => ‖colGram B p₁ p₂‖ ^ 2)]
  rfl

end Gate04Root
