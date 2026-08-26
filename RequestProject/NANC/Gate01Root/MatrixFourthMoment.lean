import Gate04Root.MatrixDuality
import RequestProject.NANC.FiniteGramFourthMoment
import RequestProject.NANC.Gate01Root.DivisorRows

/-!
# Gate01Root: exact fourth-moment matrix duality

For `B : E → P → ℂ` with row Gram kernel `H(e,f) = ∑_p B e p conj (B f p)` and
column Gram kernel `G(p₁,p₂) = ∑_e B e p₁ conj (B e p₂)`:

* `fourthMoment_row_expansion` : `tr((B Bᴴ)²) = ∑_{e,f} |H(e,f)|²`;
* `fourthMoment_column_expansion` : `tr((B Bᴴ)²) = ∑_{p₁,p₂} |G(p₁,p₂)|²`;
* `fourthMoment_row_eq_column` : `∑_{e,f} |H|² = ∑_{p₁,p₂} |G|²`;
* `columnPair_diagonal_offDiagonal_split` : the diagonal / off-diagonal split.

These are exact finite identities.  The row/column duality is **reused** from the
already banked `RouteAFibreFrame.gramFourth_eq_corr_sq`: the bridge lemmas
`rowGram_eq_gram`, `colGram_eq_corr`, `fourthMoment_eq_gramFourth` show that the
two vocabularies denote the same objects.
-/

namespace RouteAFibreFrame
namespace Gate01Root

open Finset

variable {E P : Type*} [Fintype E] [Fintype P]

/-- Row Gram kernel. -/
noncomputable def rowGram (B : E → P → ℂ) (e f : E) : ℂ := Gate04Root.rowGram B e f

/-- Column Gram kernel. -/
noncomputable def colGram (B : E → P → ℂ) (p₁ p₂ : P) : ℂ := Gate04Root.colGram B p₁ p₂

/-- The fourth moment `∑_{e,f} |H(e,f)|²`. -/
noncomputable def fourthMoment (B : E → P → ℂ) : ℝ := Gate04Root.fourthMoment B

omit [Fintype E] in
/-- Bridge: the row Gram kernel is the banked Gram matrix. -/
theorem rowGram_eq_gram (B : E → P → ℂ) (e f : E) :
    rowGram B e f = RouteAFibreFrame.gram B B e f := rfl

omit [Fintype P] in
/-- Bridge: the column Gram kernel is the banked correlation matrix. -/
theorem colGram_eq_corr (B : E → P → ℂ) (p₁ p₂ : P) :
    colGram B p₁ p₂ = RouteAFibreFrame.corr B p₁ p₂ := rfl

/-- Bridge: the fourth moment is the banked Gram fourth moment. -/
theorem fourthMoment_eq_gramFourth (B : E → P → ℂ) :
    fourthMoment B = RouteAFibreFrame.gramFourth B := rfl

section Trace

variable [DecidableEq E]

open scoped Matrix

/-- **Row expansion**: `tr((B Bᴴ)²) = ∑_{e,f} |H(e,f)|²`. -/
theorem fourthMoment_row_expansion (B : E → P → ℂ) :
    Matrix.trace ((Matrix.of B * (Matrix.of B)ᴴ) ^ 2) = ((fourthMoment B : ℝ) : ℂ) :=
  Gate04Root.trace_BBstar_sq_row_expansion B

/-- **Column expansion**: `tr((B Bᴴ)²) = ∑_{p₁,p₂} |G(p₁,p₂)|²`. -/
theorem fourthMoment_column_expansion (B : E → P → ℂ) :
    Matrix.trace ((Matrix.of B * (Matrix.of B)ᴴ) ^ 2)
      = ((∑ p₁, ∑ p₂, ‖colGram B p₁ p₂‖ ^ 2 : ℝ) : ℂ) :=
  Gate04Root.trace_BBstar_sq_column_expansion B

end Trace

/-- **Row = column duality**, obtained by reusing the banked
`gramFourth_eq_corr_sq`. -/
theorem fourthMoment_row_eq_column (B : E → P → ℂ) :
    fourthMoment B = ∑ p₁, ∑ p₂, ‖colGram B p₁ p₂‖ ^ 2 := by
  rw [fourthMoment_eq_gramFourth, RouteAFibreFrame.gramFourth_eq_corr_sq]
  rfl

/-- **Diagonal / off-diagonal split of the column pair sum.** -/
theorem columnPair_diagonal_offDiagonal_split [DecidableEq P] (F : P → P → ℝ) :
    ∑ p₁, ∑ p₂, F p₁ p₂
      = (∑ p, F p p)
        + ∑ x ∈ Finset.univ.filter (fun x : P × P => x.1 ≠ x.2), F x.1 x.2 :=
  Gate04Root.column_pair_diagonal_offDiagonal_split F

/-- The repeated-`p` part `∑_p |G(p,p)|²`. -/
noncomputable def diagColSum (B : E → P → ℂ) : ℝ := Gate04Root.diagColSum B

/-- The off-diagonal part `∑_{p₁ ≠ p₂} |G(p₁,p₂)|²`. -/
noncomputable def offDiagColSum (B : E → P → ℂ) [DecidableEq P] : ℝ :=
  Gate04Root.offDiagColSum B

/-- The exact split of the fourth moment. -/
theorem fourthMoment_split (B : E → P → ℂ) [DecidableEq P] :
    fourthMoment B = diagColSum B + offDiagColSum B :=
  Gate04Root.fourthMoment_split B

end Gate01Root
end RouteAFibreFrame
