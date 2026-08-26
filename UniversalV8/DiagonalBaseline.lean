/-
# UniversalV8 Module H — diagonal / off-diagonal baseline

Exact finite decomposition of a Gram square into its diagonal and off-diagonal parts,
plus the elementary budget consequences.  No analytic off-diagonal estimate is asserted
anywhere (see `UniversalV8/Interfaces.lean`, `NPL-OFF45` is open).
-/
import Mathlib

open Finset

namespace UniversalV8

/-- Splitting a double sum over a finite type into diagonal and off-diagonal parts. -/
theorem sum_sum_eq_diag_add_offDiag {ι M : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommMonoid M] (f : ι → ι → M) :
    ∑ i, ∑ j, f i j
      = (∑ i, f i i) + ∑ p ∈ (Finset.univ : Finset ι).offDiag, f p.1 p.2 := by
  rw [← Finset.sum_product', ← Finset.diag_union_offDiag (Finset.univ : Finset ι),
    Finset.sum_union (Finset.disjoint_diag_offDiag _), Finset.sum_diag]

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-- The exact Gram expansion of the squared norm of a finite sum of Hilbert vectors. -/
theorem gram_expand {Γ : Type*} [Fintype Γ] (v : Γ → K) :
    ‖∑ γ, v γ‖ ^ 2 = ∑ γ, ∑ γ', (inner ℂ (v γ) (v γ') : ℂ).re := by
  have h : (inner ℂ (∑ γ, v γ) (∑ γ, v γ) : ℂ).re = ‖∑ γ, v γ‖ ^ 2 := by
    rw [inner_self_eq_norm_sq_to_K]; simp [sq, Complex.mul_re]
  rw [← h, sum_inner, Complex.re_sum]
  exact Finset.sum_congr rfl fun γ _ => by rw [inner_sum, Complex.re_sum]

/-- **Diagonal-baseline decomposition.** `‖∑ z_γ v_γ‖² = D + O` with
`D = ∑ |z_γ|² ‖v_γ‖²` and `O` the off-diagonal Gram sum. -/
theorem gram_eq_diag_add_offdiag {Γ : Type*} [Fintype Γ] [DecidableEq Γ]
    (z : Γ → ℂ) (v : Γ → K) :
    ‖∑ γ, z γ • v γ‖ ^ 2
      = (∑ γ, ‖z γ‖ ^ 2 * ‖v γ‖ ^ 2)
        + ∑ p ∈ (Finset.univ : Finset Γ).offDiag,
            (inner ℂ (z p.1 • v p.1) (z p.2 • v p.2) : ℂ).re := by
  rw [gram_expand, ← Finset.sum_product',
    ← Finset.diag_union_offDiag (Finset.univ : Finset Γ),
    Finset.sum_union (Finset.disjoint_diag_offDiag _), Finset.sum_diag]
  congr 1
  refine Finset.sum_congr rfl fun γ _ => ?_
  have hz : ‖z γ‖ ^ 2 = (z γ).re ^ 2 + (z γ).im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
  rw [inner_smul_left, inner_smul_right, inner_self_eq_norm_sq_to_K]
  simp [sq, Complex.mul_re, hz]
  ring

/-- Budget consequence: a diagonal budget plus an off-diagonal budget bound the total. -/
theorem diagOffDiag_budget {Γ : Type*} [Fintype Γ] [DecidableEq Γ] (z : Γ → ℂ) (v : Γ → K)
    (TD TO : ℝ) (hD : (∑ γ, ‖z γ‖ ^ 2 * ‖v γ‖ ^ 2) ≤ TD)
    (hO : (∑ p ∈ (Finset.univ : Finset Γ).offDiag,
            (inner ℂ (z p.1 • v p.1) (z p.2 • v p.2) : ℂ).re) ≤ TO) :
    ‖∑ γ, z γ • v γ‖ ^ 2 ≤ TD + TO := by
  rw [gram_eq_diag_add_offdiag]
  exact add_le_add hD hO

/-- "Diagonal already below budget": if the diagonal costs at most `TD` then only the
remaining budget `T - TD` has to be supplied by the off-diagonal estimate. -/
theorem diagOffDiag_budget_remaining {Γ : Type*} [Fintype Γ] [DecidableEq Γ]
    (z : Γ → ℂ) (v : Γ → K) (T TD : ℝ)
    (hD : (∑ γ, ‖z γ‖ ^ 2 * ‖v γ‖ ^ 2) ≤ TD)
    (hO : (∑ p ∈ (Finset.univ : Finset Γ).offDiag,
            (inner ℂ (z p.1 • v p.1) (z p.2 • v p.2) : ℂ).re) ≤ T - TD) :
    ‖∑ γ, z γ • v γ‖ ^ 2 ≤ T := by
  have := diagOffDiag_budget z v TD (T - TD) hD hO
  linarith

/-! ## Matrix / quadratic-form version of the same decomposition -/

/-- Exact diagonal / off-diagonal decomposition of a finite quadratic form
`∑_{i,j} conj(z i) G i j (z j)`. -/
theorem quadraticForm_eq_diag_add_offDiag {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : ι → ι → ℂ) (z : ι → ℂ) :
    ∑ i, ∑ j, (starRingEnd ℂ) (z i) * G i j * z j
      = (∑ i, (starRingEnd ℂ) (z i) * G i i * z i)
        + ∑ p ∈ (Finset.univ : Finset ι).offDiag,
            (starRingEnd ℂ) (z p.1) * G p.1 p.2 * z p.2 :=
  sum_sum_eq_diag_add_offDiag _

end UniversalV8
