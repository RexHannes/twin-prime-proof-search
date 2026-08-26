/-
# Universal safe algebra — signed open chain and closed-cycle sign erasure

Two guards, both exact:

* `openChain_two`: the `k = 2` open-chain inequality for a self-adjoint operator;
* `closedCycle_trace_invariant` / `closedCycle_sign_telescopes`: outer signs conjugating a
  Gram matrix change nothing about its trace moments, so closed trace moments cannot
  obtain cancellation from outer signs alone.

No Gate-specific transport bound is asserted.
-/
import Mathlib

open ContinuousLinearMap Finset Matrix

namespace Universal.SafeAlgebra

/-- **Open chain, `k = 2`.**  For a self-adjoint bounded operator `G`,
`(re ⟪z, G z⟫)² ≤ ‖z‖² · re ⟪z, G² z⟫`.  (Positive semidefiniteness is not needed.) -/
theorem openChain_two {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (G : H →L[ℂ] H) (hG : adjoint G = G) (z : H) :
    ((inner ℂ z (G z) : ℂ).re) ^ 2 ≤ ‖z‖ ^ 2 * (inner ℂ z (G (G z)) : ℂ).re := by
  have hsq : (inner ℂ z (G (G z)) : ℂ).re = ‖G z‖ ^ 2 := by
    have h : (inner ℂ z (G (G z)) : ℂ) = inner ℂ (G z) (G z) := by
      nth_rewrite 1 [← hG]
      rw [ContinuousLinearMap.adjoint_inner_right]
    rw [h, inner_self_eq_norm_sq_to_K]; simp [sq, Complex.mul_re]
  rw [hsq]
  have h2 : |(inner ℂ z (G z) : ℂ).re| ≤ ‖z‖ * ‖G z‖ :=
    le_trans (Complex.abs_re_le_norm _) (norm_inner_le_norm _ _)
  nlinarith [abs_nonneg ((inner ℂ z (G z) : ℂ).re), sq_abs ((inner ℂ z (G z) : ℂ).re),
    mul_nonneg (norm_nonneg z) (norm_nonneg (G z))]

/-- **Closed-cycle sign erasure.**  Conjugating a matrix by an invertible (in particular a
diagonal sign/unitary) matrix leaves every trace moment unchanged. -/
theorem closedCycle_trace_invariant {n : Type*} [Fintype n] [DecidableEq n]
    (G D E : Matrix n n ℂ) (h1 : D * E = 1) (h2 : E * D = 1) (k : ℕ) :
    ((E * G * D) ^ k).trace = (G ^ k).trace := by
  have hpow : ∀ k : ℕ, (E * G * D) ^ k = E * G ^ k * D := by
    intro k
    induction k with
    | zero => simp [h2]
    | succ k ih =>
        rw [pow_succ, ih, pow_succ]
        calc E * G ^ k * D * (E * G * D) = E * G ^ k * (D * E) * G * D := by
              simp [Matrix.mul_assoc]
          _ = E * (G ^ k * G) * D := by rw [h1]; simp [Matrix.mul_assoc]
  rw [hpow, Matrix.trace_mul_cycle, h1, Matrix.one_mul]

/-- **Closed-cycle phase telescoping.**  Around a closed cycle the endpoint phases cancel:
`∏_{i<k} ε(i+1) ε(i)⁻¹ = 1` whenever `ε k = ε 0`. -/
theorem closedCycle_sign_telescopes (k : ℕ) (eps : ℕ → ℂˣ) (h : eps k = eps 0) :
    ∏ i ∈ Finset.range k, (eps (i + 1) / eps i) = 1 := by
  rw [Finset.prod_range_div, h]; simp

end Universal.SafeAlgebra
