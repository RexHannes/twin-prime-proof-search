/-
# Gate-1A (A7): theta-phase nuclear separation

The theta phase `exp(c · θ · x)` is *not* discarded.  It is separated
exactly into a nuclear (rank-one per degree) sum of products
`(θ^i) ⊗ (x^i)` with explicitly bounded `ℓ¹` coefficient mass, and a
factorially decaying tail.

* `theta_phase_separated` — the exact algebraic separation of the truncated
  expansion;
* `theta_phase_nuclear_cost` — the `ℓ¹` nuclear cost is at most `exp‖c‖`,
  uniformly in the truncation length;
* `theta_phase_tail_bound` — the tail is factorially small.

This is the precise sense in which "theta EXACTLY RETAINED" (Route A of
`Gate1A/ErrorAlgebra.lean`) is available at finite nuclear cost.
-/
import Mathlib

namespace Gate1A

namespace ThetaPhase

open Finset

/-- **`theta_phase_separated`.**  The truncated exponential of a product
`c·θ·x` separates exactly into rank-one terms in `θ` and `x`. -/
theorem theta_phase_separated (c theta x : ℂ) (n : ℕ) :
    (∑ i ∈ range n, (c * theta * x) ^ i / (i.factorial : ℂ))
      = ∑ i ∈ range n, (c ^ i / (i.factorial : ℂ)) * theta ^ i * x ^ i := by
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_pow, mul_pow]
  ring

/-- **`theta_phase_nuclear_cost`.**  The `ℓ¹` mass of the separated
coefficients is at most `exp‖c‖`, uniformly in the truncation length. -/
theorem theta_phase_nuclear_cost (c : ℂ) (n : ℕ) :
    (∑ i ∈ range n, ‖c ^ i / (i.factorial : ℂ)‖) ≤ Real.exp ‖c‖ := by
  have hrw : ∀ i : ℕ, ‖c ^ i / (i.factorial : ℂ)‖ = ‖c‖ ^ i / (i.factorial : ℝ) := by
    intro i
    rw [norm_div, norm_pow]
    congr 1
    simp
  rw [Finset.sum_congr rfl (fun i (_ : i ∈ range n) => hrw i)]
  exact Real.sum_le_exp_of_nonneg (norm_nonneg c) n

/-- **`theta_phase_tail_bound`.**  For `‖z‖ ≤ 1` the truncation error of the
theta phase is factorially small in the truncation length. -/
theorem theta_phase_tail_bound (z : ℂ) (hz : ‖z‖ ≤ 1) {n : ℕ} (hn : 0 < n) :
    ‖Complex.exp z - ∑ i ∈ range n, z ^ i / (i.factorial : ℂ)‖
      ≤ ‖z‖ ^ n * ((n.succ : ℝ) * ((n.factorial : ℝ) * (n : ℝ))⁻¹) :=
  Complex.exp_bound hz hn

/-- The tail bound in the form actually used: for a product phase
`z = c·θ·x` of modulus at most `1`, the error after `n` separated modes is
at most `2/n!`. -/
theorem theta_phase_tail_bound_simple (z : ℂ) (hz : ‖z‖ ≤ 1) {n : ℕ} (hn : 0 < n) :
    ‖Complex.exp z - ∑ i ∈ range n, z ^ i / (i.factorial : ℂ)‖
      ≤ 2 / (n.factorial : ℝ) := by
  refine (theta_phase_tail_bound z hz hn).trans ?_
  have hfac : (0 : ℝ) < (n.factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos n
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hzn : ‖z‖ ^ n ≤ 1 := pow_le_one₀ (norm_nonneg _) hz
  have hsucc : ((n.succ : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  rw [hsucc]
  have hkey : ((n : ℝ) + 1) * (((n.factorial : ℝ)) * (n : ℝ))⁻¹ ≤ 2 / (n.factorial : ℝ) := by
    rw [div_eq_inv_mul, mul_inv, ← mul_assoc]
    rw [mul_comm ((n : ℝ) + 1) ((n.factorial : ℝ))⁻¹, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [mul_comm]
    rw [inv_mul_le_iff₀ hnpos]
    have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  calc ‖z‖ ^ n * (((n : ℝ) + 1) * (((n.factorial : ℝ)) * (n : ℝ))⁻¹)
      ≤ 1 * (((n : ℝ) + 1) * (((n.factorial : ℝ)) * (n : ℝ))⁻¹) := by
        refine mul_le_mul_of_nonneg_right hzn (by positivity)
    _ = ((n : ℝ) + 1) * (((n.factorial : ℝ)) * (n : ℝ))⁻¹ := one_mul _
    _ ≤ 2 / (n.factorial : ℝ) := hkey

end ThetaPhase

end Gate1A
