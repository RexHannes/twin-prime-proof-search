/-
# Gate 1B v8.4 — countermodels and firewalls

**Status: PROVED_FINITE (all four are explicit finite constructions).**

A. INFINITE TAIL — "rapidly decaying" does not mean "compactly supported": a
   geometric weight is summable but has *every* frequency in its support, so no
   single-frequency conclusion may be drawn from the infinite dual sum.

B. ZERO POWER — an abstract bound at natural scale does not imply a prescribed
   smaller target: `x ≤ 1` does not give `x ≤ 1/2`.

C. MU RESOURCE — a source sign can cancel inside a projector identity, and so is
   not available for reuse afterwards: `μ(c₀) · μ(c₀) = 1`.

D. SELF-DUALITY — shell reassociation alone gives no improved analytic bound:
   the same shell is compatible with two different weights of different sizes.
-/
import Mathlib

namespace Gate1B.SafeAlgebra

open scoped ArithmeticFunction.Moebius
open ArithmeticFunction

/-! ## A. Infinite tail: rapid decay ≠ compact support -/

/-- The geometric weight `w n = 2^{-n}` is summable … -/
theorem countermodelA_summable : Summable (fun n : ℕ => (1 : ℝ) / 2 ^ n) := by
  simpa using summable_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2)
    (by norm_num : (1:ℝ)/2 < 1)

/-- … but it is nowhere zero: its support is all of `ℕ`, so a rapidly decaying
dual weight cannot be truncated to a single frequency without an additional
(analytic) truncation step. -/
theorem countermodelA_support_infinite : ∀ n : ℕ, (1 : ℝ) / 2 ^ n ≠ 0 := by
  intro n; positivity

/-! ## B. Zero power: natural scale does not imply a smaller target -/

/-- A bound at natural scale (`x ≤ 1`) does not imply any prescribed smaller
target (`x ≤ 1/2`). -/
theorem countermodelB_natural_scale_insufficient :
    ∃ x : ℝ, x ≤ 1 ∧ ¬ (x ≤ 1 / 2) := ⟨1, le_refl 1, by norm_num⟩

/-- Exponent form: exponent `0` does not give exponent `-η` for any `η > 0`. -/
theorem countermodelB_exponent_zero {eta : ℚ} (h : 0 < eta) : ¬ ((0 : ℚ) ≤ -eta) := by
  linarith

/-! ## C. Mu resource: a sign spent in a projector identity cannot be reused -/

/-- For squarefree `c₀` the sign `μ(c₀)` cancels against itself: after the
projector identity has consumed one copy, no independent sign remains. -/
theorem countermodelC_mu_cancels {c0 : ℕ} (h : Squarefree c0) : μ c0 * μ c0 = 1 := by
  have := ArithmeticFunction.moebius_sq_eq_one_of_squarefree h
  nlinarith [this]

/-- Concrete instance: `μ(6) μ(6) = 1`, although `μ(6) = 1` and `μ(2) = -1` are
different signs — the projector identity fixes which one is already spent. -/
theorem countermodelC_concrete : μ 6 * μ 6 = 1 ∧ μ 2 = -1 := by
  refine ⟨countermodelC_mu_cancels (by decide +kernel), ?_⟩
  exact ArithmeticFunction.moebius_apply_prime Nat.prime_two

/-! ## D. Self-duality: shell reassociation is not an analytic improvement -/

/-- The determinant shell `n N - c ℓ = 2` is satisfied by data whose weights may
be of completely different sizes: the shell alone carries no size information.
Here two different `(n, N, c, ℓ)` solutions of the same shape are exhibited. -/
theorem countermodelD_shell_not_size :
    (3 : ℤ) * 4 - 5 * 2 = 2 ∧ (7 : ℤ) * 5 - 11 * 3 = 2 := by
  constructor <;> norm_num

/-- Two "weights" attached to the two shell solutions above can differ by an
arbitrary factor: reassociation of the shell does not bound the weight. -/
theorem countermodelD_weights_unbounded (K : ℝ) : ∃ w1 w2 : ℝ, w1 = 1 ∧ w2 = K := ⟨1, K, rfl, rfl⟩

end Gate1B.SafeAlgebra
