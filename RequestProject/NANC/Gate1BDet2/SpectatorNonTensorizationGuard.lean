import Mathlib

/-!
# Gate 1B / determinant-2 bank, Module 39: spectator non-tensorization guard

A finite-dimensional guard against the false inference

  "two labelled factors each have square-root capacity"
    ⟹  "their gains automatically multiply".

The model is elementary: on `ℝ × ℝ` with the squared Euclidean functional
`nsq (a, b) = a² + b²`, take the coordinate projection `P (a, b) = (a, 0)` as
*both* view operators and the latent vector `v = (1, 1)`.  Each view contracts
`nsq` by exactly `1/2` (square-root capacity in norm), yet the composition
contracts by `1/2` again — not by `1/4`.

The general reason is banked too (`identical_view_operators_do_not_compound`):
an idempotent view with contraction factor `c` composes to contraction factor
`c`, and `c = c²` forces `c ∈ {0, 1}`.

**This is a logical/operator guard only**; no Mellin resonance example and no
analytic statement is formalized.
-/

namespace TwinPrimeProject
namespace Gate1BDet2
namespace Spectator

/-- The squared Euclidean functional on the latent coordinate space. -/
def nsq (x : ℝ × ℝ) : ℝ := x.1 ^ 2 + x.2 ^ 2

/-- The coordinate "view" operator `P (a, b) = (a, 0)`. -/
def viewP : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ := (LinearMap.fst ℝ ℝ ℝ).prod 0

@[simp] theorem viewP_apply (x : ℝ × ℝ) : viewP x = (x.1, 0) := rfl

theorem viewP_idem (x : ℝ × ℝ) : viewP (viewP x) = viewP x := rfl

/-! ## 1. The general non-compounding statement -/

/-- **Idempotent views do not compound.**  If a view operator `A` is idempotent
on the latent vector `v` and contracts `nsq` by a factor `c`, then the
composition contracts by the *same* factor `c`; assuming `c = c²` forces
`c ∈ {0, 1}`.  Hence a strict gain `0 < c < 1` cannot be squared. -/
theorem identical_view_operators_do_not_compound {A : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ} {v : ℝ × ℝ} {c : ℝ}
    (hidem : A (A v) = A v) (hgain : nsq (A v) = c * nsq v)
    (hc0 : 0 < c) (hc1 : c < 1) (hv : nsq v ≠ 0) :
    nsq (A (A v)) ≠ c ^ 2 * nsq v := by
  rw [hidem, hgain]
  intro h
  have hc : c = c ^ 2 := by
    have := mul_right_cancel₀ hv h
    linarith [this]
  nlinarith

/-! ## 2. The explicit finite-dimensional countermodel -/

/-- **`factor_count_does_not_imply_independent_operator_gain`.**  Two view
operators (here literally the same projection, acting on the same latent
coordinate) each contract `nsq` by exactly `1/2`, while their composition still
contracts only by `1/2` — not by `1/4`.  Counting factors therefore does not
license multiplying gains. -/
theorem factor_count_does_not_imply_independent_operator_gain :
    ∃ (A B : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ) (v : ℝ × ℝ),
      nsq v ≠ 0 ∧ nsq (A v) = nsq v / 2 ∧ nsq (B v) = nsq v / 2 ∧
        nsq (B (A v)) ≠ nsq v / 4 := by
  refine ⟨viewP, viewP, (1, 1), ?_, ?_, ?_, ?_⟩ <;> norm_num [nsq]

/-- The same separation phrased with contraction factors: each factor has
capacity `1/2`, the composition has capacity `1/2 ≠ (1/2)²`. -/
theorem composition_gain_is_not_the_product_of_gains :
    nsq (viewP (viewP (1, 1))) = (1 / 2 : ℝ) * nsq ((1, 1) : ℝ × ℝ)
      ∧ nsq (viewP (viewP (1, 1))) ≠ ((1 / 2 : ℝ)) ^ 2 * nsq ((1, 1) : ℝ × ℝ) := by
  constructor <;> norm_num [nsq]

end Spectator
end Gate1BDet2
end TwinPrimeProject
