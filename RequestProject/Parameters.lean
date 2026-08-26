import Mathlib

/-!
# Parameters for the F3 (r = 2) tiny-wedge audit

The dispersion analysis is organised in exponent notation
`M = X^μ`, `N = X^{1-μ}`, `Q = X^{1/2+θ}`.  This module fixes the nonnegative
parameters `μ, θ` and records the two wedge predicates as plain real
inequalities, so that all downstream algebra is stated over these named
quantities.
-/

namespace ShiftedMobiusBank

/-- The exponent parameters of the tiny cell: `M = X^μ`, `N = X^{1-μ}`,
`Q = X^{1/2+θ}`, with `μ, θ ≥ 0`. -/
structure Params where
  mu : ℝ
  theta : ℝ
  mu_nonneg : 0 ≤ mu
  theta_nonneg : 0 ≤ theta

/-- The older tiny wedge `206μ + 274θ < 1`. -/
def oldWedge (p : Params) : Prop := 206 * p.mu + 274 * p.theta < 1

/-- The current, widened tiny wedge `122μ + 162θ < 1`. -/
def newWedge (p : Params) : Prop := 122 * p.mu + 162 * p.theta < 1

/-- The gap parameter `Δ = 1 - 122μ - 162θ` used to build the small/large-`D`
splitting exponent `σ`. -/
noncomputable def gap (p : Params) : ℝ := 1 - 122 * p.mu - 162 * p.theta

/-- The small/large-`D` splitting exponent `σ = 2μ + 4θ + Δ/10`. -/
noncomputable def sigmaSplit (p : Params) : ℝ := 2 * p.mu + 4 * p.theta + gap p / 10

end ShiftedMobiusBank
