/-
NANC V4 — Ford–Maynard parameter structure and exact rational width arithmetic.

Everything in this file is exact arithmetic over `ℚ`.  No decimals, no floats.

PERMANENT FIREWALL:
    PARAMETER_RANGE_MATCH  ≠  THEOREM_APPLICATION
Checking that a rational parameter lies in the published admissible range says
nothing about whether the corresponding analytic theorem applies.
-/
import Mathlib

namespace NANC.V4

/-- Structural constraints on a Ford–Maynard parameter triple `(γ, θ, ν)`. -/
structure FMParams where
  gamma : ℚ
  theta : ℚ
  nu : ℚ
  gamma_pos : 0 < gamma
  gamma_lt_one : gamma < 1
  theta_nonneg : 0 ≤ theta
  theta_lt_half : theta < 1 / 2
  nu_pos : 0 < nu
  nu_le : nu ≤ 1 - theta

/-- Central target exponent `γ₀ = 1/2`. -/
def gamma0 : ℚ := 1 / 2

/-- Central target exponent `θ₀ = 0`. -/
def theta0 : ℚ := 0

/-- Central target exponent `ν₀ = 1/6`. -/
def nu0 : ℚ := 1 / 6

/-- The published Ford–Maynard threshold `0.1663`, as an exact rational. -/
def fmThreshold : ℚ := 1663 / 10000

/-- The central parameter triple `(1/2, 0, 1/6)` really satisfies the structural
constraints. -/
def centralParams : FMParams where
  gamma := gamma0
  theta := theta0
  nu := nu0
  gamma_pos := by norm_num [gamma0]
  gamma_lt_one := by norm_num [gamma0]
  theta_nonneg := by norm_num [theta0]
  theta_lt_half := by norm_num [theta0]
  nu_pos := by norm_num [nu0]
  nu_le := by norm_num [nu0, theta0]

/-- Exact rational comparison: `1/6 > 1663/10000`. -/
theorem one_sixth_gt_fm_threshold : fmThreshold < nu0 := by
  norm_num [fmThreshold, nu0]

/-- The exact margin: `1/6 - 1663/10000 = 11/30000`. -/
theorem one_sixth_threshold_margin : nu0 - fmThreshold = 11 / 30000 := by
  norm_num [fmThreshold, nu0]

/-- The `ε`-shrunk parameter triple `(1/2 - ε, ε, 1/6 - 2ε)`. -/
def shrinkParams (eps : ℚ) : ℚ × ℚ × ℚ := (1 / 2 - eps, eps, 1 / 6 - 2 * eps)

@[simp] theorem shrinkParams_gamma (eps : ℚ) : (shrinkParams eps).1 = 1 / 2 - eps := rfl
@[simp] theorem shrinkParams_theta (eps : ℚ) : (shrinkParams eps).2.1 = eps := rfl
@[simp] theorem shrinkParams_nu (eps : ℚ) : (shrinkParams eps).2.2 = 1 / 6 - 2 * eps := rfl

/-- For `0 < ε < 11/60000` the shrunk `ν` still exceeds the published threshold.
(The hypothesis `0 < ε` is kept because it is part of the intended parameter range;
the inequality itself already follows from `ε < 11/60000`.) -/
theorem shrunk_nu_gt_threshold_of_eps_small {eps : ℚ} (h0 : 0 < eps)
    (h1 : eps < 11 / 60000) : fmThreshold < (shrinkParams eps).2.2 := by
  simp only [shrinkParams_nu, fmThreshold]
  have := h0  -- `0 < eps` is part of the intended range; the bound needs only `h1`
  linarith

/-- The Type-II exponent interval endpoint identity `θ + ν = 1/6 - ε`. -/
theorem shrunk_theta_add_nu (eps : ℚ) :
    (shrinkParams eps).2.1 + (shrinkParams eps).2.2 = 1 / 6 - eps := by
  simp only [shrinkParams_theta, shrinkParams_nu]
  ring

/-- For small positive `ε` the shrunk triple is again a legitimate parameter triple.
(The Type-II exponent interval is then `[ε, 1/6 - ε]`.) -/
def shrunkParams (eps : ℚ) (h0 : 0 < eps) (h1 : eps < 1 / 12) : FMParams where
  gamma := (shrinkParams eps).1
  theta := (shrinkParams eps).2.1
  nu := (shrinkParams eps).2.2
  gamma_pos := by simp only [shrinkParams_gamma]; linarith
  gamma_lt_one := by simp only [shrinkParams_gamma]; linarith
  theta_nonneg := by simp only [shrinkParams_theta]; linarith
  theta_lt_half := by simp only [shrinkParams_theta]; linarith
  nu_pos := by simp only [shrinkParams_nu]; linarith
  nu_le := by simp only [shrinkParams_nu, shrinkParams_theta]; linarith

/-- The Type-II exponent interval attached to the shrunk triple. -/
def typeIIInterval (eps : ℚ) : ℚ × ℚ := (eps, 1 / 6 - eps)

theorem typeIIInterval_eq (eps : ℚ) :
    typeIIInterval eps =
      ((shrinkParams eps).2.1, (shrinkParams eps).2.1 + (shrinkParams eps).2.2) := by
  simp only [typeIIInterval, shrinkParams_theta, shrinkParams_nu, Prod.mk.injEq]
  exact ⟨trivial, by ring⟩

end NANC.V4
