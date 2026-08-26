/-
NANC V4 — exact width / range ledger.

ARITHMETIC ONLY.  Every statement here is an exact rational identity or
inequality, plus one *conditional* application of the (uninhabited) external
Ford–Maynard positivity interface.

PERMANENT FIREWALL:
    WIDTH ARITHMETIC  ≠  FORD–MAYNARD THEOREM APPLICATION
-/
import Mathlib
import RequestProject.NANC.V4.Parameters
import RequestProject.NANC.V4.EndgameInterfaces

namespace NANC.V4

/-! ### Exact rational ledger -/

theorem ledger_gamma0 : gamma0 = 1 / 2 := rfl
theorem ledger_theta0 : theta0 = 0 := rfl
theorem ledger_nu0 : nu0 = 1 / 6 := rfl
theorem ledger_fmThreshold : fmThreshold = 1663 / 10000 := rfl

theorem ledger_margin : nu0 - fmThreshold = 11 / 30000 := one_sixth_threshold_margin

theorem ledger_gamma_eps (eps : ℚ) : (shrinkParams eps).1 = 1 / 2 - eps := rfl
theorem ledger_theta_eps (eps : ℚ) : (shrinkParams eps).2.1 = eps := rfl
theorem ledger_nu_eps (eps : ℚ) : (shrinkParams eps).2.2 = 1 / 6 - 2 * eps := rfl

theorem ledger_theta_add_nu (eps : ℚ) :
    (shrinkParams eps).2.1 + (shrinkParams eps).2.2 = 1 / 6 - eps :=
  shrunk_theta_add_nu eps

theorem ledger_eps_range {eps : ℚ} (h0 : 0 < eps) (h1 : eps < 11 / 60000) :
    fmThreshold < (shrinkParams eps).2.2 :=
  shrunk_nu_gt_threshold_of_eps_small h0 h1

/-! ### Conditional width certificate -/

/-- The central-width positivity conclusion `C⁻(1/2, 0, 1/6) > 0`, for a supplied
sieve coefficient. -/
def CentralWidthOneSixthPositive (Cminus : SieveCoefficient) : Prop :=
  0 < Cminus gamma0 theta0 nu0

/-- **Conditional width certificate.**  Applying the *external, uninhabited*
Ford–Maynard positivity interface to the Lean-proved rational inequality
`1/6 > 1663/10000` yields central-width positivity at `ν = 1/6`.

This theorem is `conditionalTheorem` status: it says nothing about whether
`FMPositiveCentralWidth` actually holds. -/
theorem fm_central_width_one_sixth_conditional {Cminus : SieveCoefficient}
    (h : FMPositiveCentralWidth Cminus gamma0 theta0) :
    CentralWidthOneSixthPositive Cminus :=
  h nu0 one_sixth_gt_fm_threshold (by norm_num [nu0, theta0])

/-- The same conditional certificate along the `ε`-shrunk family. -/
theorem fm_shrunk_width_conditional {Cminus : SieveCoefficient} {eps : ℚ}
    (h : FMPositiveCentralWidth Cminus (shrinkParams eps).1 (shrinkParams eps).2.1)
    (h0 : 0 < eps) (h1 : eps < 11 / 60000) :
    0 < Cminus (shrinkParams eps).1 (shrinkParams eps).2.1 (shrinkParams eps).2.2 := by
  refine h _ (ledger_eps_range h0 h1) ?_
  simp only [ledger_nu_eps, ledger_theta_eps]
  linarith

end NANC.V4
