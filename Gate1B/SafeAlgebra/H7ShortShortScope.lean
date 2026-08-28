/-
# Gate 1B v8.5 — H7 short-short scope lock

**Status: PROVED_ALGEBRAIC / CAPACITY_ONLY (rational exponent arithmetic).**

Scales are recorded by their exponents relative to `X`, with

    Y = X^(1/9).

The authoritative *short-short* source inequalities are

    u < alpha,  u < beta,
    alpha < 4/9,  beta < 4/9,
    13/18 <= omega,  omega = alpha + beta,  omega < 8/9.

Everything proved in this file is exponent arithmetic: no asymptotic statement,
no analytic estimate, and in particular **no** claim about the complementary
region `max(alpha, beta) >= 4/9` (see `H7ScopeFirewall.lean`).
-/
import Mathlib

namespace Gate1B.SafeAlgebra

/-- The exponent of `Y = X^(1/9)` relative to `X`. -/
def yExponent : ℚ := 1 / 9

/-- The H7 short-short scope, as the literal source inequality package on the
rational exponents `u`, `alpha`, `beta`, `omega`. -/
structure H7ShortShortScope where
  /-- The small (`u`) exponent. -/
  u : ℚ
  /-- The first short exponent. -/
  alpha : ℚ
  /-- The second short exponent (the prime variable `P = X^beta`). -/
  beta : ℚ
  /-- The total exponent. -/
  omega : ℚ
  u_lt_alpha : u < alpha
  u_lt_beta : u < beta
  alpha_lt : alpha < 4 / 9
  beta_lt : beta < 4 / 9
  omega_ge : 13 / 18 ≤ omega
  omega_eq : omega = alpha + beta
  omega_lt : omega < 8 / 9

namespace H7ShortShortScope

variable (S : H7ShortShortScope)

/-- **Scope lock, `beta` side.**  In the short-short region `beta < 4/9`. -/
theorem h7_beta_lt_four_ninths : S.beta < 4 / 9 := S.beta_lt

/-- **Scope lock, `alpha` side.** -/
theorem h7_alpha_lt_four_ninths : S.alpha < 4 / 9 := S.alpha_lt

/-- The prime exponent (the exponent of `P`) is `beta`, hence `< 4/9`. -/
theorem h7_primeExponent_lt_four_ninths : S.beta < 4 / 9 := S.beta_lt

/-- In the `Y`-scale (`Y = X^(1/9)`), `beta < 4/9` says exactly that the exponent
of `P` in `Y` is `< 4`: this is the capacity form `P < Y^4`. -/
theorem h7_P_lt_Y4_capacity : S.beta / yExponent < 4 := by
  have h := S.beta_lt
  unfold yExponent
  rw [div_lt_iff₀ (by norm_num : (0:ℚ) < 1 / 9)]
  linarith

/-- The same statement written multiplicatively: `9 * beta < 4`. -/
theorem h7_nine_beta_lt_four : 9 * S.beta < 4 := by
  have h := S.beta_lt; linarith

/-- Both short exponents are strictly positive as soon as `0 ≤ u`. -/
theorem h7_beta_pos (hu : 0 ≤ S.u) : 0 < S.beta := lt_of_le_of_lt hu S.u_lt_beta

/-- The total exponent is genuinely in the recorded band. -/
theorem h7_omega_band : 13 / 18 ≤ S.alpha + S.beta ∧ S.alpha + S.beta < 8 / 9 := by
  refine ⟨?_, ?_⟩
  · rw [← S.omega_eq]; exact S.omega_ge
  · rw [← S.omega_eq]; exact S.omega_lt

/-- Consistency: the source band `13/18 ≤ omega` together with `alpha < 4/9`
forces `beta > 13/18 - 4/9 = 5/18`, so the short-short cell is a genuine
two-sided window (nonempty and bounded away from `0`). -/
theorem h7_beta_gt_five_eighteenths : 5 / 18 < S.beta := by
  have h2 := S.alpha_lt
  have h4 : 13 / 18 ≤ S.alpha + S.beta := by rw [← S.omega_eq]; exact S.omega_ge
  linarith

/-- Concrete witness that the scope is nonempty. -/
def sample : H7ShortShortScope where
  u := 1 / 10
  alpha := 5 / 12
  beta := 5 / 12
  omega := 5 / 6
  u_lt_alpha := by norm_num
  u_lt_beta := by norm_num
  alpha_lt := by norm_num
  beta_lt := by norm_num
  omega_ge := by norm_num
  omega_eq := by norm_num
  omega_lt := by norm_num

end H7ShortShortScope

end Gate1B.SafeAlgebra
