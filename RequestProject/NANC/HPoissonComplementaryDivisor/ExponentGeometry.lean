import Mathlib

/-!
# HPoissonComplementaryDivisor, Module 4: rational exponent bookkeeping

Exact `ℚ` arithmetic.  Every quantity below is an **exponent of `X`**; no
analytic content whatsoever is attached to these identities and inequalities.

The `r = 9`, `4|5` split parameters are

`U = X^(4/9)`, `V = X^(5/9)`, `Q = X^(13/18)`, `H₀ = X`,

i.e. exponents `expU = 4/9`, `expV = 5/9`, `expQ = 13/18`, `expH0 = 1`.

The corrected dyadic complementary-divisor geometry is `L_ℓ = Y V / Q`, so a
dual `y`-block of exponent `γ` produces complementary divisors of exponent
`γ + 5/9 − 13/18 = γ − 1/6`.  The *global* claim `ℓ ∼ X^(5/18)` is **false**
and is explicitly refuted here (`global_ell_exponent_false`); only the top
block `γ = 4/9` has exponent `5/18`.
-/

namespace TwinPrimeProject
namespace HPoissonCD

/-! ## 1. The exponent constants -/

/-- Exponent of `U = X^(4/9)`. -/
def expU : ℚ := 4 / 9

/-- Exponent of `V = X^(5/9)`. -/
def expV : ℚ := 5 / 9

/-- Exponent of `Q = X^(13/18)`. -/
def expQ : ℚ := 13 / 18

/-- Exponent of `H₀ = X`. -/
def expH0 : ℚ := 1

/-! ## 2. Banked exponent identities -/

/-- `U V = X`. -/
theorem expU_add_expV : expU + expV = 1 := by norm_num [expU, expV]

/-- `Q² / U = X`. -/
theorem two_expQ_sub_expU : 2 * expQ - expU = 1 := by norm_num [expQ, expU]

/-- `Q² H₀ V² = X^(32/9)`. -/
theorem two_expQ_add_expH0_add_two_expV : 2 * expQ + expH0 + 2 * expV = 32 / 9 := by
  norm_num [expQ, expH0, expV]

/-- `H₀ U V² = X^(23/9)`. -/
theorem expH0_add_expU_add_two_expV : expH0 + expU + 2 * expV = 23 / 9 := by
  norm_num [expH0, expU, expV]

/-- The two composite exponents differ by exactly `1`. -/
theorem composite_exponent_gap :
    (2 * expQ + expH0 + 2 * expV) - (expH0 + expU + 2 * expV) = 1 := by
  norm_num [expQ, expH0, expU, expV]

/-- `Q / V = X^(1/6)`. -/
theorem expQ_sub_expV : expQ - expV = 1 / 6 := by norm_num [expQ, expV]

/-- `U V / Q = X^(5/18)`. -/
theorem expU_add_expV_sub_expQ : expU + expV - expQ = 5 / 18 := by
  norm_num [expU, expV, expQ]

/-! ## 3. Corrected dyadic complementary-divisor geometry -/

/-- The exponent of the complementary-divisor block `L_ℓ = Y V / Q` attached to
a dual `y`-block of exponent `γ`. -/
def ellExponent (gamma : ℚ) : ℚ := gamma + expV - expQ

/-- `L_ℓ`-exponent `= γ − 1/6`. -/
theorem ellExponent_eq (gamma : ℚ) : ellExponent gamma = gamma - 1 / 6 := by
  simp only [ellExponent, expV, expQ]; ring

/-- **Dyadic range.**  For `1/6 ≤ γ ≤ 4/9` the complementary divisor exponent
lies in `[0, 5/18]`. -/
theorem ellExponent_mem_Icc {gamma : ℚ} (h₁ : 1 / 6 ≤ gamma) (h₂ : gamma ≤ 4 / 9) :
    0 ≤ ellExponent gamma ∧ ellExponent gamma ≤ 5 / 18 := by
  rw [ellExponent_eq]
  constructor <;> linarith

/-- The top block `γ = 4/9` (i.e. `Y = U`) is the unique block with
complementary-divisor exponent `5/18`. -/
theorem ellExponent_top : ellExponent (4 / 9) = 5 / 18 := by
  rw [ellExponent_eq]; norm_num

/-- The bottom block `γ = 1/6` has complementary-divisor exponent `0`. -/
theorem ellExponent_bottom : ellExponent (1 / 6) = 0 := by
  rw [ellExponent_eq]; norm_num

/-- `ellExponent` is injective, so distinct blocks have distinct `ℓ`-scales. -/
theorem ellExponent_injective : Function.Injective ellExponent := by
  intro a b h
  rw [ellExponent_eq, ellExponent_eq] at h
  linarith

/-- **REPAIR (refutation of the global claim).**  It is *false* that every
admissible dual block `γ ∈ [1/6, 4/9]` yields complementary divisors of size
`X^(5/18)`; the exponent varies over the whole interval `[0, 5/18]`. -/
theorem global_ell_exponent_false :
    ¬ (∀ gamma : ℚ, 1 / 6 ≤ gamma → gamma ≤ 4 / 9 → ellExponent gamma = 5 / 18) := by
  intro h
  have := h (1 / 6) (le_refl _) (by norm_num)
  rw [ellExponent_bottom] at this
  norm_num at this

/-- Only the top block attains `5/18`. -/
theorem ellExponent_eq_top_iff {gamma : ℚ} :
    ellExponent gamma = 5 / 18 ↔ gamma = 4 / 9 := by
  rw [ellExponent_eq]
  constructor <;> intro h <;> linarith

/-- The `ℓ`-exponent is strictly below `1/2` on the whole admissible range.
This is **pure exponent arithmetic**: it does *not* license any
Bombieri–Vinogradov type input (see `ConditionalExponentLedger`). -/
theorem ellExponent_lt_half {gamma : ℚ} (h₂ : gamma ≤ 4 / 9) : ellExponent gamma < 1 / 2 := by
  rw [ellExponent_eq]; linarith

end HPoissonCD
end TwinPrimeProject
