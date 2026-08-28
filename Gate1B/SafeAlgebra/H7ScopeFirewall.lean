/-
# Gate 1B v8.5 — H7 scope firewall: the high-prime residual is *outside* short-short

**Status: PROVED_ALGEBRAIC (exponent arithmetic) / PROVED_FINITE (status record).**

`P = X^beta` and `Y = X^(1/9)`, so

    P ≥ Y^(9/2)   ⟺   beta ≥ 1/2.

Since the H7 short-short scope forces `beta < 4/9 < 1/2`, the high-prime residual
`P ≥ Y^(9/2)` is *disjoint* from H7 short-short.  This is a permanent firewall:
nothing proved about the short-short cell may be transported to the high-prime
complement, and the complement is **not** asserted to be analytically closed
anywhere in this bank.
-/
import Mathlib
import Gate1B.SafeAlgebra.H7ShortShortScope

namespace Gate1B.SafeAlgebra

/-- `P ≥ Y^(9/2)` in exponent form (`Y = X^(1/9)`): `beta ≥ (9/2)·(1/9) = 1/2`. -/
def HighPrimeExponent (beta : ℚ) : Prop := 1 / 2 ≤ beta

/-- The exponent translation `P ≥ Y^(9/2) ⟺ beta ≥ 1/2`. -/
theorem highPrime_iff (beta : ℚ) : HighPrimeExponent beta ↔ (9 / 2) * yExponent ≤ beta := by
  unfold HighPrimeExponent yExponent
  constructor <;> intro h <;> linarith

/-- **Incompatibility.**  `beta < 4/9` and `beta ≥ 1/2` cannot both hold. -/
theorem beta_lt_four_ninths_not_high {beta : ℚ} (h : beta < 4 / 9) :
    ¬ HighPrimeExponent beta := by
  unfold HighPrimeExponent; intro hh; linarith

/-- **The high-prime residual is not in H7 short-short.** -/
theorem highPrime_not_in_h7ShortShort (S : H7ShortShortScope) :
    ¬ HighPrimeExponent S.beta :=
  beta_lt_four_ninths_not_high S.beta_lt

/-- No H7 short-short scope has a high-prime exponent: the two regions are
disjoint as subsets of the `beta`-line. -/
theorem h7HighPrimeResidual_scope_disjoint :
    ∀ beta : ℚ, ¬ (beta < 4 / 9 ∧ HighPrimeExponent beta) := by
  intro beta ⟨h1, h2⟩
  exact beta_lt_four_ninths_not_high h1 h2

/-- Quantitative gap: in the short-short cell `beta` misses the high-prime
threshold by at least `1/2 - 4/9 = 1/18`. -/
theorem h7_gap_to_highPrime (S : H7ShortShortScope) : S.beta + 1 / 18 < 1 / 2 := by
  have := S.beta_lt; linarith

/-! ## Finite status record -/

/-- The two *separate* routing nodes of the H7 prime-variable analysis. -/
inductive H7Region
  /-- `alpha, beta < 4/9`: the short-short cell treated by the v8.5 compiler. -/
  | H7ShortShort
  /-- `max(alpha, beta) ≥ 4/9`, in particular the high-prime residual
  `P ≥ Y^(9/2)`: a *separate open* node. -/
  | HighPrimeComplement
  deriving DecidableEq, Repr

/-- The two nodes are distinct: no theorem about one is a theorem about the
other by definitional unfolding. -/
theorem H7Region_distinct : H7Region.H7ShortShort ≠ H7Region.HighPrimeComplement := by
  decide

/-- Membership test on exponents.  `HighPrimeComplement` is only *named*; no
analytic closure is attached to it anywhere in this bank. -/
def regionOf (beta : ℚ) : H7Region :=
  if beta < 4 / 9 then H7Region.H7ShortShort else H7Region.HighPrimeComplement

/-- A short-short scope always lands in the short-short node. -/
theorem regionOf_scope (S : H7ShortShortScope) : regionOf S.beta = H7Region.H7ShortShort := by
  unfold regionOf; rw [if_pos S.beta_lt]

/-- A high-prime exponent always lands in the complement node. -/
theorem regionOf_highPrime {beta : ℚ} (h : HighPrimeExponent beta) :
    regionOf beta = H7Region.HighPrimeComplement := by
  unfold regionOf
  rw [if_neg]
  unfold HighPrimeExponent at h
  intro hlt; linarith

end Gate1B.SafeAlgebra
