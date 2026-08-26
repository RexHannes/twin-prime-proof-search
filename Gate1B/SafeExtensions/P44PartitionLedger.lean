/-
# Gate 1B v8.2 — the P4.4 five-factor partition ledger (finite ℚ certificate)

Five equal `Y`-prime defect coordinates are split as `Q₁ = Y^a`, `Q₂ = Y^b`,
`Q₃ = Y^c` with `a + b + c = 5`.  The zero-epsilon candidate parameter
inequalities for `β : ℚ` are

    β > a/9,
    β < 1/2 − (b+2c)/18,
    β < 1   − (5b+2c)/18,
    β > 5/18   (hard-source lower bound).

This file proves, by explicit finite arithmetic (**no** `native_decide`), that
the hard interior is nonempty exactly for `(a,b,c) = (3,2,0)`, and pins the
resulting interval `1/3 < β < 7/18`.

**FIREWALL.**  This is a finite exponent certificate.  It does **not** claim
that Pascadi Proposition 4.4 applies to the Gate source.
-/
import Mathlib

namespace Gate1B.SafeExtensions

/-- The four zero-epsilon P4.4 conditions on `β` for a partition `(a,b,c)`. -/
def p44Conditions (a b c : ℕ) (beta : ℚ) : Prop :=
  (a : ℚ) / 9 < beta ∧
  beta < 1 / 2 - ((b : ℚ) + 2 * c) / 18 ∧
  beta < 1 - (5 * (b : ℚ) + 2 * c) / 18 ∧
  5 / 18 < beta

/-- The zero-epsilon P4.4 hard interior for a partition `(a,b,c)` of the five
defect coordinates. -/
def p44HardInteriorNonempty (a b c : ℕ) : Prop := ∃ beta : ℚ, p44Conditions a b c beta

/-- **Only the `(3,2,0)` partition has a nonempty hard interior.** -/
theorem p44_only_320_has_hard_interior {a b c : ℕ} (hsum : a + b + c = 5)
    (h : p44HardInteriorNonempty a b c) : a = 3 ∧ b = 2 ∧ c = 0 := by
  obtain ⟨beta, h1, h2, h3, h4⟩ := h
  -- rational consequences
  have k1 : (b : ℚ) + 2 * c < 4 := by linarith
  have k2 : 2 * (a : ℚ) + (b : ℚ) + 2 * c < 9 := by
    have : (a : ℚ) / 9 < 1 / 2 - ((b : ℚ) + 2 * c) / 18 := lt_trans h1 h2
    linarith
  have k3 : 5 * (b : ℚ) + 2 * c < 13 := by linarith
  -- transport to ℕ
  have n1 : b + 2 * c < 4 := by exact_mod_cast (by push_cast at k1 ⊢; linarith : ((b + 2 * c : ℕ) : ℚ) < 4)
  have n2 : 2 * a + b + 2 * c < 9 := by
    exact_mod_cast (by push_cast at k2 ⊢; linarith : ((2 * a + b + 2 * c : ℕ) : ℚ) < 9)
  have n3 : 5 * b + 2 * c < 13 := by
    exact_mod_cast (by push_cast at k3 ⊢; linarith : ((5 * b + 2 * c : ℕ) : ℚ) < 13)
  omega

/-- **The `(3,2,0)` partition really does have a nonempty hard interior**, with
the explicit rational witness `β = 7/20`. -/
theorem p44_320_has_hard_interior : p44HardInteriorNonempty 3 2 0 := by
  refine ⟨7 / 20, ?_, ?_, ?_, ?_⟩ <;> norm_num [p44Conditions]

/-- **The `(3,2,0)` interval is exactly `1/3 < β < 7/18`.** -/
theorem p44_320_upper_eq_seven_eighteenths (beta : ℚ) :
    p44Conditions 3 2 0 beta ↔ (1 / 3 < beta ∧ beta < 7 / 18) := by
  unfold p44Conditions
  push_cast
  constructor
  · rintro ⟨h1, h2, -, -⟩
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩

end Gate1B.SafeExtensions
