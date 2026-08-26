/-
# Gate 1B v8.3 — H6 exact regroup

**Status: PROVED_ALGEBRAIC.**

The order-six shell has three model coordinates,

    C₆ * x₁ * x₂ * x₃ - q * ℓ = -2.

Absorbing `x₂` into the coefficient, `B₆ = C₆ * x₂`, gives the exact two-model
shell `B₆ * x₁ * x₃ - q * ℓ = -2`, its congruence form, and (for `q > 0`)
uniqueness of the completion variable `ℓ`.

The two-dimensional Poisson/completion analytic step is **not** performed here.
-/
import Mathlib

namespace Gate1B.SafeAlgebra

/-- The absorbed H6 coefficient. -/
def h6_defineB (C6 x2 : ℤ) : ℤ := C6 * x2

/-- **H6 exact regroup.** -/
theorem h6_shell_regroup (C6 x1 x2 x3 q ell : ℤ) :
    C6 * x1 * x2 * x3 - q * ell = -2 ↔ h6_defineB C6 x2 * x1 * x3 - q * ell = -2 := by
  unfold h6_defineB
  constructor <;> intro h <;> linear_combination h

/-- **H6 congruence form.**  Solvability of the shell in `ℓ` is exactly the
divisibility `q ∣ B₆ x₁ x₃ + 2`, equivalently the congruence
`B₆ x₁ x₃ ≡ -2 [ZMOD q]`. -/
theorem h6_congruence (B6 x1 x3 q : ℤ) :
    (∃ ell : ℤ, B6 * x1 * x3 - q * ell = -2) ↔ q ∣ (B6 * x1 * x3 + 2) := by
  constructor
  · rintro ⟨ell, h⟩
    exact ⟨ell, by linarith⟩
  · rintro ⟨ell, h⟩
    exact ⟨ell, by linarith⟩

/-- The congruence statement in `Int.ModEq` form. -/
theorem h6_congruence_modEq (B6 x1 x3 q : ℤ) :
    q ∣ (B6 * x1 * x3 + 2) ↔ B6 * x1 * x3 ≡ -2 [ZMOD q] := by
  rw [Int.modEq_iff_dvd]
  constructor
  · intro h
    have := dvd_neg.mpr h
    simpa [neg_add, sub_eq_neg_add, add_comm] using this
  · intro h
    have := dvd_neg.mpr h
    simpa [neg_sub, sub_eq_neg_add, add_comm] using this

/-- **Uniqueness of the completion variable.**  For `q ≠ 0` the shell determines
`ℓ` uniquely. -/
theorem h6_ell_unique (B6 x1 x3 q : ℤ) (hq : q ≠ 0) (h : q ∣ (B6 * x1 * x3 + 2)) :
    ∃! ell : ℤ, B6 * x1 * x3 - q * ell = -2 := by
  obtain ⟨ell, hell⟩ := h
  refine ⟨ell, by linarith, ?_⟩
  intro y hy
  have : q * y = q * ell := by linarith
  exact mul_left_cancel₀ hq this

/-- The unique completion variable is the quotient `(B₆ x₁ x₃ + 2)/q`. -/
theorem h6_ell_value (B6 x1 x3 q ell : ℤ) (hq : q ≠ 0)
    (h : B6 * x1 * x3 - q * ell = -2) : ell = (B6 * x1 * x3 + 2) / q := by
  have hq' : q * ell = B6 * x1 * x3 + 2 := by linarith
  rw [← hq']
  exact (Int.mul_ediv_cancel_left ell hq).symm

end Gate1B.SafeAlgebra
