/-
# Gate 1B v8.3 — H7 one-dimensional reciprocal shell

**Status: PROVED_ALGEBRAIC.**

Alternative to the two-dimensional H7 route: absorb *both* remaining model
coordinates but one into `B`, i.e. start from

    C₇ * x₁ * x₂ - q * ℓ = -2,

put `B = C₇ * x₂` and read the shell as a one-dimensional (single completion
variable) shell

    B * x₁ - q * ℓ = -2,   B * x₁ ≡ -2 (mod q).

This is the source shell for one-dimensional completion.  Poisson summation and
every analytic reciprocal-fraction estimate remain **open** and are not proved
here.
-/
import Mathlib

namespace Gate1B.SafeAlgebra

/-- The H7 one-dimensional reciprocal coefficient `B = C₇ x₂`. -/
def h7_rf1d_B (C7 x2 : ℤ) : ℤ := C7 * x2

/-- **H7 1D reciprocal shell.** -/
theorem h7_rf1d_shell (C7 x1 x2 q ell : ℤ) :
    C7 * x1 * x2 - q * ell = -2 ↔ h7_rf1d_B C7 x2 * x1 - q * ell = -2 := by
  unfold h7_rf1d_B
  constructor <;> intro h <;> linear_combination h

/-- **H7 1D congruence.**  The shell is solvable in `ℓ` exactly when
`B x₁ ≡ -2 (mod q)`. -/
theorem h7_rf1d_congruence (B x1 q : ℤ) :
    (∃ ell : ℤ, B * x1 - q * ell = -2) ↔ B * x1 ≡ -2 [ZMOD q] := by
  constructor
  · rintro ⟨ell, h⟩
    exact (Int.modEq_iff_dvd.2 ⟨-ell, by linarith⟩)
  · intro h
    obtain ⟨k, hk⟩ := Int.modEq_iff_dvd.1 h
    exact ⟨-k, by linarith⟩

/-- For `q ≠ 0` the one-dimensional completion variable is unique. -/
theorem h7_rf1d_ell_unique (B x1 q : ℤ) (hq : q ≠ 0) (h : q ∣ (B * x1 + 2)) :
    ∃! ell : ℤ, B * x1 - q * ell = -2 := by
  obtain ⟨ell, hell⟩ := h
  refine ⟨ell, by linarith, fun y hy => mul_left_cancel₀ hq (by linarith : q * y = q * ell)⟩

end Gate1B.SafeAlgebra
