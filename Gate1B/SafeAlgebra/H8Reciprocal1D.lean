/-
# Gate 1B v8.3 — H8 one-dimensional reciprocal shell

**Status: PROVED_ALGEBRAIC.**

At defect order eight exactly one model coordinate remains, so the shell is
already one-dimensional with `B₈ = C₈`:

    C₈ * x - q * ℓ = -2,   B₈ x ≡ -2 (mod q).

No analytic theorem is declared: the reciprocal-fraction / conductor-splice
estimate for H8 remains open.
-/
import Mathlib
import Gate1B.SafeAlgebra.HighOrderRegroupGeometry

namespace Gate1B.SafeAlgebra

/-- The H8 coefficient: nothing is absorbed, `B₈ = C₈`. -/
def h8_rf1d_B (C8 : ℤ) : ℤ := C8

/-- **H8 1D reciprocal shell.** -/
theorem h8_rf1d_shell (C8 x q ell : ℤ) :
    C8 * x - q * ell = -2 ↔ h8_rf1d_B C8 * x - q * ell = -2 := Iff.rfl

/-- **H8 1D congruence.** -/
theorem h8_rf1d_congruence (B8 x q : ℤ) :
    (∃ ell : ℤ, B8 * x - q * ell = -2) ↔ B8 * x ≡ -2 [ZMOD q] := by
  constructor
  · rintro ⟨ell, h⟩
    exact (Int.modEq_iff_dvd.2 ⟨-ell, by linarith⟩)
  · intro h
    obtain ⟨k, hk⟩ := Int.modEq_iff_dvd.1 h
    exact ⟨-k, by linarith⟩

/-- Order eight really does leave a single model coordinate, so the
one-dimensional shell is the only regroup available. -/
theorem h8_single_model : remainingModels 8 = 1 := (orderEight_oneModel).1

end Gate1B.SafeAlgebra
