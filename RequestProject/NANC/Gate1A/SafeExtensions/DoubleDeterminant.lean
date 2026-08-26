/-
# NANC Gate 1A v9 — the first double determinant

With

    N     = h1*q2 − h2*q1,
    Delta = ell1*h1 − ell2*h2,
    C     = ell1*q1 − ell2*q2,

the two exact identities

    h1*C + ell2*N = q1*Delta,
    h2*C + ell1*N = q2*Delta

hold identically over ℤ, and give cross-multiplied uniqueness of `(q1,q2)` once
`Delta ≠ 0` and the values `C, N` are frozen.  No rationals are used.
-/
import Mathlib

namespace TwinPrimeProject.NANC.Gate1A.V9

/-- `N = h1*q2 − h2*q1`. -/
def detN (h1 h2 q1 q2 : ℤ) : ℤ := h1 * q2 - h2 * q1

/-- `Delta = ell1*h1 − ell2*h2`. -/
def detDelta (ell1 ell2 h1 h2 : ℤ) : ℤ := ell1 * h1 - ell2 * h2

/-- `C = ell1*q1 − ell2*q2`. -/
def detC (ell1 ell2 q1 q2 : ℤ) : ℤ := ell1 * q1 - ell2 * q2

/-- **Left double determinant.** -/
theorem doubleDet_left (ell1 ell2 h1 h2 q1 q2 : ℤ) :
    h1 * detC ell1 ell2 q1 q2 + ell2 * detN h1 h2 q1 q2
      = q1 * detDelta ell1 ell2 h1 h2 := by
  unfold detC detN detDelta; ring

/-- **Right double determinant.** -/
theorem doubleDet_right (ell1 ell2 h1 h2 q1 q2 : ℤ) :
    h2 * detC ell1 ell2 q1 q2 + ell1 * detN h1 h2 q1 q2
      = q2 * detDelta ell1 ell2 h1 h2 := by
  unfold detC detN detDelta; ring

/-- **Cross-multiplied uniqueness of `q1`.**  If `Delta ≠ 0` and two conductor
pairs produce the same `C` and the same `N`, their first components agree. -/
theorem doubleDet_q1_unique {ell1 ell2 h1 h2 q1 q2 q1' q2' : ℤ}
    (hDelta : detDelta ell1 ell2 h1 h2 ≠ 0)
    (hC : detC ell1 ell2 q1 q2 = detC ell1 ell2 q1' q2')
    (hN : detN h1 h2 q1 q2 = detN h1 h2 q1' q2') :
    q1 = q1' := by
  have e1 := doubleDet_left ell1 ell2 h1 h2 q1 q2
  have e2 := doubleDet_left ell1 ell2 h1 h2 q1' q2'
  have : q1 * detDelta ell1 ell2 h1 h2 = q1' * detDelta ell1 ell2 h1 h2 := by
    rw [← e1, ← e2, hC, hN]
  exact mul_right_cancel₀ hDelta this

/-- **Cross-multiplied uniqueness of `q2`.** -/
theorem doubleDet_q2_unique {ell1 ell2 h1 h2 q1 q2 q1' q2' : ℤ}
    (hDelta : detDelta ell1 ell2 h1 h2 ≠ 0)
    (hC : detC ell1 ell2 q1 q2 = detC ell1 ell2 q1' q2')
    (hN : detN h1 h2 q1 q2 = detN h1 h2 q1' q2') :
    q2 = q2' := by
  have e1 := doubleDet_right ell1 ell2 h1 h2 q1 q2
  have e2 := doubleDet_right ell1 ell2 h1 h2 q1' q2'
  have : q2 * detDelta ell1 ell2 h1 h2 = q2' * detDelta ell1 ell2 h1 h2 := by
    rw [← e1, ← e2, hC, hN]
  exact mul_right_cancel₀ hDelta this

/-- The two uniqueness statements together. -/
theorem doubleDet_conductorPair_unique {ell1 ell2 h1 h2 q1 q2 q1' q2' : ℤ}
    (hDelta : detDelta ell1 ell2 h1 h2 ≠ 0)
    (hC : detC ell1 ell2 q1 q2 = detC ell1 ell2 q1' q2')
    (hN : detN h1 h2 q1 q2 = detN h1 h2 q1' q2') :
    q1 = q1' ∧ q2 = q2' :=
  ⟨doubleDet_q1_unique hDelta hC hN, doubleDet_q2_unique hDelta hC hN⟩

end TwinPrimeProject.NANC.Gate1A.V9
