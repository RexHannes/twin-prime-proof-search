/-
# NANC Gate 1A v9 — the amplifier affine line, and `Delta(t)`

For coprime `q1, q2` (with `q2 ≠ 0`) and a fixed integer `C`, all integer
solutions of

    q1*ell1 − q2*ell2 = C

are the affine line through one solution `(ell10, ell20)`:

    ell1 = ell10 + q2*t,   ell2 = ell20 + q1*t,     t ∈ ℤ unique.

Along that line the determinant `Delta` is affine:

    Delta(t) = Delta0 + N*t,   N = h1*q2 − h2*q1.

No primality is used beyond coprimality; `q2 ≠ 0` is needed for uniqueness of
`t` and is stated explicitly.
-/
import RequestProject.NANC.Gate1A.SafeExtensions.DoubleDeterminant

namespace TwinPrimeProject.NANC.Gate1A.V9

/-- The amplifier line through `(ell10, ell20)`. -/
def amplifierLine (q1 q2 ell10 ell20 t : ℤ) : ℤ × ℤ := (ell10 + q2 * t, ell20 + q1 * t)

/-- Every point of the line solves the complementary equation. -/
theorem amplifierLine_solves {q1 q2 ell10 ell20 C : ℤ}
    (h0 : q1 * ell10 - q2 * ell20 = C) (t : ℤ) :
    q1 * (amplifierLine q1 q2 ell10 ell20 t).1 - q2 * (amplifierLine q1 q2 ell10 ell20 t).2
      = C := by
  unfold amplifierLine
  simp only
  linarith [h0]

/-- **Parametrization of the complementary solutions.**  For coprime `q1, q2`
with `q2 ≠ 0`, the solution set of `q1*ell1 − q2*ell2 = C` is exactly the affine
line through a given solution, with a unique parameter `t`. -/
theorem complementarySolutions_parametrized {q1 q2 ell10 ell20 C ell1 ell2 : ℤ}
    (hcop : IsCoprime q1 q2) (hq2 : q2 ≠ 0)
    (h0 : q1 * ell10 - q2 * ell20 = C) :
    q1 * ell1 - q2 * ell2 = C ↔ ∃! t : ℤ, ell1 = ell10 + q2 * t ∧ ell2 = ell20 + q1 * t := by
  constructor
  · intro h
    have hkey : q1 * (ell1 - ell10) = q2 * (ell2 - ell20) := by linarith
    have hdvd : q2 ∣ ell1 - ell10 := by
      have : q2 ∣ q1 * (ell1 - ell10) := ⟨ell2 - ell20, hkey⟩
      exact (hcop.symm).dvd_of_dvd_mul_left this
    obtain ⟨t, ht⟩ := hdvd
    refine ⟨t, ⟨by linarith [ht], ?_⟩, ?_⟩
    · have : q2 * (q1 * t) = q2 * (ell2 - ell20) := by
        rw [← hkey, ht]; ring
      have := mul_left_cancel₀ hq2 this
      linarith
    · rintro s ⟨hs1, hs2⟩
      have : q2 * s = q2 * t := by rw [← ht]; linarith [hs1]
      exact mul_left_cancel₀ hq2 this
  · rintro ⟨t, ⟨ht1, ht2⟩, -⟩
    subst ht1; subst ht2
    linarith [h0]

/-- **`Delta` is affine along the amplifier line.** -/
theorem deltaAlongLine_affine (q1 q2 ell10 ell20 h1 h2 t : ℤ) :
    detDelta (ell10 + q2 * t) (ell20 + q1 * t) h1 h2
      = detDelta ell10 ell20 h1 h2 + detN h1 h2 q1 q2 * t := by
  unfold detDelta detN; ring

/-- The primed analogue (identical algebra, primed data). -/
theorem deltaAlongLine_affine' (q1 q2 ell10' ell20' h1' h2 t' : ℤ) :
    detDelta (ell10' + q2 * t') (ell20' + q1 * t') h1' h2
      = detDelta ell10' ell20' h1' h2 + detN h1' h2 q1 q2 * t' := by
  unfold detDelta detN; ring

end TwinPrimeProject.NANC.Gate1A.V9
