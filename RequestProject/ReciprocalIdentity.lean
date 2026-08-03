import Mathlib

/-!
# Modular reciprocity core (§9)

`PRIMITIVE_RECIPROCITY_SPLIT`.  Writing `e(x) = exp(2πix)`, and using explicit
inverse witnesses `x = overline{A} (mod C)`, `y = overline{C} (mod A)`, we have
for coprime `A, C` and any integer `j`:

`e(2j·overline{A}/C) = e(−2j·overline{C}/A) · e(2j/(AC))`.

Status of the modular reciprocity: `LEAN_PROVED`.

`PRIMITIVE_ARCHIMEDEAN_PHASE_SMALL`.  The final archimedean phase
`2/(q₁a₁·m₁q₂a₂)` is `O(X^{−1+ε})` at the balanced scales.  We record the exact
scaling lemma (if the total modulus exceeds `X^{1−ε}` then the phase argument is
`≤ 2·X^{−1+ε}`); the assertion that the resulting global error is negligible is
`CONDITIONAL_INTERFACE` (it depends on the exact total coefficient mass).
-/

namespace Banking.ReciprocalIdentity

open Complex

/-- Additive character `e(x) = exp(2πix)`. -/
noncomputable def e (x : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * x)

@[simp] lemma e_add (x y : ℝ) : e (x + y) = e x * e y := by
  unfold e; rw [← Complex.exp_add]; push_cast; ring_nf

@[simp] lemma e_int (k : ℤ) : e (k : ℝ) = 1 := by
  unfold e
  rw [show (2 * (Real.pi : ℂ) * Complex.I * (k : ℝ))
        = (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by push_cast; ring]
  exact Complex.exp_int_mul_two_pi_mul_I k

lemma e_add_int (x : ℝ) (k : ℤ) : e (x + (k : ℝ)) = e x := by
  rw [e_add, e_int, mul_one]

/-- `PRIMITIVE_RECIPROCITY_SPLIT` (§9).

For coprime nonzero integers `A, C`, inverse witnesses `x` (of `A` mod `C`) and
`y` (of `C` mod `A`), and any integer `j`,
`e(2jx/C) = e(−2jy/A) · e(2j/(AC))`.

Status: `LEAN_PROVED`. -/
theorem primitive_reciprocity_split
    (A C j x y : ℤ) (hA : A ≠ 0) (hC : C ≠ 0) (hAC : IsCoprime A C)
    (hx : A * x ≡ 1 [ZMOD C]) (hy : C * y ≡ 1 [ZMOD A]) :
    e ((2 * j * x : ℝ) / C)
      = e ((-(2 * j * y) : ℝ) / A) * e ((2 * j : ℝ) / (A * C)) := by
  rw [← e_add]
  have hCd : C ∣ (A * x + C * y - 1) := by
    obtain ⟨s, hs⟩ := Int.modEq_iff_dvd.mp hx.symm
    exact ⟨s + y, by linarith [hs]⟩
  have hAd : A ∣ (A * x + C * y - 1) := by
    obtain ⟨s, hs⟩ := Int.modEq_iff_dvd.mp hy.symm
    exact ⟨x + s, by linarith [hs]⟩
  obtain ⟨t, ht⟩ := hAC.mul_dvd hAd hCd
  have key : (2 * j * x : ℝ) / C
      = ((-(2 * j * y) : ℝ) / A + (2 * j : ℝ) / (A * C)) + ((2 * j * t : ℤ) : ℝ) := by
    have hAR : (A : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hA
    have hCR : (C : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hC
    have htR : (A : ℝ) * (x : ℝ) + (C : ℝ) * (y : ℝ) - 1
        = (A : ℝ) * (C : ℝ) * (t : ℝ) := by
      exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) ht
    push_cast; field_simp; linear_combination (j : ℝ) * htR
  rw [key, e_add_int]

/-- `PRIMITIVE_ARCHIMEDEAN_PHASE_SMALL` (§9), scaling core.

If the total modulus `D = q₁a₁·m₁q₂a₂` is at least `X^{1−ε}` and `D > 0`, then
the archimedean phase argument `2/D` is at most `2·X^{−1+ε}`.

Status of this exponent lemma: `LEAN_PROVED_CORE`.  (The negligibility of the
resulting global Taylor error is `CONDITIONAL_INTERFACE`.) -/
theorem primitive_archimedean_phase_small
    (X ε D : ℝ) (hX : 1 ≤ X) (hDlow : X ^ (1 - ε) ≤ D) :
    2 / D ≤ 2 * X ^ (-1 + ε) := by
  have hX0 : (0 : ℝ) < X := lt_of_lt_of_le one_pos hX
  have hpos : (0 : ℝ) < X ^ (1 - ε) := Real.rpow_pos_of_pos hX0 _
  have hle : 2 / D ≤ 2 / X ^ (1 - ε) :=
    div_le_div_of_nonneg_left (by norm_num) hpos hDlow
  have hrw : 2 / X ^ (1 - ε) = 2 * X ^ (-1 + ε) := by
    rw [div_eq_mul_inv, ← Real.rpow_neg (le_of_lt hX0),
      show (-(1 - ε)) = (-1 + ε) by ring]
  rw [hrw] at hle; exact hle

end Banking.ReciprocalIdentity
