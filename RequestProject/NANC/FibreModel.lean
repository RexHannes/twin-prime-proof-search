import Mathlib

/-!
# Route-A fibre frame: the exact integer fibre model

This file formalises the exact (integer) fibre model behind the Route-A edge
frame.  Everything here is an identity between integers; no analytic statement
occurs.

Setting.  Fix `r > 0`, `c` with `gcd c r = 1`, and a root `w0` of
`c * w0 ≡ -2 (mod r)`.  The integer `a0` is the witness of that congruence,
i.e. `c * w0 + 2 = r * a0`.

Along the fibre we put

* `m j = c + j * r`,
* `alpha j = a0 + j * w0`,
* `A j t = alpha j + m j * t`,
* `w t = w0 + r * t`,
* `B j' t = (m j' * w t + 2) / r`.

The results are the affine expansion (F1), (F2), the integrality of the `B`-edge
and the identity `B j j' t = A j' t` (F3).
-/

namespace RouteAFibreFrame

/-- Data of one Route-A fibre: modulus `r`, offset `c`, root `w0` of
`c * w0 ≡ -2 (mod r)`, and the explicit witness `a0` of that congruence.

The coprimality field `coprime` is part of the fibre data as specified; the
affine identities of this file do not use it, but it is what makes the root `w0`
unique modulo `r` and is therefore kept. -/
structure Fibre where
  /-- The fibre modulus. -/
  r : ℤ
  /-- The fibre offset. -/
  c : ℤ
  /-- A root of `c * w ≡ -2 (mod r)`. -/
  w0 : ℤ
  /-- The explicit witness of the congruence `c * w0 ≡ -2 (mod r)`. -/
  a0 : ℤ
  /-- Positivity of the modulus. -/
  r_pos : 0 < r
  /-- Coprimality of the offset and the modulus. -/
  coprime : Int.gcd c r = 1
  /-- The congruence `c * w0 + 2 = r * a0`. -/
  root : c * w0 + 2 = r * a0

namespace Fibre

variable (F : Fibre)

/-- The fibre point `m_j = c + j r`. -/
def m (j : ℤ) : ℤ := F.c + j * F.r

/-- The affine sequence `α_j = a0 + j w0`. -/
def alpha (j : ℤ) : ℤ := F.a0 + j * F.w0

/-- The shifted root `w_t = w0 + r t`. -/
def w (t : ℤ) : ℤ := F.w0 + F.r * t

/-- The row entry `A_j(t) = α_j + m_j t`. -/
def A (j t : ℤ) : ℤ := F.alpha j + F.m j * t

/-- The `B`-edge value `B_{j,j'}(t) = (m_{j'} w_t + 2) / r`. -/
def B (j' t : ℤ) : ℤ := (F.m j' * F.w t + 2) / F.r

/-- Definition unfolding for the fibre points. -/
theorem fibre_m_def (j : ℤ) : F.m j = F.c + j * F.r := rfl

/-- The sequence `α` is affine in `j`. -/
theorem fibre_alpha_affine (j : ℤ) : F.alpha j = F.a0 + j * F.w0 := rfl

/-- **(F1)** `A_j(t) = a0 + c t + j (w0 + r t)`. -/
theorem fibre_A_expansion (j t : ℤ) :
    F.A j t = F.a0 + F.c * t + j * (F.w0 + F.r * t) := by
  simp only [A, alpha, m]; ring

/-- **(F2)** `A_j(t) = a0 + c t + j w_t`. -/
theorem fibre_A_eq_shifted_root (j t : ℤ) :
    F.A j t = F.a0 + F.c * t + j * F.w t := by
  simp only [A, alpha, m, w]; ring

/-- The exact numerator identity `m_{j'} w_t + 2 = r * A_{j'}(t)`. -/
theorem fibre_B_numerator (j' t : ℤ) :
    F.m j' * F.w t + 2 = F.r * F.A j' t := by
  simp only [A, alpha, m, w]
  linear_combination F.root

/-- **Integrality of the `B`-edge**: `r` divides `m_{j'} w_t + 2`. -/
theorem fibre_B_integral (j' t : ℤ) : F.r ∣ F.m j' * F.w t + 2 :=
  ⟨F.A j' t, F.fibre_B_numerator j' t⟩

/-- **(F3)** The `B`-edge of the pair `(j, j')` equals `A_{j'}`. -/
theorem fibre_B_eq_A_jprime (j' t : ℤ) : F.B j' t = F.A j' t := by
  rw [B, F.fibre_B_numerator j' t]
  exact Int.mul_ediv_cancel_left _ (ne_of_gt F.r_pos)

end Fibre

/-- The fibre hypotheses are consistent: an explicit fibre with `r = 3`, `c = 1`,
`w0 = 1`, `a0 = 1`. -/
def exampleFibre : Fibre where
  r := 3
  c := 1
  w0 := 1
  a0 := 1
  r_pos := by norm_num
  coprime := by decide
  root := by norm_num

end RouteAFibreFrame
