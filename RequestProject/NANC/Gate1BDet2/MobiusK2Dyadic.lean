import Mathlib

/-!
# Gate 1B / determinant-2 bank, Module 16: the finite-depth dyadic Möbius identity

Source-independent, square-root-free formulation.  Fix natural numbers `y`, `D`
with

  `y < D`,   `y² ≥ 2D`,

and consider a dyadic modulus `d` with `D < d ≤ 2D`.  Let

  `μ_{≤y}(n) = μ(n)` for `n ≤ y`, and `0` for `n > y`

be the truncated Möbius function (`muLe` below).

## The general identity

With `A_y = μ_{≤y} * ζ` and `h_y = ε − A_y` (`ε = 1` is the Dirichlet identity),
one has, as an identity of arithmetic functions,

  `h_y * h_y * μ = μ − (μ_{≤y} + μ_{≤y}) + μ_{≤y} * μ_{≤y} * ζ`.

## The dyadic evaluation

For `D < d ≤ 2D` the left-hand side vanishes (any nonzero term would need two
factors `> y`, hence a product `> y² ≥ 2D ≥ d`), and `μ_{≤y}(d) = 0` because
`d > D > y`.  Therefore

  `μ(d) = − (μ_{≤y} * μ_{≤y} * ζ)(d)`.

## Correction to the stated identity

The requested boxed form was `μ(d) = (μ_{≤y} * μ_{≤y} * 1)(d)`, i.e. without the
sign.  That form is **false**: the derivation `h_y^{*2} * μ = μ − 2 μ_{≤y} +
μ_{≤y}^{*2} * 1` gives, after killing the first and second terms,
`0 = μ(d) + (μ_{≤y}^{*2} * 1)(d)`.  Concretely with `y = 5`, `D = 6`, `d = 7` one
has `(μ_{≤5} * μ_{≤5} * ζ)(7) = 1` while `μ(7) = −1`.  The unsigned version is
refuted in `unsigned_dyadic_identity_false`; the signed version is proved.

An explicit finite divisor-sum form is also banked
(`moebius_dyadic_divisor_sum`), so the statement does not depend on the
arithmetic-function abstraction.
-/

namespace TwinPrimeProject
namespace Gate1BDet2
namespace MobiusK2

open ArithmeticFunction Finset

/-! ## 1. The truncated Möbius function -/

/-- The truncated Möbius function `μ_{≤y}`. -/
def muLe (y : ℕ) : ArithmeticFunction ℤ :=
  ⟨fun n => if n ≤ y then (moebius n : ℤ) else 0, by simp⟩

@[simp] theorem muLe_apply (y n : ℕ) :
    muLe y n = if n ≤ y then (moebius n : ℤ) else 0 := rfl

theorem muLe_eq_zero_of_gt {y n : ℕ} (h : y < n) : muLe y n = 0 := by
  simp [muLe_apply, Nat.not_le.mpr h]

theorem muLe_eq_moebius_of_le {y n : ℕ} (h : n ≤ y) : muLe y n = moebius n := by
  simp [muLe_apply, h]

/-- `A_y = μ_{≤y} * ζ`. -/
def Ay (y : ℕ) : ArithmeticFunction ℤ := muLe y * (zeta : ArithmeticFunction ℤ)

/-- `h_y = ε − A_y`, where `ε = 1` is the Dirichlet identity. -/
def hy (y : ℕ) : ArithmeticFunction ℤ := 1 - Ay y

/-! ## 2. `h_y` is supported on `n > y` -/

/-- The complete divisor sum of `μ` is the Dirichlet identity. -/
theorem sum_divisors_moebius (n : ℕ) :
    ∑ i ∈ n.divisors, (moebius i : ℤ) = if n = 1 then 1 else 0 := by
  have h : (moebius * (zeta : ArithmeticFunction ℤ)) n = (1 : ArithmeticFunction ℤ) n := by
    rw [moebius_mul_coe_zeta]
  rwa [coe_mul_zeta_apply, one_apply] at h

/-- **`h_y` vanishes on `n ≤ y`.**  For such `n` the truncation is invisible in
the divisor sum, so `A_y(n) = ε(n)`. -/
theorem hy_apply_eq_zero_of_le {y n : ℕ} (h : n ≤ y) : hy y n = 0 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [hy, Ay]
  · have hsum : (Ay y) n = if n = 1 then 1 else 0 := by
      rw [Ay, coe_mul_zeta_apply, ← sum_divisors_moebius n]
      refine Finset.sum_congr rfl ?_
      intro i hi
      have hdvd : i ∣ n := (Nat.mem_divisors.mp hi).1
      have : i ≤ n := Nat.le_of_dvd hn hdvd
      exact muLe_eq_moebius_of_le (le_trans this h)
    have hsub : hy y n = (1 : ArithmeticFunction ℤ) n - Ay y n := rfl
    rw [hsub, hsum, one_apply]
    simp

/-! ## 3. The general convolution identity -/

/-- **The exact arithmetic-function identity.**
`h_y * h_y * μ = μ − (μ_{≤y} + μ_{≤y}) + μ_{≤y} * μ_{≤y} * ζ`. -/
theorem hy_sq_mul_moebius (y : ℕ) :
    hy y * hy y * moebius
      = moebius - (muLe y + muLe y) + muLe y * muLe y * (zeta : ArithmeticFunction ℤ) := by
  have hzm : (zeta : ArithmeticFunction ℤ) * moebius = 1 := coe_zeta_mul_moebius
  have expand :
      hy y * hy y * moebius
        = moebius - (muLe y * ((zeta : ArithmeticFunction ℤ) * moebius)
            + muLe y * ((zeta : ArithmeticFunction ℤ) * moebius))
          + muLe y * muLe y * (zeta : ArithmeticFunction ℤ)
              * ((zeta : ArithmeticFunction ℤ) * moebius) := by
    simp only [hy, Ay]
    ring
  rw [expand, hzm]
  ring

/-! ## 4. The dyadic vanishing -/

/-- `h_y * h_y` vanishes at every `a` with `1 ≤ a ≤ y²`: a nonzero term would
require both factors to exceed `y`. -/
theorem hy_sq_apply_eq_zero {y a : ℕ} (ha : a ≤ y ^ 2) : (hy y * hy y) a = 0 := by
  rw [mul_apply]
  refine Finset.sum_eq_zero ?_
  rintro ⟨a₁, a₂⟩ hp
  have hmem := Nat.mem_divisorsAntidiagonal.mp hp
  have hprod : a₁ * a₂ = a := hmem.1
  by_cases h₁ : a₁ ≤ y
  · simp [hy_apply_eq_zero_of_le h₁]
  · by_cases h₂ : a₂ ≤ y
    · simp [hy_apply_eq_zero_of_le h₂]
    · exfalso
      have hy₁ : y + 1 ≤ a₁ := Nat.lt_of_not_le h₁
      have hy₂ : y + 1 ≤ a₂ := Nat.lt_of_not_le h₂
      have : (y + 1) * (y + 1) ≤ a₁ * a₂ := Nat.mul_le_mul hy₁ hy₂
      have h2 : y ^ 2 < (y + 1) * (y + 1) := by ring_nf; omega
      omega

/-- Consequently `h_y * h_y * μ` vanishes at every `d ≤ y²`. -/
theorem hy_sq_mul_moebius_apply_eq_zero {y d : ℕ} (hd : d ≤ y ^ 2) :
    (hy y * hy y * moebius) d = 0 := by
  rw [mul_apply]
  refine Finset.sum_eq_zero ?_
  rintro ⟨a, c⟩ hp
  have hmem := Nat.mem_divisorsAntidiagonal.mp hp
  have hprod : a * c = d := hmem.1
  have hd0 : d ≠ 0 := hmem.2
  have hale : a ≤ d := Nat.le_of_dvd (Nat.pos_of_ne_zero hd0) ⟨c, hprod.symm⟩
  simp [hy_sq_apply_eq_zero (le_trans hale hd)]

/-! ## 5. The dyadic identity -/

/-- **The exact finite-depth dyadic Möbius identity.**  For `y < D`,
`2D ≤ y²` and `D < d ≤ 2D`,

  `μ(d) = − (μ_{≤y} * μ_{≤y} * ζ)(d)`. -/
theorem moebius_dyadic_truncated {y D d : ℕ}
    (hyD : y < D) (hy2 : 2 * D ≤ y ^ 2) (hd1 : D < d) (hd2 : d ≤ 2 * D) :
    (moebius d : ℤ) = -((muLe y * muLe y * (zeta : ArithmeticFunction ℤ)) d) := by
  have hzero : (hy y * hy y * moebius) d = 0 :=
    hy_sq_mul_moebius_apply_eq_zero (le_trans hd2 hy2)
  have hmu : muLe y d = 0 := muLe_eq_zero_of_gt (lt_trans hyD hd1)
  have hid : (0 : ℤ)
      = moebius d - (muLe y d + muLe y d) + (muLe y * muLe y * (zeta : ArithmeticFunction ℤ)) d := by
    rw [← hzero, hy_sq_mul_moebius y]
    rfl
  rw [hmu] at hid
  linarith

/-- The same identity written as an explicit finite divisor sum, free of the
arithmetic-function abstraction:

  `μ(d) = − ∑_{n ∣ d} ∑_{a b = n} μ_{≤y}(a) μ_{≤y}(b)`. -/
theorem moebius_dyadic_divisor_sum {y D d : ℕ}
    (hyD : y < D) (hy2 : 2 * D ≤ y ^ 2) (hd1 : D < d) (hd2 : d ≤ 2 * D) :
    (moebius d : ℤ)
      = -∑ n ∈ d.divisors, ∑ ab ∈ n.divisorsAntidiagonal,
          muLe y ab.1 * muLe y ab.2 := by
  rw [moebius_dyadic_truncated hyD hy2 hd1 hd2, coe_mul_zeta_apply]
  simp [mul_apply]

/-! ## 6. The sign correction -/

/-- **The unsigned form of the identity is false.**  Taking `y = 5`, `D = 6`,
`d = 7` (so `y < D`, `2D = 12 ≤ 25 = y²`, `D < d ≤ 2D`) the unsigned identity
would force `μ(7) = 0`, whereas `μ(7) = −1`. -/
theorem unsigned_dyadic_identity_false :
    ¬ ∀ y D d : ℕ, y < D → 2 * D ≤ y ^ 2 → D < d → d ≤ 2 * D →
        (moebius d : ℤ) = ((muLe y * muLe y * (zeta : ArithmeticFunction ℤ)) d) := by
  intro h
  have h1 : (moebius 7 : ℤ) = ((muLe 5 * muLe 5 * (zeta : ArithmeticFunction ℤ)) 7) :=
    h 5 6 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 : (moebius 7 : ℤ) = -((muLe 5 * muLe 5 * (zeta : ArithmeticFunction ℤ)) 7) :=
    moebius_dyadic_truncated (y := 5) (D := 6) (d := 7)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h3 : (moebius 7 : ℤ) = -1 := moebius_apply_prime (by norm_num)
  omega

end MobiusK2
end Gate1BDet2
end TwinPrimeProject
