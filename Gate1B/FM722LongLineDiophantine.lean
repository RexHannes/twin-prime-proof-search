import Mathlib

/-!
# Gate 1B · FM722 · the **determinant-`(-2)` long line**

Pure finite arithmetic over `ℤ`.  Nothing analytic is proved, assumed, or
interfaced here.

The object of this module is the *long line of determinant `-2`*

```
  A · b − ell · q = −2 ,
```

parametrised through one solution `(q₀ , b₀)` by

```
  q = q₀ + A · s ,      b = b₀ + ell · s ,      s ∈ ℤ .
```

## Contents

* §1 the forward line lemma (every `s` stays on the determinant line);
* §2 the converse (with `A ≠ 0` and `gcd(A, ell) = 1` the parametrisation is
  exhaustive), and the resulting equivalence;
* §3 the **odd coprimality lemma**: a divisor `y` of `b` which is odd is
  automatically coprime to `ell`;
* §4 the factor-`2` case, kept explicitly separate: for even `y` the
  conclusion genuinely fails, with a finite countermodel.

## Semantic guard

Determinant preservation is an *algebraic* statement.  It is **not** an
analytic saving, and no module of this bank may read it as one.
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace FM722LongLine

/-! ## 1. The forward determinant-line lemma -/

/-- **FM722-LONGLINE-DETERMINANT2-FORWARD.**  If `(q₀ , b₀)` lies on the
determinant line `A b − ell q = −2`, then so does every point
`q = q₀ + A s`, `b = b₀ + ell s`. -/
theorem det2_line_forward (A ell q0 b0 : ℤ) (h0 : A * b0 - ell * q0 = -2) (s : ℤ) :
    A * (b0 + ell * s) - ell * (q0 + A * s) = -2 := by
  linear_combination h0

/-! ## 2. The converse -/

/-- **FM722-LONGLINE-DETERMINANT2-CONVERSE.**  With `A ≠ 0` and
`gcd(A, ell) = 1`, every solution of `A b − ell q = −2` is on the line through
a given solution. -/
theorem det2_line_converse (A ell q0 b0 q b : ℤ) (hA : A ≠ 0) (hco : IsCoprime A ell)
    (h0 : A * b0 - ell * q0 = -2) (h : A * b - ell * q = -2) :
    ∃ s : ℤ, q = q0 + A * s ∧ b = b0 + ell * s := by
  have hkey : A * (b - b0) = ell * (q - q0) := by linarith
  have hdvd : A ∣ (q - q0) := by
    refine hco.dvd_of_dvd_mul_left ?_
    exact ⟨b - b0, by linarith⟩
  obtain ⟨s, hs⟩ := hdvd
  refine ⟨s, by linarith, ?_⟩
  have h2 : A * (b - b0) = A * (ell * s) := by
    rw [hkey, hs]; ring
  have h3 : b - b0 = ell * s := mul_left_cancel₀ hA h2
  linarith

/-- **The determinant line, both directions.** -/
theorem det2_line_iff (A ell q0 b0 q b : ℤ) (hA : A ≠ 0) (hco : IsCoprime A ell)
    (h0 : A * b0 - ell * q0 = -2) :
    (A * b - ell * q = -2) ↔ ∃ s : ℤ, q = q0 + A * s ∧ b = b0 + ell * s := by
  constructor
  · intro h; exact det2_line_converse A ell q0 b0 q b hA hco h0 h
  · rintro ⟨s, hq, hb⟩; subst hq; subst hb; exact det2_line_forward A ell q0 b0 h0 s

/-! ## 3. The odd coprimality lemma -/

/-- Any common divisor of `y ∣ b` and of `ell` divides `2`, on the determinant
line.  This is the raw form of the coprimality lemma, valid for every parity. -/
theorem gcd_divides_two_of_det2 (A ell q b y : ℤ) (hy : y ∣ b)
    (hdet : A * b - ell * q = -2) : (Int.gcd y ell : ℤ) ∣ 2 := by
  have hgy : ((Int.gcd y ell : ℕ) : ℤ) ∣ y := Int.gcd_dvd_left y ell
  have hge : ((Int.gcd y ell : ℕ) : ℤ) ∣ ell := Int.gcd_dvd_right y ell
  have h1 : ((Int.gcd y ell : ℕ) : ℤ) ∣ A * b := Dvd.dvd.mul_left (hgy.trans hy) A
  have h2 : ((Int.gcd y ell : ℕ) : ℤ) ∣ ell * q := Dvd.dvd.mul_right hge q
  have h3 : ((Int.gcd y ell : ℕ) : ℤ) ∣ (-2 : ℤ) := by
    rw [← hdet]; exact dvd_sub h1 h2
  simpa using h3

/-- **FM722-LONGLINE-ODD-COPRIMALITY.**  On the determinant line
`A b − ell q = −2`, an **odd** divisor `y` of `b` is coprime to `ell`. -/
theorem odd_divisor_coprime_ell (A ell q b y : ℤ) (hy : y ∣ b) (hodd : Odd y)
    (hdet : A * b - ell * q = -2) : Int.gcd y ell = 1 := by
  have hdvd : (Int.gcd y ell : ℤ) ∣ 2 := gcd_divides_two_of_det2 A ell q b y hy hdet
  have hnat : Int.gcd y ell ∣ 2 := by exact_mod_cast hdvd
  rcases (Nat.dvd_prime Nat.prime_two).mp hnat with h | h
  · exact h
  · exfalso
    have h2y : (2 : ℤ) ∣ y := by
      have hy' : ((Int.gcd y ell : ℕ) : ℤ) ∣ y := Int.gcd_dvd_left y ell
      rw [h] at hy'; simpa using hy'
    rcases hodd with ⟨k, hk⟩
    omega

/-- The `IsCoprime` form of the odd coprimality lemma. -/
theorem odd_divisor_isCoprime_ell (A ell q b y : ℤ) (hy : y ∣ b) (hodd : Odd y)
    (hdet : A * b - ell * q = -2) : IsCoprime y ell :=
  Int.isCoprime_iff_gcd_eq_one.mpr (odd_divisor_coprime_ell A ell q b y hy hodd hdet)

/-! ## 4. The factor-`2` case, kept explicitly separate -/

/-- **The oddness hypothesis is necessary.**  For `y = 2` the same determinant
data gives `gcd(y, ell) = 2 ≠ 1`: an explicit finite countermodel. -/
theorem det2_even_y_countermodel :
    ∃ A ell q b y : ℤ, y ∣ b ∧ A * b - ell * q = -2 ∧ Int.gcd y ell ≠ 1 := by
  refine ⟨1, 2, 1, 0, 2, ⟨0, by ring⟩, by ring, ?_⟩
  decide

/-- In the even case, all that survives is the divisor-of-`2` bound. -/
theorem even_case_gcd_dvd_two (A ell q b y : ℤ) (hy : y ∣ b)
    (hdet : A * b - ell * q = -2) : Int.gcd y ell ∣ 2 := by
  have hdvd : (Int.gcd y ell : ℤ) ∣ 2 := gcd_divides_two_of_det2 A ell q b y hy hdet
  exact_mod_cast hdvd

end FM722LongLine
end CurrentProgramme
end TwinPrimeProject
