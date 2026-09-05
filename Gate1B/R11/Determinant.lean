/-
# Gate1B / R11 : matched determinant algebra and Bézout parametrization (§10, §11)

Exact arithmetic for the matched determinant `A*B + 2 = k*d` at the **fixed shift 2**
(nothing here averages over the shift):

* the integer determinant identity `A*B − k*d = −2`;
* all four cross gcd identities;
* the affine (Bézout) parametrization of the solution set, with uniqueness.
-/
import Mathlib

namespace Gate1B.R11

/-! ## 1. Matched determinant -/

/-- The matched determinant identity, over `ℤ` to avoid truncated subtraction. -/
theorem determinant_eq_neg_two {A B k d : ℕ} (h : A * B + 2 = k * d) :
    (A : ℤ) * (B : ℤ) - (k : ℤ) * (d : ℤ) = -2 := by
  have hz : (A : ℤ) * (B : ℤ) + 2 = (k : ℤ) * (d : ℤ) := by exact_mod_cast h
  linarith

/-! ## 2. The four cross gcd identities -/

/-- A divisor of `2` which is odd equals `1`. -/
theorem eq_one_of_dvd_two_of_odd {g : ℕ} (h2 : g ∣ 2) (hodd : Odd g) : g = 1 := by
  rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
  · exact h
  · exact absurd (h ▸ hodd) (by decide)

/-- Divisors of odd numbers are odd (local copy, to keep this file self-contained). -/
theorem odd_of_dvd_odd' {N e : ℕ} (hN : Odd N) (hd : e ∣ N) : Odd e := by
  rcases Nat.even_or_odd e with he | ho
  · exact absurd (even_iff_two_dvd.mpr (dvd_trans he.two_dvd hd))
      (Nat.not_even_iff_odd.mpr hN)
  · exact ho

/-- Core cross-coprimality step: from `x*y + 2 = u*v` with `x` odd, `gcd(x,u) = 1`. -/
theorem cross_coprime_aux {x y u v : ℕ} (h : x * y + 2 = u * v) (hx : Odd x) :
    Nat.gcd x u = 1 := by
  have hgx : Nat.gcd x u ∣ x := Nat.gcd_dvd_left x u
  have hgu : Nat.gcd x u ∣ u := Nat.gcd_dvd_right x u
  have h1 : Nat.gcd x u ∣ x * y := hgx.mul_right y
  have h2 : Nat.gcd x u ∣ x * y + 2 := h ▸ hgu.mul_right v
  have h3 : Nat.gcd x u ∣ 2 := by
    have := Nat.dvd_sub h2 h1
    simpa using this
  exact eq_one_of_dvd_two_of_odd h3 (odd_of_dvd_odd' hx hgx)

/-- **All four cross gcd identities** for a matched determinant with odd entries. -/
theorem determinant_pairwise_cross_coprime {A B k d : ℕ}
    (hA : Odd A) (hB : Odd B) (h : A * B + 2 = k * d) :
    Nat.gcd A k = 1 ∧ Nat.gcd A d = 1 ∧ Nat.gcd B k = 1 ∧ Nat.gcd B d = 1 := by
  refine ⟨cross_coprime_aux h hA, ?_, ?_, ?_⟩
  · exact cross_coprime_aux (x := A) (y := B) (u := d) (v := k) (by rw [h, mul_comm k d]) hA
  · exact cross_coprime_aux (x := B) (y := A) (u := k) (v := d) (by rw [mul_comm B A, h]) hB
  · exact cross_coprime_aux (x := B) (y := A) (u := d) (v := k)
      (by rw [mul_comm B A, h, mul_comm k d]) hB

/-! ## 3. Bézout / affine parametrization -/

/-- Every integer `t` produces a further solution of the matched determinant equation. -/
theorem determinant_solution_parametrization {A k B0 d0 : ℤ} (h : A * B0 + 2 = k * d0)
    (t : ℤ) : A * (B0 + k * t) + 2 = k * (d0 + A * t) := by linear_combination h

/-- **Uniqueness of the affine parameter.**  With `gcd(A,k) = 1` and `k ≠ 0`, every integer
solution of `A*B + 2 = k*d` is `(B0 + k t, d0 + A t)` for exactly one `t`. -/
theorem determinant_solution_parametrization_unique {A k B0 d0 B d : ℤ}
    (hk : k ≠ 0) (hcop : IsCoprime k A) (h0 : A * B0 + 2 = k * d0) (h : A * B + 2 = k * d) :
    ∃! t : ℤ, B = B0 + k * t ∧ d = d0 + A * t := by
  have hkey : A * (B - B0) = k * (d - d0) := by linear_combination h - h0
  have hdvd : k ∣ A * (B - B0) := ⟨d - d0, hkey⟩
  have hkB : k ∣ B - B0 := hcop.dvd_of_dvd_mul_left hdvd
  obtain ⟨t, ht⟩ := hkB
  refine ⟨t, ⟨by linarith [ht], ?_⟩, ?_⟩
  · have : k * (A * t) = k * (d - d0) := by
      rw [← hkey, ht]; ring
    have := mul_left_cancel₀ hk this
    linarith
  · rintro s ⟨hs1, -⟩
    have : k * t = k * s := by rw [← ht]; linarith
    exact (mul_left_cancel₀ hk this).symm

/-- Bridge: natural-number coprimality gives integer coprimality, so the parametrization
applies to the matched determinant of §2. -/
theorem isCoprime_of_nat_gcd_eq_one {a b : ℕ} (h : Nat.gcd a b = 1) :
    IsCoprime (a : ℤ) (b : ℤ) := Int.isCoprime_iff_gcd_eq_one.mpr (by simpa using h)

end Gate1B.R11
