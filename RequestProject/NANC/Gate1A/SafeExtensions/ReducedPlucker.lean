/-
# NANC Gate 1A v9 — the reduced Plücker system

Input: `C, N, Delta : ℤ`, a common factor `g` with explicit quotient witnesses
`C = g*c`, `Delta = g*d`, the double-determinant identities, and *explicit*
coprimality hypotheses.  Everything is stated with quotient witnesses so that no
fragile `Int` division simplification is needed.

* `reducedPlucker_g_dvd_N`  — `gcd(g, ell2) = 1` (as `IsCoprime`) forces `g ∣ N`;
* `reducedPlucker_left`     — `q1*d = h1*c + ell2*n`;
* `reducedPlucker_right`    — `q2*d = h2*c + ell1*n`;
* `reducedPlucker_coprime_cd` — `gcd(c,d) = 1` when `g` is the actual gcd;
* `reducedPlucker_coprime_cn` — `gcd(c,n) = 1` under `gcd(q1,q2) = 1`
  (available when `q1 ≠ q2` are primes).
-/
import RequestProject.NANC.Gate1A.SafeExtensions.DoubleDeterminant

namespace TwinPrimeProject.NANC.Gate1A.V9

/-- **`g` divides `N`.**  From `h1*C + ell2*N = q1*Delta`, `C = g*c`,
`Delta = g*d` and `IsCoprime g ell2`. -/
theorem reducedPlucker_g_dvd_N {ell1 ell2 h1 h2 q1 q2 g c d : ℤ}
    (hC : detC ell1 ell2 q1 q2 = g * c)
    (hD : detDelta ell1 ell2 h1 h2 = g * d)
    (hcop : IsCoprime g ell2) :
    g ∣ detN h1 h2 q1 q2 := by
  have key := doubleDet_left ell1 ell2 h1 h2 q1 q2
  have hdvd : g ∣ ell2 * detN h1 h2 q1 q2 := by
    refine ⟨q1 * d - h1 * c, ?_⟩
    have : ell2 * detN h1 h2 q1 q2
        = q1 * detDelta ell1 ell2 h1 h2 - h1 * detC ell1 ell2 q1 q2 := by linarith
    rw [this, hC, hD]; ring
  exact hcop.dvd_of_dvd_mul_left hdvd

/-- **Left reduced identity** `q1*d = h1*c + ell2*n`. -/
theorem reducedPlucker_left {ell1 ell2 h1 h2 q1 q2 g c d n : ℤ} (hg : g ≠ 0)
    (hC : detC ell1 ell2 q1 q2 = g * c)
    (hD : detDelta ell1 ell2 h1 h2 = g * d)
    (hN : detN h1 h2 q1 q2 = g * n) :
    q1 * d = h1 * c + ell2 * n := by
  have key := doubleDet_left ell1 ell2 h1 h2 q1 q2
  rw [hC, hD, hN] at key
  have : g * (h1 * c + ell2 * n) = g * (q1 * d) := by linarith
  exact (mul_left_cancel₀ hg this).symm

/-- **Right reduced identity** `q2*d = h2*c + ell1*n`. -/
theorem reducedPlucker_right {ell1 ell2 h1 h2 q1 q2 g c d n : ℤ} (hg : g ≠ 0)
    (hC : detC ell1 ell2 q1 q2 = g * c)
    (hD : detDelta ell1 ell2 h1 h2 = g * d)
    (hN : detN h1 h2 q1 q2 = g * n) :
    q2 * d = h2 * c + ell1 * n := by
  have key := doubleDet_right ell1 ell2 h1 h2 q1 q2
  rw [hC, hD, hN] at key
  have : g * (h2 * c + ell1 * n) = g * (q2 * d) := by linarith
  exact (mul_left_cancel₀ hg this).symm

/-- **`c` and `d` are coprime** when `g` really is the gcd of `C` and `Delta`. -/
theorem reducedPlucker_coprime_cd {C Delta g c d : ℤ} (hg : g ≠ 0)
    (hC : C = g * c) (hD : Delta = g * d) (hgcd : (Int.gcd C Delta : ℤ) = g) :
    Int.gcd c d = 1 := by
  have hec : ((Int.gcd c d : ℕ) : ℤ) ∣ c := Int.gcd_dvd_left c d
  have hed : ((Int.gcd c d : ℕ) : ℤ) ∣ d := Int.gcd_dvd_right c d
  have h1 : g * ((Int.gcd c d : ℕ) : ℤ) ∣ C := by rw [hC]; exact mul_dvd_mul_left g hec
  have h2 : g * ((Int.gcd c d : ℕ) : ℤ) ∣ Delta := by rw [hD]; exact mul_dvd_mul_left g hed
  have h3 : g * ((Int.gcd c d : ℕ) : ℤ) ∣ ((Int.gcd C Delta : ℕ) : ℤ) := Int.dvd_coe_gcd h1 h2
  rw [hgcd] at h3
  obtain ⟨k, hk⟩ := h3
  have hek : ((Int.gcd c d : ℕ) : ℤ) * k = 1 := by
    have : g * (((Int.gcd c d : ℕ) : ℤ) * k) = g * 1 := by rw [mul_one, ← mul_assoc]; exact hk.symm
    exact mul_left_cancel₀ hg this
  have hdvd1 : ((Int.gcd c d : ℕ) : ℤ) ∣ 1 := ⟨k, hek.symm⟩
  have : ((Int.gcd c d : ℕ) : ℤ) = 1 :=
    Int.eq_one_of_dvd_one (Int.natCast_nonneg _) hdvd1
  exact_mod_cast this

/-- **`c` and `n` are coprime.**  A common divisor would divide both `q1` and
`q2` (using `gcd(c,d) = 1`), contradicting `IsCoprime q1 q2`, which is available
when `q1 ≠ q2` are primes. -/
theorem reducedPlucker_coprime_cn {ell1 ell2 h1 h2 q1 q2 g c d n : ℤ} (hg : g ≠ 0)
    (hC : detC ell1 ell2 q1 q2 = g * c)
    (hD : detDelta ell1 ell2 h1 h2 = g * d)
    (hN : detN h1 h2 q1 q2 = g * n)
    (hcd : IsCoprime c d) (hq : IsCoprime q1 q2) :
    Int.gcd c n = 1 := by
  have hec : ((Int.gcd c n : ℕ) : ℤ) ∣ c := Int.gcd_dvd_left c n
  have hen : ((Int.gcd c n : ℕ) : ℤ) ∣ n := Int.gcd_dvd_right c n
  have hq1 : ((Int.gcd c n : ℕ) : ℤ) ∣ q1 * d := by
    rw [reducedPlucker_left hg hC hD hN]
    exact dvd_add (hec.mul_left h1) (hen.mul_left ell2)
  have hq2 : ((Int.gcd c n : ℕ) : ℤ) ∣ q2 * d := by
    rw [reducedPlucker_right hg hC hD hN]
    exact dvd_add (hec.mul_left h2) (hen.mul_left ell1)
  have hed : IsCoprime ((Int.gcd c n : ℕ) : ℤ) d := IsCoprime.of_isCoprime_of_dvd_left hcd hec
  have he1 : ((Int.gcd c n : ℕ) : ℤ) ∣ q1 := hed.dvd_of_dvd_mul_right hq1
  have he2 : ((Int.gcd c n : ℕ) : ℤ) ∣ q2 := hed.dvd_of_dvd_mul_right hq2
  have hunit : IsUnit ((Int.gcd c n : ℕ) : ℤ) := hq.isUnit_of_dvd' he1 he2
  have hnn : (0 : ℤ) ≤ ((Int.gcd c n : ℕ) : ℤ) := Int.natCast_nonneg _
  have : ((Int.gcd c n : ℕ) : ℤ) = 1 := by
    rcases Int.isUnit_iff.mp hunit with h | h
    · exact h
    · omega
  exact_mod_cast this

end TwinPrimeProject.NANC.Gate1A.V9
