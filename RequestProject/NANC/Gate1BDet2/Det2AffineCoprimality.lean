import Mathlib
import RequestProject.NANC.Gate1BDet2.Det2AffineLines

/-!
# Gate 1B / determinant-2 bank, Module 5: coprimality along the affine line

The two affine forms

  `V(t) = v₀ + l t`,  `Q(t) = q₀ + u t`

have fixed determinant `l Q(t) − u V(t) = 2`.  Hence a common divisor of the two
forms divides `2`, and in the odd sector the two forms are coprime for *every*
value of the affine parameter: they cannot share an odd prime factor.
-/

namespace TwinPrimeProject
namespace Gate1BDet2

/-! ## 1. Integer statement -/

/-- **Affine-form rigidity.**  Any common divisor of the two affine forms on a
determinant-2 line divides `2`. -/
theorem affine_common_divisor_dvd_two {u l v₀ q₀ t g : ℤ}
    (h : OnDet2Line u l v₀ q₀)
    (hgv : g ∣ v₀ + l * t) (hgq : g ∣ q₀ + u * t) : g ∣ 2 := by
  have hdet : l * (q₀ + u * t) - u * (v₀ + l * t) = 2 := det2_translate h t
  rw [← hdet]
  exact dvd_sub (hgq.mul_left l) (hgv.mul_left u)

/-- The integer gcd of the two affine forms divides `2`. -/
theorem affine_gcd_dvd_two {u l v₀ q₀ t : ℤ} (h : OnDet2Line u l v₀ q₀) :
    Int.gcd (v₀ + l * t) (q₀ + u * t) ∣ 2 := by
  have hg : ((Int.gcd (v₀ + l * t) (q₀ + u * t) : ℕ) : ℤ) ∣ 2 :=
    affine_common_divisor_dvd_two (t := t) h (Int.gcd_dvd_left _ _) (Int.gcd_dvd_right _ _)
  exact_mod_cast hg

/-! ## 2. Natural-number odd-sector consequence -/

/-- **Odd affine forms are coprime.**  If the two affine forms of a
determinant-2 line take natural values `V, Q` at the parameter `t` and `V` is
odd, then `V` and `Q` are coprime.  (The oddness of `Q` is not needed; it is
automatic in the source, where `Q` is odd as well.) -/
theorem affine_coprime_of_odd {u l v₀ q₀ t : ℤ} {V Q : ℕ}
    (h : OnDet2Line u l v₀ q₀)
    (hV : (V : ℤ) = v₀ + l * t) (hQ : (Q : ℤ) = q₀ + u * t)
    (hodd : Odd V) : Nat.Coprime V Q := by
  have hg : ((Nat.gcd V Q : ℕ) : ℤ) ∣ 2 := by
    refine affine_common_divisor_dvd_two (t := t) h ?_ ?_
    · rw [← hV]; exact_mod_cast Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left V Q)
    · rw [← hQ]; exact_mod_cast Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_right V Q)
  have hg' : Nat.gcd V Q ∣ 2 := by exact_mod_cast hg
  exact eq_one_of_dvd_two_of_dvd_odd hg' (Nat.gcd_dvd_left V Q) hodd

/-- The same statement with both forms odd, as it occurs in the source. -/
theorem affine_coprime_of_odd_odd {u l v₀ q₀ t : ℤ} {V Q : ℕ}
    (h : OnDet2Line u l v₀ q₀)
    (hV : (V : ℤ) = v₀ + l * t) (hQ : (Q : ℤ) = q₀ + u * t)
    (hoddV : Odd V) (_hoddQ : Odd Q) : Nat.Coprime V Q :=
  affine_coprime_of_odd h hV hQ hoddV

/-- **No shared odd prime factor.**  On a determinant-2 line no odd prime
divides both affine forms. -/
theorem no_common_odd_prime {u l v₀ q₀ t : ℤ} {p : ℕ} (hp : Nat.Prime p)
    (hodd : p ≠ 2) (h : OnDet2Line u l v₀ q₀)
    (hpv : (p : ℤ) ∣ v₀ + l * t) (hpq : (p : ℤ) ∣ q₀ + u * t) : False := by
  have hg : ((p : ℕ) : ℤ) ∣ 2 := affine_common_divisor_dvd_two h hpv hpq
  have hp2 : (p : ℕ) ∣ 2 := by exact_mod_cast hg
  rcases (Nat.prime_two.eq_one_or_self_of_dvd p hp2) with h1 | h2
  · exact hp.one_lt.ne' h1
  · exact hodd h2

end Gate1BDet2
end TwinPrimeProject
