/-
# NANC Gate 1A v9 — the reduced conductor, and the constant-conductor exclusion

From the exact source relation `C = delta*p*(m+s)` together with `C = g*c` one
gets `c ∣ delta*p*(m+s)`.  Splitting off the part of `c` that meets
`2*k*delta*n`, i.e. writing `c = u * cSharp`, the *effective* conductor
`cSharp` divides `p*(m+s)` — **under an explicit coprimality hypothesis**
`IsCoprime cSharp delta`, which is stated, never hidden.

The final size contradiction is banked as a theorem with fully explicit integer
hypotheses (`constantReducedConductor_impossible`); it uses only the two facts

* every prime factor of `p*(m+s)` is at least `P0`;
* the small modulus `2*k*delta` is nonzero and smaller than `P0`.

**FIREWALL.**  No analytic cancellation is derived from any of this.
-/
import Mathlib

namespace TwinPrimeProject.NANC.Gate1A.V9

/-- `c` divides the source product. -/
theorem reducedConductor_dvd {C c g delta p m s : ℤ}
    (hC : C = g * c) (hsrc : C = delta * p * (m + s)) :
    c ∣ delta * p * (m + s) := by
  rw [← hsrc, hC]
  exact Dvd.intro_left g rfl

/-- The reduced conductor: the part of `c` coprime to `delta`. -/
theorem reducedConductor_cSharp_dvd {c u cSharp delta p m s : ℤ}
    (hsplit : c = u * cSharp) (hdvd : c ∣ delta * (p * (m + s)))
    (hcop : IsCoprime cSharp delta) :
    cSharp ∣ p * (m + s) := by
  have h1 : cSharp ∣ delta * (p * (m + s)) := dvd_trans ⟨u, by rw [hsplit]; ring⟩ hdvd
  exact hcop.dvd_of_dvd_mul_left h1

/- The intended normalisation is `u = gcd(c, 2*k*delta*n)` and `cSharp = c / u`.
That specific choice of `u` is *not* needed for the divisibility conclusion: the
statement above already covers it, since any splitting `c = u * cSharp` with
`cSharp` coprime to `delta` works, and no separate theorem with an unused
`u = gcd(...)` hypothesis is banked. -/

/-- **Constant reduced conductor is impossible** in the clean sector.  If the
effective conductor `c` is trivial in the sense that it divides the small
modulus `2*k*delta`, while every prime factor of `p*(m+s)` is at least `P0` and
`|2*k*delta| < P0`, then `c` must be a unit; assuming it is not gives a
contradiction. -/
theorem constantReducedConductor_impossible {c k delta p m s P0 : ℤ}
    (hcunit : c.natAbs ≠ 1)
    (hsmall : c ∣ 2 * k * delta) (hne : 2 * k * delta ≠ 0)
    (hsize : |2 * k * delta| < P0)
    (hcps : c ∣ p * (m + s))
    (hprimes : ∀ pi : ℤ, Prime pi → pi ∣ p * (m + s) → P0 ≤ |pi|) :
    False := by
  obtain ⟨pi, hpi, hpic⟩ := Int.exists_prime_and_dvd hcunit
  have hlow : P0 ≤ |pi| := hprimes pi hpi (hpic.trans hcps)
  have hdvdsmall : pi ∣ 2 * k * delta := hpic.trans hsmall
  have habs : |pi| ∣ |2 * k * delta| := (abs_dvd _ _).mpr ((dvd_abs _ _).mpr hdvdsmall)
  have hup : |pi| ≤ |2 * k * delta| := Int.le_of_dvd (abs_pos.mpr hne) habs
  linarith

end TwinPrimeProject.NANC.Gate1A.V9
