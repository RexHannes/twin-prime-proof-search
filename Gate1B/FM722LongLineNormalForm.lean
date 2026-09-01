import Mathlib

/-!
# Gate 1B · FM722 · the **long-line Diophantine normal form**

Pure finite arithmetic over `ℤ`.  No asymptotics, no range data, no analytic
claim.

Given the long line `q ℓ − T π = 2` with one solution `(q₀, T₀)` and
`gcd(ℓ, π) = 1`, `π ≠ 0`, every integer solution is

```
  q = q₀ + π t,      T = T₀ + ℓ t,      t ∈ ℤ,
```

and conversely.  The asymptotic length `Q/P` of the admissible `t`-range is
*not* formalised: it is exposed as an uninhabited range interface, since it
depends on source range data that is not part of this bank.
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace FM722

/-- **FM722-ANCHOR-LONGLINE-NORMALFORM45 (kernel form).**  The complete
parametrisation of the solutions of the long line `q ℓ − T π = 2` through a
given solution, in both directions. -/
theorem longline_parametrisation (q0 T0 ell pi : ℤ) (hpi : pi ≠ 0)
    (hco : Int.gcd ell pi = 1) (h0 : q0 * ell - T0 * pi = 2) (q T : ℤ) :
    q * ell - T * pi = 2 ↔ ∃ t : ℤ, q = q0 + pi * t ∧ T = T0 + ell * t := by
  have hcop : IsCoprime ell pi := Int.isCoprime_iff_gcd_eq_one.mpr hco
  constructor
  · intro hqT
    have hkey : (q - q0) * ell = (T - T0) * pi := by linarith [hqT, h0]
    have hdvd : pi ∣ (q - q0) * ell := ⟨T - T0, by rw [hkey]; ring⟩
    have hdvd' : pi ∣ (q - q0) := (hcop.symm).dvd_of_dvd_mul_right hdvd
    obtain ⟨t, ht⟩ := hdvd'
    refine ⟨t, by linarith [ht], ?_⟩
    have h2 : (pi * t) * ell = (T - T0) * pi := by rw [← ht]; exact hkey
    have h3 : pi * (t * ell) = pi * (T - T0) := by ring_nf; ring_nf at h2; linarith [h2]
    have h4 : t * ell = T - T0 := mul_left_cancel₀ hpi h3
    linarith [h4]
  · rintro ⟨t, hq, hT⟩
    subst hq
    subst hT
    ring_nf
    ring_nf at h0
    linarith [h0]

/-- **Range interface for the long line (supplied source data; never
constructed in this bank).**  The admissible `t`-range and its asymptotic
length `≍ Q/P` are source range data: this bank neither proves nor assumes
them, and no term of this type is ever produced here. -/
structure LongLineRangeData (Q P : ℝ) where
  /-- The number of admissible line parameters `t` in the source range. -/
  count : ℝ
  /-- Lower comparison with `Q/P`. -/
  lower : Q / P ≤ 2 * count
  /-- Upper comparison with `Q/P`. -/
  upper : count ≤ 2 * (Q / P)

end FM722
end CurrentProgramme
end TwinPrimeProject
