/-
# NANC Gate 1A v9 — the moving complementary-divisor identity (fibre only)

Signed integer variables `ell1, ell2, q1, q2, delta, p, m, s` tied by the source
relation

    ell1*q1 − ell2*q2 = delta*p*(m+s).

Banked here:

* `ComplementaryDivisorData` — the frozen data carrying the relation;
* `complementary_deltaP_dvd` — `delta*p ∣ ell1*q1 − ell2*q2`;
* `complementary_m_eq` — the exact quotient form of `m` (stated multiplicatively
  so that no `Int` division appears);
* `complementary_m_unique` — the **one-root fibre theorem**: `m` is determined by
  the frozen data.

**FIREWALL.**  This is a FIBRE theorem only.  A one-root fibre is *not* an
analytic saving.
-/
import Mathlib

namespace TwinPrimeProject.NANC.Gate1A.V9

/-- Frozen data for the moving complementary-divisor identity. -/
structure ComplementaryDivisorData where
  ell1 : ℤ
  ell2 : ℤ
  q1 : ℤ
  q2 : ℤ
  delta : ℤ
  p : ℤ
  m : ℤ
  s : ℤ
  hdelta : delta ≠ 0
  hp : p ≠ 0
  relation : ell1 * q1 - ell2 * q2 = delta * p * (m + s)

namespace ComplementaryDivisorData

variable (D : ComplementaryDivisorData)

/-- `delta*p` divides the cross-determinant. -/
theorem complementary_deltaP_dvd : D.delta * D.p ∣ D.ell1 * D.q1 - D.ell2 * D.q2 :=
  ⟨D.m + D.s, D.relation⟩

/-- `delta*p ≠ 0`. -/
theorem deltaP_ne_zero : D.delta * D.p ≠ 0 := mul_ne_zero D.hdelta D.hp

/-- **Exact rearrangement.**  `m` is the quotient of the cross-determinant by
`delta*p`, minus `s`; stated multiplicatively to avoid integer division. -/
theorem complementary_m_eq :
    D.delta * D.p * (D.m + D.s) = D.ell1 * D.q1 - D.ell2 * D.q2 := D.relation.symm

/-- The quotient witness: `(ell1*q1 − ell2*q2)/(delta*p) = m + s` as an exact
integer division. -/
theorem complementary_m_ediv :
    (D.ell1 * D.q1 - D.ell2 * D.q2) / (D.delta * D.p) = D.m + D.s := by
  rw [D.relation]
  exact Int.mul_ediv_cancel_left _ D.deltaP_ne_zero

end ComplementaryDivisorData

/-- **One-root fibre.**  Two data sets with the same frozen `(ell, q, delta, p, s)`
have the same `m`. -/
theorem complementary_m_unique {ell1 ell2 q1 q2 delta p s m m' : ℤ}
    (hdelta : delta ≠ 0) (hp : p ≠ 0)
    (h : ell1 * q1 - ell2 * q2 = delta * p * (m + s))
    (h' : ell1 * q1 - ell2 * q2 = delta * p * (m' + s)) :
    m = m' := by
  have hdp : delta * p ≠ 0 := mul_ne_zero hdelta hp
  have : delta * p * (m + s) = delta * p * (m' + s) := by rw [← h, ← h']
  have := mul_left_cancel₀ hdp this
  linarith

end TwinPrimeProject.NANC.Gate1A.V9
