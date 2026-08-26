/-
# Gate04Root.Affine

Integer affine data of a root-collapse edge, and the two banked affine identities

* `affine_det_eq_two_k` :  `m' * α - m * β = 2 * k`      (AFF)
* `beta_affine_relation` : `r * β = m' * w₀ + 2`

together with the *canonical range* consequences (kept in a separate structure, so
that the basic affine identities never silently depend on the range hypotheses).

Everything here is elementary integer algebra.  No analytic input.
-/
import Mathlib

namespace Gate04Root

/-- The integer affine data attached to one edge of the root-collapse graph.

`w₀` is the canonical representative of the relevant residue, `α` the associated
numerator at level `m`, `β` the numerator at the shifted level `m' = m + k r`. -/
structure AffineEdgeData where
  r : ℤ
  m : ℤ
  k : ℤ
  mPrime : ℤ
  w0 : ℤ
  alpha : ℤ
  beta : ℤ
  mPrime_def : mPrime = m + k * r
  alpha_def : r * alpha = m * w0 + 2
  beta_linear : beta = alpha + k * w0

namespace AffineEdgeData

variable (e : AffineEdgeData)

/-- **(AFF)** The affine determinant of an edge is exactly `2k`. -/
theorem affine_det_eq_two_k : e.mPrime * e.alpha - e.m * e.beta = 2 * e.k := by
  have h1 := e.mPrime_def
  have h2 := e.alpha_def
  have h3 := e.beta_linear
  rw [h1, h3]
  linear_combination e.k * h2

/-- The shifted affine relation `r β = m' w₀ + 2`. -/
theorem beta_affine_relation : e.r * e.beta = e.mPrime * e.w0 + 2 := by
  have h2 := e.alpha_def
  rw [e.mPrime_def, e.beta_linear]
  linear_combination h2

/-- `m` divides `r α - 2`; this is the congruence used by the gcd lemmas. -/
theorem m_dvd_r_alpha_sub_two : e.m ∣ e.r * e.alpha - 2 :=
  ⟨e.w0, by linear_combination e.alpha_def⟩

/-- `m'` divides `r β - 2`. -/
theorem mPrime_dvd_r_beta_sub_two : e.mPrime ∣ e.r * e.beta - 2 :=
  ⟨e.w0, by linear_combination e.beta_affine_relation⟩

end AffineEdgeData

/-- The *canonical range* hypotheses, deliberately kept separate from
`AffineEdgeData` so that the affine identities above never depend on them. -/
structure CanonicalRange (e : AffineEdgeData) : Prop where
  w0_nonneg : 0 ≤ e.w0
  w0_lt_r : e.w0 < e.r
  r_pos : 0 < e.r
  m_pos : 0 < e.m

namespace CanonicalRange

variable {e : AffineEdgeData} (hc : CanonicalRange e)
include hc

/-- In the canonical range `α` is strictly positive. -/
theorem alpha_pos : 0 < e.alpha := by
  have h := e.alpha_def
  have hw : 0 ≤ e.m * e.w0 := mul_nonneg hc.m_pos.le hc.w0_nonneg
  have hra : 0 < e.r * e.alpha := by omega
  by_contra hcon
  push_neg at hcon
  nlinarith [hc.r_pos]

/-- The sharp upper bound in cleared-denominator form: `r α < m r + 2`,
i.e. `α < m + 2/r`. -/
theorem r_mul_alpha_lt : e.r * e.alpha < e.m * e.r + 2 := by
  have h := e.alpha_def
  have hw : e.w0 ≤ e.r - 1 := by have := hc.w0_lt_r; omega
  have h1 : e.m * e.w0 ≤ e.m * (e.r - 1) :=
    mul_le_mul_of_nonneg_left hw hc.m_pos.le
  nlinarith [hc.m_pos]

/-- The elementary integer bound `α ≤ m`, valid as soon as `2 ≤ m`.
(For `m = 1, r = 1` one really has `α = 2 > m`, so the hypothesis `2 ≤ m` cannot
be dropped; we do not force a false strict bound.) -/
theorem alpha_le_m (hm : 2 ≤ e.m) : e.alpha ≤ e.m := by
  have h := e.alpha_def
  have hw : e.w0 ≤ e.r - 1 := by have := hc.w0_lt_r; omega
  have h1 : e.m * e.w0 ≤ e.m * (e.r - 1) :=
    mul_le_mul_of_nonneg_left hw hc.m_pos.le
  have h2 : e.r * e.alpha ≤ e.m * e.r := by nlinarith
  nlinarith [hc.r_pos]

end CanonicalRange

end Gate04Root
