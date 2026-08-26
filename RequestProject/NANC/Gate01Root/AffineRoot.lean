import Gate04Root.Affine
import RequestProject.NANC.Gate01.GenericCRTResidue

/-!
# Gate01Root: affine root data

The root-route edge data `(r, m, k, m', w₀, α, β)` with

* `m' = m + k r`,
* `r α = m w₀ + 2`,
* `β = α + k w₀`,

and the two affine identities

* `m' α - m β = 2 k`   (`root_affine_det_eq_two_k`),
* `r β = m' w₀ + 2`    (`root_beta_affine_relation`).

Both are obtained by *reuse*: the second is the shifted canonical relation and
the first is also derivable from the already banked
`RouteAFibreFrame.Gate01.edge_determinant` (which additionally assumes `r ≠ 0`);
we record that reuse explicitly in `root_affine_det_eq_two_k_via_bank`.

The canonical range `0 ≤ w₀ < r` is a *reconstructed-model* hypothesis, kept in
the separate structure `CanonicalRootEdgeData`.  It is not an exhaustive-source
theorem.

Everything here is finite integer algebra.
-/

namespace RouteAFibreFrame
namespace Gate01Root

/-- Integer data of a root-route edge. -/
structure RootEdgeData where
  /-- The modulus. -/
  r : ℤ
  /-- The base point. -/
  m : ℤ
  /-- The (signed, nonzero in the graph rows) jump. -/
  k : ℤ
  /-- The shifted point `m' = m + k r`. -/
  mPrime : ℤ
  /-- The canonical root representative. -/
  w0 : ℤ
  /-- The base numerator. -/
  alpha : ℤ
  /-- The shifted numerator. -/
  beta : ℤ
  /-- `m' = m + k r`. -/
  mPrime_def : mPrime = m + k * r
  /-- `r α = m w₀ + 2`. -/
  alpha_def : r * alpha = m * w0 + 2
  /-- `β = α + k w₀`. -/
  beta_linear : beta = alpha + k * w0

namespace RootEdgeData

variable (e : RootEdgeData)

/-- Bridge to the standalone affine edge data of `Gate04Root`. -/
def toAffineEdgeData : Gate04Root.AffineEdgeData :=
  ⟨e.r, e.m, e.k, e.mPrime, e.w0, e.alpha, e.beta, e.mPrime_def, e.alpha_def, e.beta_linear⟩

@[simp] theorem toAffineEdgeData_r : e.toAffineEdgeData.r = e.r := rfl
@[simp] theorem toAffineEdgeData_m : e.toAffineEdgeData.m = e.m := rfl
@[simp] theorem toAffineEdgeData_k : e.toAffineEdgeData.k = e.k := rfl
@[simp] theorem toAffineEdgeData_mPrime : e.toAffineEdgeData.mPrime = e.mPrime := rfl
@[simp] theorem toAffineEdgeData_w0 : e.toAffineEdgeData.w0 = e.w0 := rfl
@[simp] theorem toAffineEdgeData_alpha : e.toAffineEdgeData.alpha = e.alpha := rfl
@[simp] theorem toAffineEdgeData_beta : e.toAffineEdgeData.beta = e.beta := rfl

end RootEdgeData

/-- **(AFF)**  `m' α - m β = 2 k`. -/
theorem root_affine_det_eq_two_k (e : RootEdgeData) :
    e.mPrime * e.alpha - e.m * e.beta = 2 * e.k :=
  e.toAffineEdgeData.affine_det_eq_two_k

/-- The shifted affine relation `r β = m' w₀ + 2`. -/
theorem root_beta_affine_relation (e : RootEdgeData) :
    e.r * e.beta = e.mPrime * e.w0 + 2 :=
  e.toAffineEdgeData.beta_affine_relation

/-- The same determinant identity obtained by *reusing* the banked
`Gate01.edge_determinant` (which carries the extra hypothesis `r ≠ 0`). -/
theorem root_affine_det_eq_two_k_via_bank (e : RootEdgeData) (hr : e.r ≠ 0) :
    e.mPrime * e.alpha - e.m * e.beta = 2 * e.k :=
  Gate01.edge_determinant hr e.mPrime_def e.alpha_def (root_beta_affine_relation e)

/-- `m ∣ r α - 2`, the canonical congruence of the base edge. -/
theorem root_m_dvd_r_alpha_sub_two (e : RootEdgeData) : e.m ∣ e.r * e.alpha - 2 :=
  e.toAffineEdgeData.m_dvd_r_alpha_sub_two

/-- `m' ∣ r β - 2`, the canonical congruence of the shifted edge. -/
theorem root_mPrime_dvd_r_beta_sub_two (e : RootEdgeData) : e.mPrime ∣ e.r * e.beta - 2 :=
  e.toAffineEdgeData.mPrime_dvd_r_beta_sub_two

/-- The **reconstructed** canonical-range extension.  `0 ≤ w₀ < r` is a modelling
hypothesis of the reconstruction, not an exhaustive-source theorem. -/
structure CanonicalRootEdgeData extends RootEdgeData where
  /-- `0 < r`. -/
  r_pos : 0 < r
  /-- `0 < m`. -/
  m_pos : 0 < m
  /-- `0 ≤ w₀`. -/
  w0_nonneg : 0 ≤ w0
  /-- `w₀ < r`. -/
  w0_lt_r : w0 < r

namespace CanonicalRootEdgeData

variable (e : CanonicalRootEdgeData)

/-- Bridge to the `Gate04Root` canonical-range predicate. -/
theorem toCanonicalRange :
    Gate04Root.CanonicalRange e.toRootEdgeData.toAffineEdgeData :=
  ⟨e.w0_nonneg, e.w0_lt_r, e.r_pos, e.m_pos⟩

/-- **`0 < α ≤ m`** in the canonical range, for `3 ≤ r` and `3 ≤ m`.

(The bound `α ≤ m` in fact only needs `2 ≤ m`; the hypothesis `3 ≤ r` is not
used.  It cannot be dropped entirely: for `m = r = 1` one has `α = 2 > m`.) -/
theorem alpha_pos_le_m_of_canonical_range (hr : 3 ≤ e.r) (hm : 3 ≤ e.m) :
    0 < e.alpha ∧ e.alpha ≤ e.m := by
  have hc := e.toCanonicalRange
  exact ⟨hc.alpha_pos, hc.alpha_le_m (show (2 : ℤ) ≤ e.m by omega)⟩

/-- The sharp cleared-denominator upper bound `r α < m r + 2`. -/
theorem r_mul_alpha_lt : e.r * e.alpha < e.m * e.r + 2 :=
  e.toCanonicalRange.r_mul_alpha_lt

end CanonicalRootEdgeData

end Gate01Root
end RouteAFibreFrame
