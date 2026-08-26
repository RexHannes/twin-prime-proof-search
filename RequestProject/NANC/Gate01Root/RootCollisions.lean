import Gate04Root.Collisions
import RequestProject.NANC.Gate01Root.RootCollapse

/-!
# Gate01Root: root-collision determinants

`Δ_A(e,f) = α_e m_f - α_f m_e`, `Δ_B(e,f) = β_e m'_f - β_f m'_e`, the collision
criteria `t_p(e) = t_p(f) ↔ p ∣ Δ_A`, `t_q(e) = t_q(f) ↔ q ∣ Δ_B`, and the
rigidity statements.

Signed `k` is handled explicitly: `k` is an arbitrary nonzero integer in
`double_delta_zero_row_eq`, and the equality `k_e = k_f` is obtained from the
affine determinant identity `m' α - m β = 2 k` (whose right-hand side is signed),
not from any positivity assumption.
-/

namespace RouteAFibreFrame
namespace Gate01Root

/-- Base collision determinant. -/
def deltaA (e f : RootEdgeData) : ℤ :=
  Gate04Root.deltaA e.toAffineEdgeData f.toAffineEdgeData

/-- Shifted collision determinant. -/
def deltaB (e f : RootEdgeData) : ℤ :=
  Gate04Root.deltaB e.toAffineEdgeData f.toAffineEdgeData

theorem deltaA_eq (e f : RootEdgeData) : deltaA e f = e.alpha * f.m - f.alpha * e.m := rfl

theorem deltaB_eq (e f : RootEdgeData) :
    deltaB e f = e.beta * f.mPrime - f.beta * e.mPrime := rfl

variable {p q : ℕ}

/-- **Collision criterion at `p`.** -/
theorem rootP_eq_iff_dvd_deltaA (e f : RootEdgeData) {ime imf : ZMod p}
    (hme : (e.m : ZMod p) * ime = 1) (hmf : (f.m : ZMod p) * imf = 1) :
    rootP e.alpha ime = rootP f.alpha imf ↔ (p : ℤ) ∣ deltaA e f :=
  Gate04Root.rootP_eq_iff_dvd_deltaA e.toAffineEdgeData f.toAffineEdgeData hme hmf

/-- **Collision criterion at `q`.** -/
theorem rootQ_eq_iff_dvd_deltaB (e f : RootEdgeData) {ime imf : ZMod q}
    (hme : (e.mPrime : ZMod q) * ime = 1) (hmf : (f.mPrime : ZMod q) * imf = 1) :
    rootQ e.beta ime = rootQ f.beta imf ↔ (q : ℤ) ∣ deltaB e f :=
  Gate04Root.rootQ_eq_iff_dvd_deltaB e.toAffineEdgeData f.toAffineEdgeData hme hmf

/-- **`Δ_A = 0` collapses the base row**, and with a jump bound also fixes `r`. -/
theorem deltaA_zero_eq_base_row {e f : RootEdgeData}
    (hme : 0 < e.m) (hmf : 0 < f.m)
    (hce : IsCoprime e.alpha e.m) (hcf : IsCoprime f.alpha f.m)
    (h : deltaA e f = 0) (hlt : |e.r - f.r| < e.m) :
    e.m = f.m ∧ e.alpha = f.alpha ∧ e.r = f.r := by
  obtain ⟨hm, ha⟩ :=
    Gate04Root.deltaA_zero_eq_base_row (e := e.toAffineEdgeData) (f := f.toAffineEdgeData)
      hme hmf hce hcf h
  exact ⟨hm, ha, Gate04Root.r_eq_of_base_row_eq (e := e.toAffineEdgeData)
    (f := f.toAffineEdgeData) hm ha hce hlt⟩

/-- **`Δ_B = 0` collapses the shifted row.** -/
theorem deltaB_zero_eq_shifted_row {e f : RootEdgeData}
    (hme : 0 < e.mPrime) (hmf : 0 < f.mPrime)
    (hce : IsCoprime e.beta e.mPrime) (hcf : IsCoprime f.beta f.mPrime)
    (h : deltaB e f = 0) : e.mPrime = f.mPrime ∧ e.beta = f.beta :=
  Gate04Root.deltaB_zero_eq_shifted_row (e := e.toAffineEdgeData)
    (f := f.toAffineEdgeData) hme hmf hce hcf h

/-- The bridge to the standalone affine data is injective. -/
theorem rootEdge_eq_of_affine_eq :
    ∀ {e f : RootEdgeData}, e.toAffineEdgeData = f.toAffineEdgeData → e = f := by
  rintro ⟨er, em, ek, emp, ew, ea, eb, _, _, _⟩ ⟨fr, fm, fk, fmp, fw, fa, fb, _, _, _⟩ h
  simp only [RootEdgeData.toAffineEdgeData, Gate04Root.AffineEdgeData.mk.injEq] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  subst h1; subst h2; subst h3; subst h4; subst h5; subst h6; subst h7
  rfl

/-- **Double vanishing determinant rigidity**: `Δ_A = Δ_B = 0 ⟹ e = f`, for
rows with positive reduced denominators and nonzero (signed) jump. -/
theorem double_delta_zero_row_eq {e f : RootEdgeData}
    (hme : 0 < e.m) (hmf : 0 < f.m)
    (hmpe : 0 < e.mPrime) (hmpf : 0 < f.mPrime)
    (hce : IsCoprime e.alpha e.m) (hcf : IsCoprime f.alpha f.m)
    (hbe : IsCoprime e.beta e.mPrime) (hbf : IsCoprime f.beta f.mPrime)
    (hke : e.k ≠ 0)
    (hA : deltaA e f = 0) (hB : deltaB e f = 0) : e = f := by
  exact rootEdge_eq_of_affine_eq (Gate04Root.double_delta_zero_row_eq
    (e := e.toAffineEdgeData) (f := f.toAffineEdgeData)
    hme hmf hmpe hmpf hce hcf hbe hbf hke hA hB)

end Gate01Root
end RouteAFibreFrame
