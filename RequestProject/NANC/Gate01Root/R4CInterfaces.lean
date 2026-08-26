import Gate04Root.R4CInterfaces
import RequestProject.NANC.Gate01Root.MatrixFourthMoment

/-!
# Gate01Root: the R4C finite implication

`R4CBound B T` is the finite hypothesis `fourthMoment B ≤ T²`.  We bank the
implications

* `r4c_implies_testVector_bound` : `∑_e |∑_p B e p x p|² ≤ T ∑_p |x p|²`;
* `r4c_implies_MDL2_bound` : with `T = M D L` and `∑_p |b p|² ≤ L`,
  `‖B b‖² ≤ M D L²`;
* `MDL2_eq_ML4_div_H` : `M D L² = M L⁴ / H` when `D H = L²`;
* `r4c_implies_avgCov_scale` : the combination.

**This proves only conditional implications; R4C itself is never proved.**
-/

namespace RouteAFibreFrame
namespace Gate01Root

variable {E P : Type*} [Fintype E] [Fintype P]

/-- The squared `ℓ²`-norm of a finite complex vector. -/
noncomputable def nsq {ι : Type*} [Fintype ι] (f : ι → ℂ) : ℝ := Gate04Root.nsq f

/-- The image vector `B x`. -/
noncomputable def applyB (B : E → P → ℂ) (x : P → ℂ) : E → ℂ := Gate04Root.applyB B x

/-- **R4C hypothesis** `tr((B Bᴴ)²) ≤ T²`. -/
def R4CBound (B : E → P → ℂ) (T : ℝ) : Prop := fourthMoment B ≤ T ^ 2

theorem R4CBound_iff (B : E → P → ℂ) (T : ℝ) : R4CBound B T ↔ Gate04Root.R4CBound B T :=
  Iff.rfl

/-- **R4C ⇒ test-vector bound.** -/
theorem r4c_implies_testVector_bound {B : E → P → ℂ} {T : ℝ} (hT : 0 ≤ T)
    (hR : R4CBound B T) (x : P → ℂ) : nsq (applyB B x) ≤ T * nsq x :=
  Gate04Root.r4c_implies_testVector_bound hT hR x

/-- **R4C ⇒ operator bound**: `T` dominates the squared operator norm. -/
theorem r4c_implies_operator_bound {B : E → P → ℂ} {T : ℝ} (hT : 0 ≤ T)
    (hR : R4CBound B T) : Gate04Root.OpNormSqBound B T :=
  Gate04Root.r4c_implies_operator_bound hT hR

/-- **R4C at the scale `T = M D L`.** -/
theorem r4c_implies_MDL2_bound {B : E → P → ℂ} {M D L : ℝ}
    (hM : 0 ≤ M) (hD : 0 ≤ D) (hL : 0 ≤ L)
    (hR : R4CBound B (M * D * L)) {b : P → ℂ} (hb : nsq b ≤ L) :
    nsq (applyB B b) ≤ M * D * L ^ 2 :=
  Gate04Root.r4c_implies_MDL2_bound hM hD hL hR hb

/-- `M D L² = M L⁴ / H` under `D H = L²`. -/
theorem MDL2_eq_ML4_div_H {M D L H : ℝ} (hH : H ≠ 0) (hDH : D * H = L ^ 2) :
    M * D * L ^ 2 = M * L ^ 4 / H :=
  Gate04Root.MDL2_eq_ML4_div_H hH hDH

/-- `(M D L)² = M² L⁶ / H²` under `D H = L²`. -/
theorem MDL_sq_eq_M2L6_div_H2 {M D L H : ℝ} (hH : H ≠ 0) (hDH : D * H = L ^ 2) :
    (M * D * L) ^ 2 = M ^ 2 * L ^ 6 / H ^ 2 :=
  Gate04Root.MDL_sq_eq hH hDH

/-- **Average covariance scale** (conditional on R4C). -/
theorem r4c_implies_avgCov_scale {B : E → P → ℂ} {M D L H : ℝ}
    (hM : 0 ≤ M) (hD : 0 ≤ D) (hL : 0 ≤ L) (hH : H ≠ 0) (hDH : D * H = L ^ 2)
    (hR : R4CBound B (M * D * L)) {b : P → ℂ} (hb : nsq b ≤ L) :
    nsq (applyB B b) ≤ M * L ^ 4 / H :=
  Gate04Root.r4c_implies_avgCov_scale hM hD hL hH hDH hR hb

end Gate01Root
end RouteAFibreFrame
