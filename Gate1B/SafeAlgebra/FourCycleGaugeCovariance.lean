/-
# Gate 1B v14 — four-cycle gauge covariance and the cross-ratio normal form

**Status: exact algebra, all PROVED.  Source-independent.**

The four-cycle data `(a₁,a₂,a₃,a₄; h₁,h₂,h₃,h₄)` carries a gauge action

    a_j ↦ c_j c_{j+1} a_j        (indices cyclic),
    h_j ↦ c_j h_j.

Under it the trace scales by `C = c₁c₂c₃c₄`, the determinant and the
discriminant by `C²`:

* `fourCycle_trace_gauge`, `fourCycle_det_gauge`, `fourCycleDisc_gauge`.

Consequently the cross-ratio `κ = a₁a₃/(a₂a₄)` is gauge invariant
(`crossRatio_gauge_invariant`), and over a field every multiplier tuple with
`a₁,a₂,a₃ ≠ 0` is gauge equivalent to the normal form `(1,1,1,κ⁻¹)`
(`gauge_normal_form`).  The construction is explicit and uses **no square
roots**.
-/
import Gate1B.SafeAlgebra.MovingMultiplierFourCycle

namespace Gate1B.SafeAlgebra

section Gauge

variable {R : Type*} [CommRing R]

/-- **Gauge covariance of the trace**: the four-cycle trace scales by
`C = c₁c₂c₃c₄`. -/
theorem fourCycle_trace_gauge (A1 A2 A3 A4 H1 H2 H3 H4 c1 c2 c3 c4 : R) :
    Matrix.trace (cycleMatrix (c1 * c2 * A1) (c2 * c3 * A2) (c3 * c4 * A3) (c4 * c1 * A4)
        (c1 * H1) (c2 * H2) (c3 * H3) (c4 * H4))
      = (c1 * c2 * c3 * c4) * Matrix.trace (cycleMatrix A1 A2 A3 A4 H1 H2 H3 H4) := by
  rw [fourCycle_trace, fourCycle_trace]
  ring

/-- **Gauge covariance of the determinant**: it scales by `C²`. -/
theorem fourCycle_det_gauge (A1 A2 A3 A4 H1 H2 H3 H4 c1 c2 c3 c4 : R) :
    Matrix.det (cycleMatrix (c1 * c2 * A1) (c2 * c3 * A2) (c3 * c4 * A3) (c4 * c1 * A4)
        (c1 * H1) (c2 * H2) (c3 * H3) (c4 * H4))
      = (c1 * c2 * c3 * c4) ^ 2 * Matrix.det (cycleMatrix A1 A2 A3 A4 H1 H2 H3 H4) := by
  rw [fourCycle_det, fourCycle_det]
  ring

/-- **Gauge covariance of the discriminant**: it scales by `C²`. -/
theorem fourCycleDisc_gauge (A1 A2 A3 A4 H1 H2 H3 H4 c1 c2 c3 c4 : R) :
    fourCycleDisc (c1 * c2 * A1) (c2 * c3 * A2) (c3 * c4 * A3) (c4 * c1 * A4)
        (c1 * H1) (c2 * H2) (c3 * H3) (c4 * H4)
      = (c1 * c2 * c3 * c4) ^ 2 * fourCycleDisc A1 A2 A3 A4 H1 H2 H3 H4 := by
  unfold fourCycleDisc
  rw [fourCycle_trace_gauge, fourCycle_det_gauge, fourCycle_trace, fourCycle_det]
  ring

end Gauge

section CrossRatio

variable {K : Type*} [Field K]

/-- The gauge-invariant cross-ratio of the four multipliers. -/
def crossRatio (a1 a2 a3 a4 : K) : K := a1 * a3 / (a2 * a4)

/-- **Gauge invariance of the cross-ratio.** -/
theorem crossRatio_gauge_invariant (A1 A2 A3 A4 c1 c2 c3 c4 : K)
    (hc1 : c1 ≠ 0) (hc2 : c2 ≠ 0) (hc3 : c3 ≠ 0) (hc4 : c4 ≠ 0) :
    crossRatio (c1 * c2 * A1) (c2 * c3 * A2) (c3 * c4 * A3) (c4 * c1 * A4)
      = crossRatio A1 A2 A3 A4 := by
  unfold crossRatio
  have hC : c1 * c2 * c3 * c4 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero hc1 hc2) hc3) hc4
  rw [show c1 * c2 * A1 * (c3 * c4 * A3) = (c1 * c2 * c3 * c4) * (A1 * A3) by ring,
    show c2 * c3 * A2 * (c4 * c1 * A4) = (c1 * c2 * c3 * c4) * (A2 * A4) by ring]
  exact mul_div_mul_left _ _ hC

/-- **Gauge normal form.**  If `a₁, a₂, a₃ ≠ 0` there is an explicit gauge
(without square roots) taking the multipliers to `(1, 1, 1, κ⁻¹)`, where
`κ = a₁a₃/(a₂a₄)`. -/
theorem gauge_normal_form (a1 a2 a3 a4 : K) (h1 : a1 ≠ 0) (h2 : a2 ≠ 0) (h3 : a3 ≠ 0) :
    ∃ c1 c2 c3 c4 : K, c1 ≠ 0 ∧ c2 ≠ 0 ∧ c3 ≠ 0 ∧ c4 ≠ 0 ∧
      a1 = c1 * c2 * 1 ∧ a2 = c2 * c3 * 1 ∧ a3 = c3 * c4 * 1 ∧
      a4 = c4 * c1 * (a2 * a4 / (a1 * a3)) := by
  refine ⟨a1, 1, a2, a3 / a2, h1, one_ne_zero, h2, div_ne_zero h3 h2, by ring, by ring, ?_, ?_⟩
  · field_simp
  · field_simp

end CrossRatio

end Gate1B.SafeAlgebra
