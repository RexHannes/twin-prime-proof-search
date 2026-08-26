import RequestProject.Parameters

/-!
# Routing threshold `w*(μ)` (§6, §13.1)

In the fixed-depth fragmented routing theorem, a selected smooth residual block of
size `W_j = X^{w_j+o(1)}` becomes the outer window, and the residual modulus is
`Q_j = X / W_j = X^{1/2 + θ_j}` with `θ_j = 1/2 - w_j`.  The widened Wright wedge
`122μ + 162θ_j < 1` therefore becomes a *threshold condition on `w_j`*:

`122μ + 162θ_j < 1  ⟺  w_j > w*(μ)`,   where   `w*(μ) = (40 + 61μ)/81`.

This module machine-checks the routing-threshold equivalence, the definition of
`θ_j` from `w_j`, and the resulting characterization of routability.
-/

namespace ShiftedMobiusBank

/-- The routing threshold `w*(μ) = (40 + 61μ)/81`. -/
noncomputable def wStar (mu : ℝ) : ℝ := (40 + 61 * mu) / 81

/-- §13.1 — the routing-threshold equivalence in raw `(μ, w)` form:
`122μ + 162(1/2 - w) < 1  ⟺  w > (40 + 61μ)/81`. -/
theorem routing_threshold_equiv (mu w : ℝ) :
    122 * mu + 162 * (1 / 2 - w) < 1 ↔ w > wStar mu := by
  unfold wStar
  rw [gt_iff_lt, div_lt_iff₀ (by norm_num : (0:ℝ) < 81)]
  constructor <;> intro h <;> linarith

/-- The residual conductor exponent produced by selecting a block of size
`W_j = X^{w_j}`: `θ_j = 1/2 - w_j`. -/
noncomputable def thetaOfW (w : ℝ) : ℝ := 1 / 2 - w

/-- §13.1 — routability characterization via the `newWedge` predicate.  Building
the parameter point with `θ = 1/2 - w`, the widened wedge holds iff `w > w*(μ)`. -/
theorem newWedge_iff_wStar (mu w : ℝ) (hmu : 0 ≤ mu)
    (hθ : 0 ≤ thetaOfW w) :
    newWedge ⟨mu, thetaOfW w, hmu, hθ⟩ ↔ w > wStar mu := by
  unfold newWedge thetaOfW at *
  simpa using routing_threshold_equiv mu w

/-- The threshold is monotone increasing in `μ`: larger `μ` needs a longer smooth
block to route. -/
theorem wStar_mono {mu1 mu2 : ℝ} (h : mu1 ≤ mu2) : wStar mu1 ≤ wStar mu2 := by
  unfold wStar
  rw [div_le_div_iff_of_pos_right (by norm_num : (0:ℝ) < 81)]
  linarith

/-- At `μ = 0` the threshold is `40/81 < 1/2`: a block just below `X^{1/2}`
suffices to route when `M` is tiny. -/
theorem wStar_zero : wStar 0 = 40 / 81 := by unfold wStar; norm_num

theorem wStar_zero_lt_half : wStar 0 < 1 / 2 := by rw [wStar_zero]; norm_num

end ShiftedMobiusBank
