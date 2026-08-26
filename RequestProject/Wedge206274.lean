import RequestProject.Parameters

/-!
# The old `206μ + 274θ < 1` wedge (subsumed, preserved)

This module preserves the earlier machine-checked algebra for the first corrected
KF tiny wedge.  It is *subsumed* by `Wedge122162` (see
`wedge_containment_206_implies_122`), but retained per §12.3 of the master task.
-/

namespace ShiftedMobiusBank

/-- The old wedge implies the previously audited cross-coprime exponent
condition `148μ + 158θ < 1`. -/
theorem oldWedge_implies_cross_coprime (p : Params) (h : oldWedge p) :
    148 * p.mu + 158 * p.theta < 1 := by
  have hmu := p.mu_nonneg
  have htheta := p.theta_nonneg
  unfold oldWedge at h; linarith

/-- Exact feasibility equivalence for the *old* splitting parameter: there is a
`σ` with `2μ + 4θ < σ` and `148μ + 158θ + 29σ < 1` iff `206μ + 274θ < 1`. -/
theorem oldWedge_sigma_feasible_iff (mu theta : ℝ) :
    (∃ sigma : ℝ,
      2 * mu + 4 * theta < sigma ∧
      148 * mu + 158 * theta + 29 * sigma < 1) ↔
    206 * mu + 274 * theta < 1 := by
  constructor
  · rintro ⟨sigma, hlower, hupper⟩; linarith
  · intro h
    refine ⟨(2 * mu + 4 * theta + (1 - 148 * mu - 158 * theta) / 29) / 2, ?_, ?_⟩
    · linarith
    · linarith

/-- The concrete point quoted in the original prompt lies in the old wedge. -/
theorem oldWedge_concrete_point :
    206 * (1 / 400 : ℚ) + 274 * (1 / 10000 : ℚ) < 1 := by norm_num

/-- The decimal value quoted in the original prompt is exactly `339/625 = 0.5424`. -/
theorem oldWedge_concrete_value :
    206 * (1 / 400 : ℚ) + 274 * (1 / 10000 : ℚ) = 339 / 625 := by norm_num

end ShiftedMobiusBank
