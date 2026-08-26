import RequestProject.Parameters

/-!
# The widened `122μ + 162θ < 1` wedge and its splitting parameter

All statements here are elementary real inequalities, machine-checked with
`linarith`/`ring`.  They formalise §12.1 and §12.2 of the master task: the
containment of the old wedge in the new one, and the full list of consequences of
the splitting exponent `σ`.
-/

namespace ShiftedMobiusBank

/-- §12.1 — wedge containment.  The old wedge is a *strict subset* of the new
one: `206μ + 274θ < 1` implies `122μ + 162θ < 1` for nonnegative exponents.
The converse is deliberately not stated (it is false). -/
theorem wedge_containment_206_implies_122 (p : Params) (h : oldWedge p) :
    newWedge p := by
  have hmu := p.mu_nonneg
  have htheta := p.theta_nonneg
  unfold oldWedge newWedge at *
  linarith

/-- §12.2 — the gap is positive inside the new wedge. -/
theorem gap_pos (p : Params) (h : newWedge p) : 0 < gap p := by
  unfold newWedge gap at *; linarith

/-- §12.2 — the splitting exponent exceeds the trivial floor `2μ + 4θ`. -/
theorem sigma_gt_floor (p : Params) (h : newWedge p) :
    2 * p.mu + 4 * p.theta < sigmaSplit p := by
  have := gap_pos p h
  unfold sigmaSplit; linarith

/-- §12.2 — `52μ + 62θ + 5σ < 1`. -/
theorem ineq_52_62_5sigma (p : Params) (h : newWedge p) :
    52 * p.mu + 62 * p.theta + 5 * sigmaSplit p < 1 := by
  have hmu := p.mu_nonneg
  have htheta := p.theta_nonneg
  unfold sigmaSplit gap; unfold newWedge at h; linarith

/-- §12.2 — `108μ + 158θ < 1`. -/
theorem ineq_108_158 (p : Params) (h : newWedge p) :
    108 * p.mu + 158 * p.theta < 1 := by
  have hmu := p.mu_nonneg
  have htheta := p.theta_nonneg
  unfold newWedge at h; linarith

/-- §12.2 — `120μ + 158θ + σ < 1`. -/
theorem ineq_120_158_sigma (p : Params) (h : newWedge p) :
    120 * p.mu + 158 * p.theta + sigmaSplit p < 1 := by
  have := gap_pos p h
  unfold sigmaSplit gap; unfold newWedge at h; linarith

/-- §12.2 — `8μ + 14θ < 1`. -/
theorem ineq_8_14 (p : Params) (h : newWedge p) :
    8 * p.mu + 14 * p.theta < 1 := by
  have hmu := p.mu_nonneg
  have htheta := p.theta_nonneg
  unfold newWedge at h; linarith

/-- §12.2 — `2μ + 2θ + 1/50 < 1`. -/
theorem ineq_2_2_fiftieth (p : Params) (h : newWedge p) :
    2 * p.mu + 2 * p.theta + 1 / 50 < 1 := by
  have hmu := p.mu_nonneg
  have htheta := p.theta_nonneg
  unfold newWedge at h; linarith

/-- §12.2 — `3μ + 4θ < 1/2`. -/
theorem ineq_3_4_half (p : Params) (h : newWedge p) :
    3 * p.mu + 4 * p.theta < 1 / 2 := by
  have hmu := p.mu_nonneg
  have htheta := p.theta_nonneg
  unfold newWedge at h; linarith

/-- §12.2 — the fixed-factor exponent *identity*
`2σ + 2μ = 1/5 - (92/5)μ - (122/5)θ`. -/
theorem fixed_factor_identity (p : Params) :
    2 * sigmaSplit p + 2 * p.mu
      = 1 / 5 - (92 / 5) * p.mu - (122 / 5) * p.theta := by
  unfold sigmaSplit gap; ring

/-- §12.2 — the fixed-factor exponent bound `2σ + 2μ ≤ 1/5`. -/
theorem fixed_factor_le (p : Params) :
    2 * sigmaSplit p + 2 * p.mu ≤ 1 / 5 := by
  have hmu := p.mu_nonneg
  have htheta := p.theta_nonneg
  rw [fixed_factor_identity]; linarith

/-- Bundle: every §12.2 consequence holds simultaneously inside the new wedge. -/
theorem splitting_parameter_122_162 (p : Params) (h : newWedge p) :
    0 < gap p ∧
    2 * p.mu + 4 * p.theta < sigmaSplit p ∧
    52 * p.mu + 62 * p.theta + 5 * sigmaSplit p < 1 ∧
    108 * p.mu + 158 * p.theta < 1 ∧
    120 * p.mu + 158 * p.theta + sigmaSplit p < 1 ∧
    8 * p.mu + 14 * p.theta < 1 ∧
    2 * p.mu + 2 * p.theta + 1 / 50 < 1 ∧
    3 * p.mu + 4 * p.theta < 1 / 2 ∧
    2 * sigmaSplit p + 2 * p.mu ≤ 1 / 5 :=
  ⟨gap_pos p h, sigma_gt_floor p h, ineq_52_62_5sigma p h, ineq_108_158 p h,
    ineq_120_158_sigma p h, ineq_8_14 p h, ineq_2_2_fiftieth p h,
    ineq_3_4_half p h, fixed_factor_le p⟩

/-- Concrete nonempty point of the widened wedge (`μ = 1/400`, `θ = 1/10000`),
inherited from the old wedge point. -/
theorem concrete_point_new_wedge :
    122 * (1 / 400 : ℚ) + 162 * (1 / 10000 : ℚ) < 1 := by norm_num

end ShiftedMobiusBank
