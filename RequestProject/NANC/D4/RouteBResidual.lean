import RequestProject.NANC.D4.Prop44Census27

namespace NANC.D4

def RouteBResidual (η ε u v l : ℚ) : Prop :=
  HighP3Atomic η u v l ∧ ¬ RouteBClosed12 η ε u v l

theorem routeB_closed_or_residual {η ε u v l : ℚ}
    (hhigh : HighP3Atomic η u v l) :
    RouteBClosed12 η ε u v l ∨ RouteBResidual η ε u v l := by
  by_cases h : RouteBClosed12 η ε u v l
  · exact Or.inl h
  · exact Or.inr ⟨hhigh, h⟩

theorem routeB_closed_residual_disjoint {η ε u v l : ℚ}
    (hc : RouteBClosed12 η ε u v l) (hr : RouteBResidual η ε u v l) : False := hr.2 hc

def BalancedRhoPacket (α u v : ℚ) : Prop := u = α/2 ∧ v = α/2

set_option maxHeartbeats 1000000 in
theorem feasible_implies_min_le_one_ninth
    {η ε u v l : ℚ} (hη0 : 0 ≤ η) (hηsmall : η ≤ 1/100) (hε : 0 ≤ ε)
    (hclosed : RouteBClosed12 η ε u v l) : min u v ≤ 1/9 := by
  simp only [RouteBClosed12] at hclosed
  rcases hclosed with h|h|h|h|h|h|h|h|h|h|h|h
  · rw [min_le_iff]; left; linarith [h.2.1]
  · rw [min_le_iff]; right; linarith [h.2.1]
  · rw [min_le_iff]; left; linarith [h.2.1]
  · rw [min_le_iff]; right; linarith [h.2.1]
  · simp only [Cell132j2] at h; rw [min_le_iff]; right; rcases h.1 with ⟨hu,hv,huv,hl,hs⟩; linarith [h.2.2.2]
  · simp only [Cell312j2] at h; rw [min_le_iff]; left; rcases h.1 with ⟨hu,hv,huv,hl,hs⟩; linarith [h.2.2.2]
  · rw [min_le_iff]; left; rcases h.1 with ⟨hu,hv,huv,hl,hs⟩; linarith [h.2.1]
  · rw [min_le_iff]; right; rcases h.1 with ⟨hu,hv,huv,hl,hs⟩; linarith [h.2.1]
  · rw [min_le_iff]; right; rcases h.1 with ⟨hu,hv,huv,hl,hs⟩; linarith [h.2.2.1]
  · rw [min_le_iff]; left; rcases h.1 with ⟨hu,hv,huv,hl,hs⟩; linarith [h.2.2.1]
  · rw [min_le_iff]; right; linarith [h.2.2.1]
  · rw [min_le_iff]; left; linarith [h.2.2.1]

theorem min_gt_one_ninth_is_residual
    {η ε u v l : ℚ} (hη0 : 0 ≤ η) (hηsmall : η ≤ 1/100) (hε : 0 ≤ ε)
    (hhigh : HighP3Atomic η u v l) (hmin : 1/9 < min u v) :
    RouteBResidual η ε u v l := by
  refine ⟨hhigh, fun hc => ?_⟩
  linarith [feasible_implies_min_le_one_ninth hη0 hηsmall hε hc]


set_option maxHeartbeats 1000000 in
theorem balanced_highP3_packet_residual
    {η ε α l u v : ℚ} (hη0 : 0 ≤ η) (hηsmall : η ≤ 1/100) (hε : 0 ≤ ε)
    (hα : 5/18-η/2 ≤ α) (hl : 5/18-η/2 ≤ l) (hsum : α+l ≤ 1)
    (hbal : BalancedRhoPacket α u v) : RouteBResidual η ε u v l := by
  have ha : 1/9 < α/2 := by linarith
  have hh : HighP3Atomic η u v l := by
    rcases hbal with ⟨rfl,rfl⟩
    refine ⟨by linarith, by linarith, ?_, hl, ?_⟩
    · linarith
    · linarith
  apply min_gt_one_ninth_is_residual hη0 hηsmall hε hh
  rw [hbal.1, hbal.2, min_self]
  exact ha

theorem every_highP3_fibre_contains_residual
    {η ε α l : ℚ} (hη0 : 0 ≤ η) (hηsmall : η ≤ 1/100) (hε : 0 ≤ ε)
    (hα : 5/18-η/2 ≤ α) (hl : 5/18-η/2 ≤ l) (hsum : α+l ≤ 1) :
    ∃ u v, u+v=α ∧ RouteBResidual η ε u v l := by
  refine ⟨α/2, α/2, by ring, ?_⟩
  exact balanced_highP3_packet_residual hη0 hηsmall hε hα hl hsum ⟨rfl,rfl⟩

end NANC.D4
