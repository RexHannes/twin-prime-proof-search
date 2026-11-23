import RequestProject.REAL1B_20261122.FMIntegral
import RequestProject.REAL1B_20261122.FMSemantics
import RequestProject.REAL1B_20261122.FMGridNumerals

namespace REAL1B.FM.Grid
theorem integral_enclosure : Direct.J ≤ Direct.enclosure := by
  calc
    _ ≤ (totalUpper:ℝ)/scale := integral_le_mesh
    _ = _ := by rw [total_upper_exact]; norm_num [scale, Direct.enclosure]

open Filter Source Direct

theorem infinite_of_certified_profile {a : Set.Ioo (0:ℝ) 1} {κ : ℝ} (hk : 0 < κ)
    (hl : Closing.LowerLedger) (hr : Closing.Reduction a)
    (hc : Calibration a) (hp : ProfileUpper) (ho : OutsideBound a κ)
    (hs : ∀ᶠ x : ℝ in atTop, 0 < Sb x) :
    Set.Infinite {p : ℕ | p.Prime ∧ (p+2).Prime} :=
  infinite_of_profile_and_outside hk hl hr hc hp integral_enclosure ho hs

end REAL1B.FM.Grid
#print axioms REAL1B.FM.Grid.integral_enclosure
#print axioms REAL1B.FM.Grid.infinite_of_certified_profile
