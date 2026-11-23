import RequestProject.REAL1B_20261122.FMGridExact
import RequestProject.REAL1B_20261122.FMProfileTransfer

namespace REAL1B.FM.Analytic
open Filter Vaughan Source Direct

/-- Gold 4.67. All distribution inputs refer to the indicated physical sum.
The outside-box inequality is an explicit independent arithmetic premise. -/
theorem infinite_of_analytic_estimates {a : Set.Ioo (0:ℝ) 1} {κ : ℝ} (hκ : 0 < κ)
    (hn : Profile.Normalization) (hledger : Ledger.Estimates)
    (hwhole : VaughanEstimates a Direct.phi) (hbox : VaughanEstimates a Direct.psi)
    (hmean : Profile.MeanDensity) (hrough : Profile.RoughDensity)
    (hout : OutsideBound a κ) : Set.Infinite {p : ℕ | p.Prime ∧ (p+2).Prime} := by
  have hs := Profile.scale_lower hn
  exact Grid.infinite_of_certified_profile hκ (Ledger.lower_of_estimates hledger hs)
    (reduction_of_estimates a.property.2 hs hwhole) (calibration_of_estimates a.property.2 hs hbox (Profile.mean_transfer hn hmean))
    (Profile.upper_of_rough_density hn hrough) hout (comparator_pos hs)

end REAL1B.FM.Analytic
#print axioms REAL1B.FM.Analytic.infinite_of_analytic_estimates
