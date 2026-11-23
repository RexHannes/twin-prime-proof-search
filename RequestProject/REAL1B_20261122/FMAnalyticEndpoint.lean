import RequestProject.REAL1B_20261122.FMGridExact
import RequestProject.REAL1B_20261122.FMProfileTransfer

namespace REAL1B.FM.Analytic
open Filter Vaughan Source Direct

/-- Gold 4.67. All distribution inputs refer to the indicated physical sum.
The outside-box inequality is an explicit independent arithmetic premise. -/
theorem infinite_of_analytic_estimates {a : Set.Ioo (0:ℝ) 1} {κ : ℝ} (hκ : 0 < κ)
    (hn : Profile.Normalization) (hledger : Ledger.Estimates)
    (hwhole : VaughanEstimates a Direct.phi) (hbox : VaughanEstimates a Direct.psi)
    (hmean : negligible (fun x => mean Direct.psi x - Direct.J * Sb x) Sb)
    (hH : ∀ᶠ x : ℝ in atTop, ∀ n ∈ interval (x/2), Closing.boxes n → 0 ≤ kernelH n)
    (hrough : ∀ e : ℝ, 0 < e → ∀ᶠ x : ℝ in atTop,
      Profile.roughProfile x ≤ cStar * J * Profile.reference x + e * Sb x)
    (hout : OutsideBound a κ) : Set.Infinite {p : ℕ | p.Prime ∧ (p+2).Prime} := by
  have hs := Profile.scale_lower hn
  have hψ : ∀ᶠ x : ℝ in atTop, ∀ n ∈ interval (x/2), 0 ≤ Direct.psi x n := by
    filter_upwards [hH,eventually_ge_atTop (4:ℝ)] with x hh hx n hw
    by_cases hb : Closing.boxes n
    · rw [box_phi_eq_H hx hw hb]
      exact hh n hw hb
    · simp [Direct.psi,hb]
  exact Grid.infinite_of_certified_profile hκ (Ledger.lower_of_estimates hledger hs)
    (reduction_of_estimates a.property.2 hs hwhole) (calibration_of_estimates a.property.2 hs hbox hmean)
    (Profile.profile_upper hn hψ hrough) hout (comparator_pos hs)

end REAL1B.FM.Analytic
#print axioms REAL1B.FM.Analytic.infinite_of_analytic_estimates
