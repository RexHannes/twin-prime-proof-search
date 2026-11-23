import RequestProject.REAL1B_20261122.FMGridExact
import RequestProject.REAL1B_20261122.FMProfileSlices
import RequestProject.REAL1B_20261122.FMNormalization

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


/-- Each Type-I bound includes both original subtractions. The squareful payments
are proved for every positive presieve exponent, on the complete and boxed outputs. -/
theorem infinite_of_signed_estimates {a : Set.Ioo (0:ℝ) 1} {κ : ℝ} (hκ : 0<κ)
    (hn : Normalization.ShiftedPrimeEstimate) (hl : Ledger.Estimates)
    (hi : negligible (fun x => typeI a x (phi x) - mean phi x) scale)
    (hs : negligible (fun x => shortProduct a x (phi x)) scale)
    (hib : negligible (fun x => typeI a x (psi x) - mean psi x) scale)
    (hsb : negligible (fun x => shortProduct a x (psi x)) scale)
    (hm : ∀ j, negligible (fun x => H2.series*Profile.countTest (fun _ => 1) x j -
      Profile.sliceIntegral j*Profile.reference x) scale)
    (hr : ∀ j, ∀ e : ℝ, 0<e → ∀ᶠ x : ℝ in atTop,
      Profile.roughTest x j ≤ (cStar*Profile.sliceIntegral j+e)*Profile.reference x)
    (hout : OutsideBound a κ) : Set.Infinite {p : ℕ | p.Prime ∧ (p+2).Prime} := by
  have hnorm := Normalization.normalized_of_shifted_primes hn
  have hscale := Profile.scale_lower hnorm
  apply infinite_of_analytic_estimates hκ hnorm hl _ _ (Profile.mean_of_unit_counts hm)
    (Profile.rough_of_unit_counts hr) hout
  · exact ⟨negligible_comparator hi hscale,negligible_comparator hs hscale,
      Squareful.native_squareful a.property.1 hscale⟩
  · exact ⟨negligible_comparator hib hscale,negligible_comparator hsb hscale,
      Squareful.box_squareful a.property.1 hscale⟩

end REAL1B.FM.Analytic
#print axioms REAL1B.FM.Analytic.infinite_of_analytic_estimates
#print axioms REAL1B.FM.Analytic.infinite_of_signed_estimates
