import RequestProject.Options
namespace TwinPrimeProject.NANC
structure CDVMixedCovarianceInput where mixedCovarianceBound : Prop
structure CDVClosureFromMixedCovariance (MixedCovariance CDVConclusion : Prop) where
  assemble : MixedCovariance → CDVConclusion

theorem cdv_closed_from_mixed_covariance {M C : Prop}
    (H : CDVClosureFromMixedCovariance M C) (h : M) : C := H.assemble h
end TwinPrimeProject.NANC
