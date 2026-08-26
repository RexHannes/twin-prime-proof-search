import RequestProject.Options
namespace TwinPrimeProject.NANC

theorem same_r_count_ratio_exponent (a b : ℚ) :
    (1/3-a) - (a+2*b-2/3) = 1-2*a-2*b := by ring

theorem same_r_count_power_saving (a b κ : ℚ) (h : 5/9+κ ≤ a+b) :
    1-2*a-2*b ≤ -1/9-2*κ := by linarith

structure SameRFromPointwiseROW where
  pointwiseROW : Prop
  sameRClosed : Prop
  assemble : pointwiseROW → sameRClosed

theorem same_r_closed_from_pointwise_row (H : SameRFromPointwiseROW)
    (h : H.pointwiseROW) : H.sameRClosed := H.assemble h
end TwinPrimeProject.NANC
