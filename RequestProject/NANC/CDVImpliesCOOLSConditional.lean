import RequestProject.Options
namespace TwinPrimeProject.NANC

theorem cdv_hs_implies_cools_ratio (b : ℚ) : 1/2*(1/3)-b = 1/6-b := by ring

theorem cdv_hs_beats_cools_highP3 (b : ℚ) (hb : 5/18 ≤ b) : 1/6-b ≤ -1/9 := by linarith
end NANC
