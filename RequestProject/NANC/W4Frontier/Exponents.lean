import RequestProject.NANC.W4Frontier.Basic

namespace TwinPrimeProject.NANC.W4Frontier

abbrev Rexp : ℤ := 20
abbrev Mexp : ℤ := 24
abbrev Kexp : ℤ := 4
abbrev Lexp : ℤ := 25
abbrev Dexp : ℤ := 28
abbrev Uexp : ℤ := 27
abbrev Hexp : ℤ := 22
abbrev OldDeltaDeterminantRHSExp : ℤ := Mexp + Dexp
abbrev CorrectKDeterminantRHSExp : ℤ := Kexp + Dexp

example : Kexp + Rexp = Mexp := by norm_num
example : Hexp = 2 * Lexp - Dexp := by norm_num
example : Mexp - Hexp = 2 := by norm_num
example : 2 * (Mexp - Hexp) = 4 := by norm_num
example : 2 * Rexp > Mexp := by norm_num

/-- RETIRED_FALSE_GRAPH exponent: the old `2*delta*z` RHS had exponent 52. -/
theorem retiredDeltaDeterminantRHSExp_eq_fiftyTwo :
    OldDeltaDeterminantRHSExp = 52 := by norm_num

/-- The corrected `2*k*z` determinant RHS has exponent 32. -/
theorem correctKDeterminantRHSExp_eq_thirtyTwo :
    CorrectKDeterminantRHSExp = 32 := by norm_num

theorem edgeCountExp : Rexp + Mexp + Kexp = 2 * Mexp := by norm_num

def UnsignedJointMassExp : ℤ := 2 * Mexp + 2 * Dexp - 4 * Lexp
def CountScaleTargetExp : ℤ := Mexp - Hexp

theorem unsignedJointMassExp_eq_four : UnsignedJointMassExp = 4 := by
  norm_num [UnsignedJointMassExp]
theorem countScaleTargetExp_eq_two : CountScaleTargetExp = 2 := by
  norm_num [CountScaleTargetExp]

theorem unsigned_mass_is_target_square :
    2 * CountScaleTargetExp = UnsignedJointMassExp := by
  norm_num [CountScaleTargetExp, UnsignedJointMassExp]

/-- Dividing the kernel covariance target `M+H` by the normalization `2H`
leaves the count-scale target `M-H`. -/
theorem covariance_normalization_exp :
    (Mexp + Hexp) - 2 * Hexp = Mexp - Hexp := by ring

/-- The marginal Cauchy route is worse than the target by exactly one M-scale. -/
theorem decoupling_loss_exp :
    (2 * Mexp - Hexp) - (Mexp - Hexp) = Mexp := by ring

/-- Relative to unsigned joint mass, marginal Cauchy loses one H-scale. -/
theorem joint_rarity_loss_exp :
    (2 * Mexp - Hexp) - 2 * (Mexp - Hexp) = Hexp := by ring

end TwinPrimeProject.NANC.W4Frontier
