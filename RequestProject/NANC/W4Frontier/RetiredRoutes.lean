import RequestProject.NANC.W4Frontier.Exponents

namespace TwinPrimeProject.NANC.W4Frontier

/-- The exponent loss in any argument that first separates the two pair
 discrepancies. -/
theorem decoupling_cauchy_loses_M :
    (2 * Mexp - Hexp) - CountScaleTargetExp = Mexp := by
  norm_num [CountScaleTargetExp]

/-- The same loss, measured relative to unsigned joint mass, is H. -/
theorem decoupling_loses_joint_rarity_H :
    (2 * Mexp - Hexp) - UnsignedJointMassExp = Hexp := by
  norm_num [UnsignedJointMassExp]

def decouplingCauchyStatus : BankStatus := .falseRoute

def pdsLSStatus : BankStatus := .retired
def oneSidedLargeSieveStatus : BankStatus := .retired
def schattenOperatorNormStatus : BankStatus := .retired
def marginalW2Status : BankStatus := .retired
def pobToMQWStatus : BankStatus := .retired
def zKuznetsovStatus : BankStatus := .retired
def positiveGCDCountStatus : BankStatus := .retired
def shortKOnlyStatus : BankStatus := .retired

end TwinPrimeProject.NANC.W4Frontier
