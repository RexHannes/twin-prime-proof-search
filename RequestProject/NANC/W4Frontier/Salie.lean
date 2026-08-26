import RequestProject.NANC.W4Frontier.Basic

namespace TwinPrimeProject.NANC.W4Frontier

/-- External finite-field Salié identity. No global inhabitant is provided. -/
structure SalieIdentityInterface extends ConditionalInterface

/-- Shifted Salié identity. No global inhabitant is provided. -/
structure ShiftedSalieIdentityInterface extends ConditionalInterface

/-- Generic local-transform formula. No global inhabitant is provided. -/
structure LocalTransformInterface extends ConditionalInterface

/-- Weil classification of the complete w-correlation. -/
structure WCorrelationClassificationInterface extends ConditionalInterface

def salieIdentityStatus : BankStatus := .conditional
def shiftedSalieIdentityStatus : BankStatus := .conditional
def localTransformStatus : BankStatus := .conditional
def wCorrelationClassifiedStatus : BankStatus := .conditional

/-- The Salié rewrite clarifies the algebra but, after Cauchy and Weil, is
recorded as furnishing no exponent gain. This is a ledger status, not closure. -/
def salieLosslessGainless : LedgerItem :=
  ⟨"SALIE_LOSSLESS_GAINGLESS", .retired,
   "Algebraically useful; reproduces the original Weil scale and gives no saving."⟩

/-- Pure w-orthogonality is not banked: r=r' does not force m=m'. -/
def pureWOrthogonalityStatus : BankStatus := .falseRoute

end TwinPrimeProject.NANC.W4Frontier
