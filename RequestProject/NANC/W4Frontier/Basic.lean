import RequestProject.NANC.Status

namespace TwinPrimeProject.NANC.W4Frontier

/-- The W4 supplement reuses the project's authoritative status type. -/
abbrev BankStatus := TwinPrimeProject.NANC.TrustStatus

/-- An honest proof-carrying interface for facts proved outside this Lean bank. -/
structure ConditionalInterface where
  statement : Prop
  proof : statement

/-- Use of an external fact always requires an explicit interface value. -/
theorem ConditionalInterface.use (h : ConditionalInterface) : h.statement := h.proof

/-- A named ledger item, which need not assert its mathematical description. -/
structure LedgerItem where
  label : String
  status : BankStatus
  description : String
  deriving Repr

end TwinPrimeProject.NANC.W4Frontier
