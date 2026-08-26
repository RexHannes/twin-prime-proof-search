import RequestProject.Options
namespace TwinPrimeProject.NANC

inductive TrustStatus where
  | leanProved
  | leanProvedReduction
  | externallyAudited
  | provedModuloSource
  | conditionalInterface
  | openInput
  | auditedFailedRoute
  | falseRetired
  -- Fine-grained labels used by the W4 frontier supplement.
  | provedFinite
  | provedAlgebraic
  | conditional
  | open
  | retired
  | falseRoute
deriving DecidableEq, Repr
end TwinPrimeProject.NANC
