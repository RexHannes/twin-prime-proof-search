import RequestProject.Status
import RequestProject.HighP3Status

namespace TwinPrimeProject

abbrev ProofStatus := ShiftedMobiusBank.ProofStatus
abbrev LedgerEntry := ShiftedMobiusBank.LedgerEntry

/-- Current status of the residue-aware Type-I analytic estimate. -/
def residueAwareFordTypeIStatus : ProofStatus := .externallyAudited

/-- The clean exponent-one-half endpoint has not been audited. -/
def fordTypeIExactHalfEndpointStatus : ProofStatus := .openInput

/-- Authoritative corrective Vaughan/high-P3 ledger, using the restricted trust
taxonomy of the corrective update. -/
def correctiveVaughanHighP3Status := highP3CorrectiveLedger

/-- Secondary prose label for the externally audited Type-I result. -/
def residueAwareFordTypeISecondaryLabel : String := "PROVED_MODULO_CLASSICAL_BV"

/-- Conservative status registry for the residue-aware comparison development. -/
def statusLedger : List LedgerEntry :=
  [ ⟨"TwinPrimeWeightedDetector", .leanProvedCore, none⟩
  , ⟨"OddPrimorial", .leanProvedCore, none⟩
  , ⟨"ResidueAwareComparisonCandidate", .leanProvedCore, none⟩
  , ⟨"CenteredCandidateDifference", .leanProvedCore, none⟩
  , ⟨"ResidueAwareNonnegative", .leanProved, none⟩
  , ⟨"ResidueAwareSupport", .leanProved, none⟩
  , ⟨"ResidueAwareEvenVanishing", .leanProved, none⟩
  , ⟨"ResidueAwarePointwiseBound", .conditionalInterface, none⟩
  , ⟨"ShiftedCongruenceIfCoprime", .leanProved, none⟩
  , ⟨"ShiftedCongruenceVacuousOnDivisor", .leanProved, none⟩
  , ⟨"ResidueAwareLocalRule", .leanProved, none⟩
  , ⟨"FiniteLocalDensityIdentity", .leanProved, none⟩
  , ⟨"ResidueAwareDensityFactor", .leanProvedCore, none⟩
  , ⟨"LocalDensityOne", .leanProved, none⟩
  , ⟨"LocalDensityEvenZero", .leanProved, none⟩
  , ⟨"LocalDensityPrime", .leanProved, none⟩
  , ⟨"LocalDensityPrimePower", .leanProved, none⟩
  , ⟨"LocalDensityDependsOnRadical", .leanProved, none⟩
  , ⟨"TotientLocalFactorSplit", .conditionalInterface, none⟩
  , ⟨"LargePrimeDivisorCount", .leanProved, none⟩
  , ⟨"LargePrimeReciprocalTail", .leanProved, none⟩
  , ⟨"TwinPrimeFiniteEulerFactor", .leanProved, none⟩
  , ⟨"W0DivV0Identity", .leanProved, none⟩
  , ⟨"FiniteTwinPrimeSingularSeries", .leanProved, none⟩
  , ⟨"InfiniteTwinPrimeProductConvergence", .openInput, none⟩
  , ⟨"WeightedTwinPrimeCountDecomposition", .conditionalInterface, none⟩
  , ⟨"PrimePowerContaminationBound", .openInput, none⟩
  , ⟨"HeathBrownK3IdentityInterface", .sourcePending, none⟩
  , ⟨"ResidueAwarePrimeMass", .openInput, none⟩
  , ⟨"FordB1ResidueAware", .openInput, none⟩
  , ⟨"FordB2ResidueAware", .openInput, none⟩
  , ⟨"RESIDUE_AWARE_FORD_TYPE_I", .externallyAudited,
      some "ResidueAwareFordTypeI (was OPEN_INPUT)"⟩
  , ⟨"DIVISOR_WEIGHTED_MAXIMAL_BV", .externallyAudited, none⟩
  , ⟨"INTERVAL_UNIFORM_RESIDUE_SIEVE", .externallyAudited, none⟩
  , ⟨"TYPE_I_LARGE_PRIME_TAIL", .externallyAudited, none⟩
  , ⟨"TYPE_I_EVEN_MODULUS_BRANCH", .externallyAudited, none⟩
  , ⟨"FORD_TYPE_I_EXACT_HALF_ENDPOINT", .openInput, none⟩
  , ⟨"FordMaynardSparseComparisonTransference", .openInput, none⟩
  , ⟨"CenteredShiftedPrimeTypeII", .openInput, none⟩
  , ⟨"HeathBrownSieveGlobalCentering", .openInput, none⟩
  , ⟨"ConstantTwinComparisonModel", .refuted, none⟩
  , ⟨"ShiftedMobiusIsFordTypeII", .superseded, none⟩
  ]

end TwinPrimeProject
