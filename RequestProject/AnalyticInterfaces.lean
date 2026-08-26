import RequestProject.TwinPrimeDefinitions

namespace TwinPrimeProject

/-- All unproved analytic claims are fields of an explicit assumption package,
never global axioms. Downstream results must accept the relevant proof fields.
The historical field for Type I is retained compatibly; its ledger status is now
`EXTERNALLY_AUDITED`, while the other fields keep their prior status. -/
structure AnalyticOpenInputs where
  ResidueAwarePrimeMass : Prop
  residueAwarePrimeMass : ResidueAwarePrimeMass
  FordB1ResidueAware : Prop
  fordB1ResidueAware : FordB1ResidueAware
  FordB2ResidueAware : Prop
  fordB2ResidueAware : FordB2ResidueAware
  ResidueAwareFordTypeI : Prop
  residueAwareFordTypeI : ResidueAwareFordTypeI
  FordMaynardSparseComparisonTransference : Prop
  fordMaynardSparseComparisonTransference : FordMaynardSparseComparisonTransference
  CenteredShiftedPrimeTypeII : Prop
  centeredShiftedPrimeTypeII : CenteredShiftedPrimeTypeII
  HeathBrownSieveGlobalCentering : Prop
  heathBrownSieveGlobalCentering : HeathBrownSieveGlobalCentering

/-- An explicit externally supplied result. Creating this record requires a proof
of its statement; the record itself does not kernel-prove the analytic theorem. -/
structure ExternallyAuditedAnalyticInput where
  statement : Prop
  proof : statement
  rangeDescription : String
  dependencies : List String

/-- Explicit input for the residue-aware Ford Type-I estimate. The audited range
is every fixed `γ < 1/2`, equivalently `m ≤ x^(1/2-ε)` for fixed `ε > 0`. -/
abbrev ResidueAwareFordTypeIInput := ExternallyAuditedAnalyticInput

/-- Explicit input for divisor-weighted maximal Bombieri--Vinogradov. -/
abbrev DivisorWeightedMaximalBVInput := ExternallyAuditedAnalyticInput

/-- Explicit input for the interval-uniform dimension-one rough sieve. -/
abbrev IntervalUniformResidueSieveInput := ExternallyAuditedAnalyticInput

/-- Explicit input for matching the large-prime local-factor tail in Type I. -/
abbrev TypeILargePrimeTailInput := ExternallyAuditedAnalyticInput

/-- Explicit input for the even-modulus branch of Type I. -/
abbrev TypeIEvenModulusBranchInput := ExternallyAuditedAnalyticInput

/-- Transparent accessor for an explicitly supplied Type-I result. No analytic
theorem is kernel-proved by this accessor or by creating its record type. -/
theorem useResidueAwareFordTypeI (h : ResidueAwareFordTypeIInput) : h.statement :=
  h.proof

/-- The exact K=3 Heath--Brown identity remains source-pending. -/
structure HeathBrownK3IdentityInterface where
  verifiedRangeAndIdentity : Prop
  proof : verifiedRangeAndIdentity

end TwinPrimeProject
