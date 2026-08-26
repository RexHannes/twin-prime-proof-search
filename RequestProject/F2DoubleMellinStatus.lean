import Mathlib

/-! Status-only interface for the F2 prime/unit double-Mellin reduction.

The exact Sol-corrected formula was not included in the task materials or prior
project ledger, so this file does not fabricate one. It records the excluded
strata and an explicit conditional reduction shape only. -/

namespace ShiftedMobiusBank

structure F2ExcludedStrata where
  principalCharacters : Prop
  nonunits : Prop
  equalPrimes : Prop
  primePowers : Prop
  repeatedPrimes : Prop
  gcdStrata : Prop

structure F2PrimeUnitClaims where
  originalPrimeUnit : Prop
  doubleMellinNN : Prop
  excluded : F2ExcludedStrata

/-- `PROVISIONAL_REDUCTION`: a supplied exact finite expansion may provide the
prime/unit NN formula; this declaration does not assert that input. -/
theorem F2_DOUBLE_MELLIN_PRIME_UNIT (C : F2PrimeUnitClaims)
    (exactFiniteExpansion : C.originalPrimeUnit → C.doubleMellinNN)
    (h : C.originalPrimeUnit) : C.doubleMellinNN := exactFiniteExpansion h

end ShiftedMobiusBank
