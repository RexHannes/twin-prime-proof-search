import Mathlib

/-! Principal-sector and reciprocal-tensor dependency interfaces. -/

namespace ShiftedMobiusBank

structure F2SectorClaims where
  primeUnit : Prop
  ppMain : Prop
  pnSingleSpectral : Prop
  npSingleSpectral : Prop
  nnReciprocalTensor : Prop
  compositeAndGcdReassembly : Prop
  fullF2 : Prop

/-- The reciprocal-character tensor is an explicit OPEN input. Principal sectors
are separate premises and cannot be silently absorbed into the NN theorem. -/
theorem RECIPROCAL_CHARACTER_TENSOR_LARGE_SIEVE (C : F2SectorClaims)
    (rct : C.nnReciprocalTensor)
    (pp : C.ppMain) (pn : C.pnSingleSpectral) (np : C.npSingleSpectral)
    (reassemble : C.primeUnit → C.ppMain → C.pnSingleSpectral →
      C.npSingleSpectral → C.nnReciprocalTensor →
      C.compositeAndGcdReassembly → C.fullF2)
    (hPrime : C.primeUnit) (hComposite : C.compositeAndGcdReassembly) : C.fullF2 :=
  reassemble hPrime pp pn np rct hComposite

/-- Metadata for any structured tensor subcase. A result is Ford-ready only if
all four preservation flags are true. -/
structure StructuredTensorSubcase where
  label : String
  theoremAvailable : Bool
  preservesFixedShift : Bool
  preservesArbitraryCoefficients : Bool
  preservesRankOne : Bool
  preservesCompositeModuli : Bool

structure StructuredTensorInventory where
  smoothAlpha : StructuredTensorSubcase
  smoothCH : StructuredTensorSubcase
  primeModulus : StructuredTensorSubcase
  semiprimeModulus : StructuredTensorSubcase
  quadraticCharacters : StructuredTensorSubcase
  averagedShift : StructuredTensorSubcase
  wellFactorableLambda : StructuredTensorSubcase

/-- Exact Boolean criterion preventing a structured result from being labelled
Ford-ready unless all four required features are preserved. -/
def StructuredTensorSubcase.fordReady (s : StructuredTensorSubcase) : Bool :=
  s.theoremAvailable && s.preservesFixedShift && s.preservesArbitraryCoefficients &&
    s.preservesRankOne && s.preservesCompositeModuli

end ShiftedMobiusBank
