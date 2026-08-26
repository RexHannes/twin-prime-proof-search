import RequestProject.NANC.Gate01Consolidation.SourceInterfaces
import RequestProject.NANC.Gate01Consolidation.ProductModeObstruction
import RequestProject.NANC.Gate01Consolidation.ShiftInverse
import RequestProject.NANC.Gate01Consolidation.DeterminantIdentity
import RequestProject.NANC.Gate01Consolidation.R9Regrouping

/-!
# The Gate 0–1 consolidation status ledger

A machine-checkable table.  Only genuinely finite, Lean-proved items carry
`provedFinite`; conditional results carry `provedConditional`; everything
analytic or source-dependent stays `openAnalytic` / `openSource`; retired or
purely reformulating routes are marked as such.

Consistency with the existing project ledgers: the Gate 1A / Gate 1B / Gate 0
entries agree with `RequestProject/NANC/Gate01CombinedLedger.lean`
(direct analytic Gate 1A OPEN, switched analytic Gate 1B OPEN, Gate 0 coverage
OPEN).  No existing status is overwritten by this module.
-/

namespace TwinPrimeProject
namespace Gate01Consolidation

/-- Status codes for the consolidation bank. -/
inductive ProofStatus
  /-- Proved in Lean, finite / algebraic / combinatorial content only. -/
  | provedFinite
  /-- Proved in Lean, but only as an implication from explicit interfaces. -/
  | provedConditional
  /-- An open analytic estimate; an explicit, never inhabited interface. -/
  | openAnalytic
  /-- An open source input; an explicit, never inhabited interface. -/
  | openSource
  /-- A reformulation with no strict reduction proved. -/
  | reformulationOnly
  /-- A route that is retired. -/
  | retired
  deriving DecidableEq, Repr

/-- Items of the Gate 0–1 consolidation bank. -/
inductive Item
  | ESeparation
  | NonzeroOrthogonality
  | CRTNaturalCentering
  | CRTSourceCentering
  | ShiftInverse
  | ShiftRepresentationMultiplicity
  | PrimeCovarianceKernel
  | PrimeSecondMoment
  | PrimeOffDiagonalBound
  | AnovaProductModeObstruction
  | DeterminantIdentity
  | DeterminantClosureRoute
  | DirectGaussReassembly
  | NonUnitStratification
  | DirectPhysicalPhase
  | R9FourFiveRegrouping
  | FourFiveThresholdCrossing
  | FourFiveAveragedDispersion
  | SwitchedMixedCovariance
  | ExpectedDensitySource
  | SwitchedRoutingJ3ToJ6
  | GlobalHighP3Exhaustion
  | Gate1B
  | Gate1A
  | Gate0
  deriving DecidableEq, Repr

open ProofStatus Item

/-- The status table. -/
def status : Item → ProofStatus
  | ESeparation => provedFinite
  | NonzeroOrthogonality => provedFinite
  | CRTNaturalCentering => provedFinite
  | CRTSourceCentering => provedConditional
  | ShiftInverse => provedFinite
  | ShiftRepresentationMultiplicity => provedFinite
  | PrimeCovarianceKernel => provedFinite
  | PrimeSecondMoment => provedFinite
  | PrimeOffDiagonalBound => openAnalytic
  | AnovaProductModeObstruction => provedFinite
  | DeterminantIdentity => provedFinite
  | DeterminantClosureRoute => reformulationOnly
  | DirectGaussReassembly => provedFinite
  | NonUnitStratification => provedFinite
  | DirectPhysicalPhase => openAnalytic
  | R9FourFiveRegrouping => provedFinite
  | FourFiveThresholdCrossing => provedFinite
  | FourFiveAveragedDispersion => openAnalytic
  | SwitchedMixedCovariance => openAnalytic
  | ExpectedDensitySource => openSource
  | SwitchedRoutingJ3ToJ6 => openSource
  | GlobalHighP3Exhaustion => openSource
  | Gate1B => openAnalytic
  | Gate1A => openAnalytic
  | Gate0 => openSource

/-- The finite items of the bank. -/
def finiteItems : List Item :=
  [ESeparation, NonzeroOrthogonality, CRTNaturalCentering, ShiftInverse,
   ShiftRepresentationMultiplicity, PrimeCovarianceKernel, PrimeSecondMoment,
   AnovaProductModeObstruction, DeterminantIdentity, DirectGaussReassembly,
   NonUnitStratification, R9FourFiveRegrouping, FourFiveThresholdCrossing]

/-- The items that remain analytic or source-open. -/
def openItems : List Item :=
  [PrimeOffDiagonalBound, DirectPhysicalPhase, FourFiveAveragedDispersion,
   SwitchedMixedCovariance, ExpectedDensitySource, SwitchedRoutingJ3ToJ6,
   GlobalHighP3Exhaustion, Gate1B, Gate1A, Gate0]

/-- Every item listed as finite really carries `provedFinite`. -/
theorem finiteItems_provedFinite : ∀ i ∈ finiteItems, status i = provedFinite := by decide

/-- No open item is ever marked as proved (finitely or conditionally): a silent
upgrade is impossible. -/
theorem openItems_not_proved :
    ∀ i ∈ openItems, status i ≠ provedFinite ∧ status i ≠ provedConditional := by decide

/-- The gates are not closed by this bank. -/
theorem gates_not_closed :
    status Gate0 = openSource ∧ status Gate1A = openAnalytic ∧ status Gate1B = openAnalytic := by
  decide

/-- The determinant route is reformulation only; the determinant *identity* is
proved. -/
theorem determinant_route_reformulation_only :
    status DeterminantIdentity = provedFinite ∧
    status DeterminantClosureRoute = reformulationOnly := by decide

/-- The source-density CRT identity is conditional (on DENS-MULT), never
finite-proved. -/
theorem crt_source_conditional : status CRTSourceCentering = provedConditional := by decide

end Gate01Consolidation
end TwinPrimeProject
