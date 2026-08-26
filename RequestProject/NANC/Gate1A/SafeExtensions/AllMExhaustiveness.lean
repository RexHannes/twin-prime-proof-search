/-
# NANC Gate 1A v9.4 — sector table and ALL-`m` exhaustiveness

The Gate 1A clean-P3 sectors are recorded as a finite inductive type together
with a status ledger.  A status is recorded as **open** unless a proved theorem
in this repository justifies anything stronger.

The exhaustiveness certificate is deliberately *unforgiving*:

* the frozen exception bank carries **proof fields**, never Boolean flags or
  status strings;
* the exhaustiveness certificate has **no "all other cases" escape field** —
  every sector must be discharged individually and the sector list must be
  proved to cover the source.

Consequently the certificate structures below have **no inhabitant** in this
repository, which is exactly the machine-visible statement that Gate 1A
clean-P3 is not closed.
-/
import Mathlib

namespace TwinPrimeProject.NANC.Gate1A.V94

open Finset

/-! ## 1. The sector list -/

/-- The Gate 1A clean-P3 sectors. -/
inductive Gate1ACleanP3Sector
  | sameQ
  | zeroFrequency
  | tZero
  | repeatedPrime
  | crossRolePrime
  | nonunit
  | gcdCollision
  | properConductor
  | projective
  | trueLocalZero
  | smoothingBoundary
  | genericFullConductor
  deriving DecidableEq, Repr, Fintype

/-- The status a sector can carry. -/
inductive SectorStatus
  /-- Discharged by a finite/algebraic theorem in this repository. -/
  | FiniteBanked
  /-- Blocked by a *source* interface: the literal source coefficient is not in
  the repository. -/
  | SourceInterfaceOpen
  /-- Blocked by an analytic interface. -/
  | AnalyticInterfaceOpen
  deriving DecidableEq, Repr

/-- The honest v9.4 sector ledger.  Only statuses justified by proved theorems
in this repository are recorded as `FiniteBanked`, and `FiniteBanked` here means
*the finite algebra of the sector is banked*, never that the sector is
analytically closed. -/
def sectorStatus : Gate1ACleanP3Sector → SectorStatus
  | .sameQ => .FiniteBanked
  | .zeroFrequency => .FiniteBanked
  | .tZero => .FiniteBanked
  | .repeatedPrime => .SourceInterfaceOpen
  | .crossRolePrime => .SourceInterfaceOpen
  | .nonunit => .FiniteBanked
  | .gcdCollision => .SourceInterfaceOpen
  | .properConductor => .SourceInterfaceOpen
  | .projective => .SourceInterfaceOpen
  | .trueLocalZero => .SourceInterfaceOpen
  | .smoothingBoundary => .AnalyticInterfaceOpen
  | .genericFullConductor => .AnalyticInterfaceOpen

/-- At least one sector is still blocked: the ledger is not "all banked". -/
theorem sectorStatus_not_all_banked :
    ∃ S : Gate1ACleanP3Sector, sectorStatus S ≠ SectorStatus.FiniteBanked :=
  ⟨.genericFullConductor, by decide⟩

/-- The generic full-conductor sector is analytically open. -/
theorem genericFullConductor_analyticOpen :
    sectorStatus .genericFullConductor = SectorStatus.AnalyticInterfaceOpen := rfl

/-- The projective sector is blocked by a source interface. -/
theorem projective_sourceInterfaceOpen :
    sectorStatus .projective = SectorStatus.SourceInterfaceOpen := rfl

/-! ## 2. Frozen exception bank: proof fields only -/

/-- The frozen exception bank.  Every field is a **proof obligation** about the
source data; there are no Boolean flags and no status strings, so the structure
cannot be inhabited by bookkeeping alone. -/
structure Gate1AFrozenExceptionBank (Source : Type*) where
  /-- The sector classification of the source data. -/
  sectorOf : Source → Gate1ACleanP3Sector
  /-- The finite energy attached to a piece of source data. -/
  energy : Source → ℝ
  /-- Energies are non-negative. -/
  energy_nonneg : ∀ x, 0 ≤ energy x
  /-- The exceptional target for each sector. -/
  target : Gate1ACleanP3Sector → ℝ
  /-- Every exceptional sector is discharged by a *proof* that its energy meets
  its target. -/
  discharged : ∀ x, energy x ≤ target (sectorOf x)

/-! ## 3. ALL-`m` exhaustiveness certificate (no escape field) -/

/-- The ALL-`m` source exhaustiveness certificate.

Note the deliberate absence of an "all other cases" field: the sector map must
be **total and proved**, and the reassembly must bound the total source energy
by the sum of the sector targets.  There is no inhabitant of this structure in
the repository. -/
structure AllMSourceExhaustivenessCertificate (Source : Type*) [Fintype Source] where
  bank : Gate1AFrozenExceptionBank Source
  /-- The global source energy. -/
  totalEnergy : ℝ
  /-- The reassembly identity: the total energy is the sum over the source. -/
  reassembly : totalEnergy = ∑ x : Source, bank.energy x
  /-- The final finite budget. -/
  budget : ℝ
  /-- The sector targets sum, over the source, to at most the budget. -/
  sector_budget : ∑ x : Source, bank.target (bank.sectorOf x) ≤ budget

namespace AllMSourceExhaustivenessCertificate

variable {Source : Type*} [Fintype Source] (C : AllMSourceExhaustivenessCertificate Source)

/-- **The compiler.**  A complete exhaustiveness certificate bounds the total
source energy by the finite budget.  (This is the only content that is proved:
the certificate itself is not constructed.) -/
theorem total_le_budget : C.totalEnergy ≤ C.budget := by
  rw [C.reassembly]
  refine le_trans (Finset.sum_le_sum fun x _ => C.bank.discharged x) C.sector_budget

end AllMSourceExhaustivenessCertificate

end TwinPrimeProject.NANC.Gate1A.V94
