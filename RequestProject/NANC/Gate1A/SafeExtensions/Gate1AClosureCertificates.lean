/-
# NANC Gate 1A v9.4 — abstract closure certificates

Two certificate structures and their *compilers*:

* `Gate1ACleanP3ClosureCertificate` — the clean-P3 route;
* the ALL-`m` route lives in `AllMExhaustiveness`.

Each compiles to the abstract final budget predicate `FinalBudgetMet`.  This
makes the exact missing pieces machine-visible: to close Gate 1A clean-P3 one
must *construct an inhabitant*, i.e. supply every field with a proof.

**No inhabitant of either certificate is constructed in this repository**, and
none may be constructed until every sector certificate is proved.  In
particular this file does not, and must not, assert that Gate 1A is closed.
-/
import Mathlib

namespace TwinPrimeProject.NANC.Gate1A.V94

open Finset

/-- The abstract final budget predicate. -/
def FinalBudgetMet (total budget : ℝ) : Prop := total ≤ budget

/-- A per-sector finite energy certificate. -/
structure SectorEnergyCertificate (Source : Type*) [Fintype Source] where
  /-- The energy carried by the sector at each source datum. -/
  energy : Source → ℝ
  energy_nonneg : ∀ x, 0 ≤ energy x
  /-- The sector budget. -/
  bound : ℝ
  /-- The sector is controlled. -/
  controlled : ∑ x : Source, energy x ≤ bound

/-- The Gate 1A clean-P3 closure certificate.  Every field is a proof
obligation. -/
structure Gate1ACleanP3ClosureCertificate (Source : Type*) [Fintype Source] where
  /-- Generic full-conductor sector. -/
  generic : SectorEnergyCertificate Source
  /-- Proper-conductor sector. -/
  proper : SectorEnergyCertificate Source
  /-- Zero-reduced / projective sector. -/
  zeroProjective : SectorEnergyCertificate Source
  /-- Same-`q` sector. -/
  sameQ : SectorEnergyCertificate Source
  /-- The total energy to be controlled. -/
  totalEnergy : ℝ
  /-- Reassembly: the total is dominated by the four sector energies. -/
  reassembly : totalEnergy ≤ ∑ x : Source,
    (generic.energy x + proper.energy x + zeroProjective.energy x + sameQ.energy x)
  /-- The final budget. -/
  finalBudget : ℝ
  /-- Budget arithmetic. -/
  budget_arith :
    generic.bound + proper.bound + zeroProjective.bound + sameQ.bound ≤ finalBudget

namespace Gate1ACleanP3ClosureCertificate

variable {Source : Type*} [Fintype Source] (C : Gate1ACleanP3ClosureCertificate Source)

/-- **The clean-P3 compiler.**  A complete certificate meets the final budget. -/
theorem toFinalBudget : FinalBudgetMet C.totalEnergy C.finalBudget := by
  have hsum : ∑ x : Source,
      (C.generic.energy x + C.proper.energy x + C.zeroProjective.energy x + C.sameQ.energy x)
      = (∑ x : Source, C.generic.energy x) + (∑ x : Source, C.proper.energy x)
        + (∑ x : Source, C.zeroProjective.energy x) + (∑ x : Source, C.sameQ.energy x) := by
    simp [Finset.sum_add_distrib]
  have h1 := C.generic.controlled
  have h2 := C.proper.controlled
  have h3 := C.zeroProjective.controlled
  have h4 := C.sameQ.controlled
  have hb := C.budget_arith
  have := C.reassembly
  rw [hsum] at this
  exact this.trans (by linarith)

end Gate1ACleanP3ClosureCertificate

/-! ## Machine-visible open fields

The clean-P3 certificate cannot be inhabited today because
`generic : SectorEnergyCertificate Source` would require the generic
full-conductor analytic estimate, and `zeroProjective` would require the
literal zero-projective source coefficient.  Both remain interfaces.  The
statement "Gate 1A clean-P3 is closed" is therefore *not* available as a
theorem, and the absence of an inhabitant below is the machine-visible record
of that fact. -/

end TwinPrimeProject.NANC.Gate1A.V94
