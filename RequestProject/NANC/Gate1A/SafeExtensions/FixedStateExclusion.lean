/-
# NANC Gate 1A v9.4 — fixed-state exclusion

A **fixed-state exclusion certificate** attaches to every state a finite set of
*obstruction integers* that does **not** depend on the family parameter `r`.
Then the number of excluded `r` in any finite range is bounded by the size of
that fixed set, uniformly in the range.

The firewall in this file records why the "fixed" is essential: if the
obstruction set is permitted to depend on `r`, then singletons already exclude
*every* `r`, and no counting bound survives.
-/
import Mathlib

namespace TwinPrimeProject.NANC.Gate1A.V94

open Finset

/-- A fixed-state exclusion certificate: obstruction integers attached to each
state, independent of the family parameter. -/
structure FixedStateExclusionCertificate (State : Type*) where
  /-- The `r`-independent obstruction integers of a state. -/
  obstructionIntegers : State → Finset ℤ
  /-- A uniform bound on the number of obstructions. -/
  obstructionBound : ℕ
  card_le : ∀ st, (obstructionIntegers st).card ≤ obstructionBound

namespace FixedStateExclusionCertificate

variable {State : Type*} (C : FixedStateExclusionCertificate State)

/-- The excluded parameters in a finite range. -/
def excluded (st : State) (range : Finset ℤ) : Finset ℤ :=
  range.filter fun r => r ∈ C.obstructionIntegers st

/-- **Uniform exclusion count.**  In any finite range, the number of excluded
parameters is at most the fixed obstruction bound — in particular it does not
grow with the range. -/
theorem excluded_card_le (st : State) (range : Finset ℤ) :
    (C.excluded st range).card ≤ C.obstructionBound := by
  refine le_trans (Finset.card_le_card ?_) (C.card_le st)
  intro r hr
  simpa [excluded] using (Finset.mem_filter.mp hr).2

/-- Consequently, a range larger than the obstruction bound always contains an
admissible parameter. -/
theorem exists_admissible (st : State) (range : Finset ℤ)
    (hrange : C.obstructionBound < range.card) :
    ∃ r ∈ range, r ∉ C.obstructionIntegers st := by
  by_contra hcon
  push_neg at hcon
  have hsub : range ⊆ C.obstructionIntegers st := fun r hr => hcon r hr
  exact absurd (le_trans (Finset.card_le_card hsub) (C.card_le st)) (not_le.mpr hrange)

end FixedStateExclusionCertificate

/-! ## Firewall: `r`-dependent obstructions carry no information -/

/-- **Firewall countermodel.**  If the obstruction set is allowed to depend on
the family parameter, then obstruction sets of size one already exclude every
parameter.  Hence only *fixed* (parameter-independent) obstruction sets may be
used in an exclusion certificate. -/
theorem rDependent_obstruction_excludes_everything :
    ∃ obstruction : ℤ → Finset ℤ,
      (∀ r, (obstruction r).card = 1) ∧ ∀ r, r ∈ obstruction r := by
  refine ⟨fun r => {r}, fun r => Finset.card_singleton r, fun r => Finset.mem_singleton_self r⟩

end TwinPrimeProject.NANC.Gate1A.V94
