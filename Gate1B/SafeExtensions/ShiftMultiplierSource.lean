/-
# Gate 1B v12 — the physical four-multiplier source interface

**Status: definitions and finite identities PROVED; the analytic moment bound is
an UNINHABITED interface.**

The four multipliers `a1,…,a4` produced by the shifted four-cycle are **not**
asserted to be independent.  `PhysicalFourMultiplierSource` carries the actual
relation among them explicitly:

* `allowedTuples` — the finite family of tuples the physical source really
  produces;
* `sourceWeight` — the exact weight;
* `relation` together with `allowed_satisfies_relation` — the relation
  certificate.

There is **no default "all tuples" inhabitant**: any inhabitant must exhibit its
own allowed family and certificate.

`shiftMult4CharacterMoment` is defined through the *proved* four-cycle
discriminant `Gate1B.SafeAlgebra.fourCycleDisc`, so the moment is attached to
the genuine cyclic multiplier data rather than to four free parameters.

Contents:

* `PhysicalFourMultiplierSource`;
* `shiftMult4CharacterMoment`;
* `shiftMult4CharacterMoment_congr`, `shiftMult4CharacterMoment_empty`;
* `ShiftMult4CharacterBound` — UNINHABITED interface + non-vacuity guard;
* `cartesianEnlargement_changes_moment` — the enlargement counterguard.
-/
import Mathlib
import Gate1B.SafeAlgebra.MovingMultiplierFourCycle
import Gate1B.SafeAlgebra.FourMultiplierCounterguards

namespace Gate1B.SafeExtensions

open Finset Gate1B.SafeAlgebra

/-- **The physical four-multiplier source.**  No field says the four multipliers
range independently; the relation is a field. -/
structure PhysicalFourMultiplierSource (R : Type*) [CommRing R] [DecidableEq R] where
  /-- The tuples the physical source actually produces. -/
  allowedTuples : Finset (R × R × R × R)
  /-- The exact source weight. -/
  sourceWeight : R × R × R × R → ℂ
  /-- The relation the physical multipliers satisfy. -/
  relation : R × R × R × R → Prop
  /-- The relation certificate. -/
  allowed_satisfies_relation : ∀ t ∈ allowedTuples, relation t

namespace PhysicalFourMultiplierSource

variable {R : Type*} [CommRing R] [DecidableEq R]

/-- **The shifted four-multiplier character moment**, built from the proved
four-cycle discriminant and evaluated only on the physically allowed tuples. -/
noncomputable def shiftMult4CharacterMoment (S : PhysicalFourMultiplierSource R)
    (phi : R → ℂ) (h1 h2 h3 h4 : R) : ℂ :=
  ∑ t ∈ S.allowedTuples,
    S.sourceWeight t * phi (fourCycleDisc t.1 t.2.1 t.2.2.1 t.2.2.2 h1 h2 h3 h4)

/-- The moment depends only on the allowed family and the weight. -/
theorem shiftMult4CharacterMoment_congr (S S' : PhysicalFourMultiplierSource R)
    (phi : R → ℂ) (h1 h2 h3 h4 : R)
    (hT : S.allowedTuples = S'.allowedTuples) (hw : S.sourceWeight = S'.sourceWeight) :
    S.shiftMult4CharacterMoment phi h1 h2 h3 h4
      = S'.shiftMult4CharacterMoment phi h1 h2 h3 h4 := by
  unfold shiftMult4CharacterMoment
  rw [hT, hw]

/-- An empty physical source produces no moment. -/
theorem shiftMult4CharacterMoment_empty (S : PhysicalFourMultiplierSource R)
    (phi : R → ℂ) (h1 h2 h3 h4 : R) (hS : S.allowedTuples = ∅) :
    S.shiftMult4CharacterMoment phi h1 h2 h3 h4 = 0 := by
  unfold shiftMult4CharacterMoment
  rw [hS, Finset.sum_empty]

end PhysicalFourMultiplierSource

/-- **UNINHABITED ANALYTIC INTERFACE.**  The shifted four-multiplier character
moment bound.  Nothing in this bank constructs it. -/
structure ShiftMult4CharacterBound {R : Type*} [CommRing R] [DecidableEq R]
    (S : PhysicalFourMultiplierSource R) (phi : R → ℂ) (h1 h2 h3 h4 : R)
    (target : ℝ) : Prop where
  /-- EXTERNAL ANALYTIC INPUT — never supplied here. -/
  moment_le : ‖S.shiftMult4CharacterMoment phi h1 h2 h3 h4‖ ≤ target

/-- **Non-vacuity guard.** -/
theorem shiftMult4CharacterBound_not_vacuous {R : Type*} [CommRing R] [DecidableEq R]
    (S : PhysicalFourMultiplierSource R) (phi : R → ℂ) (h1 h2 h3 h4 : R) :
    ¬ ShiftMult4CharacterBound S phi h1 h2 h3 h4 (-1) := by
  intro h
  have := h.moment_le
  have h0 : (0 : ℝ) ≤ ‖S.shiftMult4CharacterMoment phi h1 h2 h3 h4‖ := norm_nonneg _
  linarith

/-- **Counterguard (Cartesian enlargement).**  Replacing a physical source subset
by the full Cartesian product changes a four-variable moment: this is the
`ℕ`-valued instance proved in `FourMultiplierCounterguards`, recorded here at the
interface so that no later step may perform the substitution silently. -/
theorem cartesianEnlargement_changes_moment :
    (quadMoment fullCube : ℚ) / (fullCube.card : ℚ)
      ≠ (quadMoment diagonalSource : ℚ) / (diagonalSource.card : ℚ) :=
  rankOneRestriction_changes_moment

end Gate1B.SafeExtensions
