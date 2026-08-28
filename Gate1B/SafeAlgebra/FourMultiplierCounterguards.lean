/-
# Gate 1B v12 — source-independence firewall for four-multiplier moments

**Status: PROVED_ALGEBRAIC (finite explicit computation).**

Four copies produced by Cauchy–Schwarz are **not** four independent physical
source parameters.  This module makes the distinction kernel-checked, using the
four-cycle trace at `h = 0`, namely the quadratic form

    F(a1,a2,a3,a4) = a1 a3 + a2 a4,

evaluated over

* the full Cartesian cube `{0,1}⁴` (16 tuples), and
* the rank-one/diagonal source subset `{(0,0,0,0), (1,1,1,1)}` (2 tuples).

The two normalised moments differ (`1/2` versus `1`), so replacing a physical
source subset by the full Cartesian product is *not* a harmless step, in either
direction.

Contents:

* `quadMoment`, `fullCube`, `diagonalSource`;
* `quadMoment_fullCube`, `quadMoment_diagonalSource`;
* `fourCopies_ne_fourIndependentParameters` — the normalised moments differ;
* `rankOneRestriction_changes_moment` — restriction is not a harmless step.
-/
import Mathlib

namespace Gate1B.SafeAlgebra

open Finset

/-- The four-variable moment `∑ (a1 a3 + a2 a4)` over a finite tuple family. -/
def quadMoment (S : Finset (ℕ × ℕ × ℕ × ℕ)) : ℕ :=
  ∑ a ∈ S, (a.1 * a.2.2.1 + a.2.1 * a.2.2.2)

/-- The full Cartesian source cube `{0,1}⁴`. -/
def fullCube : Finset (ℕ × ℕ × ℕ × ℕ) :=
  ({0, 1} : Finset ℕ) ×ˢ ({0, 1} : Finset ℕ) ×ˢ ({0, 1} : Finset ℕ) ×ˢ ({0, 1} : Finset ℕ)

/-- A rank-one (diagonal) physical source subset. -/
def diagonalSource : Finset (ℕ × ℕ × ℕ × ℕ) := {(0, 0, 0, 0), (1, 1, 1, 1)}

theorem card_fullCube : fullCube.card = 16 := by decide

theorem card_diagonalSource : diagonalSource.card = 2 := by decide

theorem quadMoment_fullCube : quadMoment fullCube = 8 := by decide

theorem quadMoment_diagonalSource : quadMoment diagonalSource = 2 := by decide

/-- **Counterguard D.**  Four Cauchy copies do not amount to four independent
physical source parameters: the normalised four-variable moment over the full
Cartesian cube (`8/16`) differs from the one over the rank-one physical source
(`2/2`).  Stated by cross-multiplication to stay inside `ℕ`. -/
theorem fourCopies_ne_fourIndependentParameters :
    quadMoment fullCube * diagonalSource.card
      ≠ quadMoment diagonalSource * fullCube.card := by
  decide

/-- **Counterguard D′.**  A diagonal / rank-one source restriction materially
changes a four-variable moment; it is not an inessential normalisation. -/
theorem rankOneRestriction_changes_moment :
    (quadMoment fullCube : ℚ) / (fullCube.card : ℚ)
      ≠ (quadMoment diagonalSource : ℚ) / (diagonalSource.card : ℚ) := by
  rw [quadMoment_fullCube, quadMoment_diagonalSource, card_fullCube, card_diagonalSource]
  norm_num

end Gate1B.SafeAlgebra
