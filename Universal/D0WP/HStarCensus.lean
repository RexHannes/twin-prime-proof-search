/-
# Universal / D0WP — HSTAR source-owner census

**Status of this module: CONDITIONAL_KERNEL; the census input is UNINHABITED.**

The three neutral source families are `FIRST_PARENT`, `BALANCED_R9`,
`OTHER_PARENT`.  Naming them does **not** make them exhaustive.  The exact
obligation is isolated as

```
HStarSourceOwnerCensusInput rows family :
    every HSTAR source row is assigned to some family,
```

with the family map a *function*, so "exactly one family" and "exactly one
owner per family" are structural, and disjointness of the family fibres — the
no-double-spending property — is kernel-proved.

Conditionally on the census input plus the RUN1B, balanced-`R9` and OTHER45
conclusions, the HSTAR remainder bound follows.  No inhabitant of the census
input is constructed here.
-/
import Universal.D0WP.FinitePacketCompiler

namespace Universal.D0WP

open Finset

/-- Neutral HSTAR source families.  Exhaustiveness is *not* assumed. -/
inductive HStarFamily
  /-- First-parent family. -/
  | firstParent
  /-- Balanced `R9` family. -/
  | balancedR9
  /-- Other-parent family. -/
  | otherParent
  deriving DecidableEq, Repr, Fintype

/-- **SOURCE PIN (UNINHABITED here).**  Every HSTAR source row is owned by one
of the three families.  Rows with `family i = none` are exactly the rows the
census does not yet cover. -/
def HStarSourceOwnerCensusInput {ι : Type*} (rows : Finset ι)
    (family : ι → Option HStarFamily) : Prop :=
  ∀ i ∈ rows, (family i).isSome

/-- The family fibres are pairwise disjoint: no analytic saving is spent
twice. -/
theorem hstar_families_disjoint {ι : Type*} [DecidableEq ι] (rows : Finset ι)
    (family : ι → Option HStarFamily) {f f' : HStarFamily} (h : f ≠ f') :
    Disjoint (rows.filter (fun i => family i = some f))
      (rows.filter (fun i => family i = some f')) := by
  refine Finset.disjoint_filter.2 ?_
  intro i _ hf hf'
  rw [hf] at hf'
  exact h (Option.some.inj hf')

/-- **HSTAR REMAINDER, CONDITIONAL (kernel-proved implication).**

The census input is load-bearing: without it the family fibres need not cover
the row set. -/
theorem hstar_remainder_conditional {ι : Type*} [DecidableEq ι]
    (rows : Finset ι) (family : ι → Option HStarFamily) (F : ι → ℂ)
    (B : HStarFamily → ℝ)
    (census : HStarSourceOwnerCensusInput rows family)
    (hfam : ∀ f : HStarFamily,
      ‖∑ i ∈ rows.filter (fun i => family i = some f), F i‖ ≤ B f) :
    ‖∑ i ∈ rows, F i‖ ≤ ∑ f : HStarFamily, B f := by
  classical
  set famOf : ι → HStarFamily := fun i => (family i).getD HStarFamily.firstParent with hfamOf
  have hfilter : ∀ f : HStarFamily,
      rows.filter (fun i => famOf i = f) = rows.filter (fun i => family i = some f) := by
    intro f
    ext i
    simp only [Finset.mem_filter, and_congr_right_iff]
    intro hi
    have hsome : (family i).isSome := census i hi
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hsome
    rw [hfamOf]
    simp only [hx, Option.getD_some]
    constructor
    · rintro rfl; rfl
    · intro h
      exact Option.some.inj (hx ▸ h)
  refine owner_bound_assembly rows famOf F B ?_
  intro f
  rw [hfilter f]
  exact hfam f

/-- The census input is a genuine obligation: it can fail. -/
theorem hstarCensus_not_automatic :
    ∃ (rows : Finset Unit) (family : Unit → Option HStarFamily),
      ¬ HStarSourceOwnerCensusInput rows family := by
  refine ⟨{()}, fun _ => none, ?_⟩
  intro census
  have := census () (by simp)
  simp at this

end Universal.D0WP
