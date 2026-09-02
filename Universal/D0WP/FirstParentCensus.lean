/-
# Universal / D0WP — first-parent source census

**Status of this module: KERNEL_PROVED finite routing algebra; the census pin
itself is left UNINHABITED.**

The first-parent source owner classes are represented as a finite type with an
explicit deterministic owner order.  What is kernel-proved is exactly the finite
content:

* the owner order lists every class exactly once;
* the assignment `assignOwner` is deterministic and returns the *first* matching
  class;
* the assignment succeeds for a row **iff** some class matches that row.

Exhaustiveness for the *literal* source grammar is precisely the last "iff"'s
right-hand side, and it is **not** proved here: it is the pin
`FirstParentSourceCensusPin`, which has no inhabitant in this repository.
-/
import Mathlib

namespace Universal.D0WP

/-- First-parent source owner classes. -/
inductive FirstParentOwner
  /-- Pure Möbius source. -/
  | pureMobius
  /-- Canonical composite source. -/
  | canonicalComposite
  /-- Canonical singleton source. -/
  | canonicalSingleton
  /-- Canonical semiprime source. -/
  | canonicalSemiprime
  /-- Canonical short source. -/
  | canonicalShort
  /-- Möbius-free source. -/
  | mobiusFree
  /-- Local source. -/
  | localOwner
  deriving DecidableEq, Repr

namespace FirstParentOwner

/-- The explicit deterministic owner order. -/
def order : List FirstParentOwner :=
  [pureMobius, canonicalComposite, canonicalSingleton, canonicalSemiprime,
   canonicalShort, mobiusFree, localOwner]

/-- Every class occurs in the order. -/
theorem mem_order (c : FirstParentOwner) : c ∈ order := by
  cases c <;> simp [order]

/-- No class occurs twice. -/
theorem order_nodup : order.Nodup := by decide

end FirstParentOwner

/-- Deterministic owner assignment: the first class in the fixed order whose
predicate matches. -/
def assignOwner {ι : Type*} (p : FirstParentOwner → ι → Bool) (i : ι) :
    Option FirstParentOwner :=
  FirstParentOwner.order.find? (fun c => p c i)

/-- The assigned class really matches. -/
theorem assignOwner_matches {ι : Type*} {p : FirstParentOwner → ι → Bool} {i : ι}
    {c : FirstParentOwner} (h : assignOwner p i = some c) : p c i = true := by
  unfold assignOwner at h
  have := List.find?_some (p := fun c => p c i) h
  simpa using this

/-- **Assignment succeeds exactly when some class matches (kernel-proved).** -/
theorem assignOwner_isSome_iff {ι : Type*} (p : FirstParentOwner → ι → Bool) (i : ι) :
    (assignOwner p i).isSome ↔ ∃ c, p c i = true := by
  unfold assignOwner
  rw [List.find?_isSome]
  constructor
  · rintro ⟨c, _, hc⟩
    exact ⟨c, hc⟩
  · rintro ⟨c, hc⟩
    exact ⟨c, FirstParentOwner.mem_order c, hc⟩

/-- **SOURCE PIN (UNINHABITED here).**  Every literal first-parent source row is
owned by some class of the census. -/
def FirstParentSourceCensusPin {ι : Type*} (rows : Finset ι)
    (p : FirstParentOwner → ι → Bool) : Prop :=
  ∀ i ∈ rows, ∃ c, p c i = true

/-- Conditional consequence of the census pin: every row receives exactly one
owner. -/
theorem census_assigns_owner {ι : Type*} {rows : Finset ι}
    {p : FirstParentOwner → ι → Bool} (pin : FirstParentSourceCensusPin rows p)
    (i : ι) (hi : i ∈ rows) : ∃ c, assignOwner p i = some c := by
  have : (assignOwner p i).isSome := (assignOwner_isSome_iff p i).2 (pin i hi)
  exact Option.isSome_iff_exists.mp this

/-- The census pin is a genuine obligation: it can fail. -/
theorem firstParentCensusPin_not_automatic :
    ∃ (rows : Finset Unit) (p : FirstParentOwner → Unit → Bool),
      ¬ FirstParentSourceCensusPin rows p := by
  refine ⟨{()}, fun _ _ => false, ?_⟩
  intro pin
  obtain ⟨c, hc⟩ := pin () (by simp)
  simp at hc

end Universal.D0WP
