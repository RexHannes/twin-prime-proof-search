/-
# Universal v13 — source-exact weighted high-`p₃` packet dictionary

**Status: DICTIONARY TYPE ONLY; no real inhabitant is constructed.**

A high-`p₃` packet carries a *weight type*, and the whole point of this module
is that the weight type is part of the data:

* `WeightType.common` — one weight shared by every packet;
* `WeightType.finiteTemplate` — a weight drawn from a fixed finite template
  list, independent of the packet edge;
* `WeightType.edgeDependent` — a weight that genuinely depends on the packet
  edge.

`SourceExactWeightedHighP3PacketDictionary` records a finite family of packets
together with the claim that each packet's weight really is of the declared
type.  Only the empty dictionary is exhibited (as a sanity inhabitant of the
*type*); no dictionary for the actual high-`p₃` source is constructed, and no
estimate is attached anywhere.
-/
import Mathlib

namespace Universal.SafeExtensions

open Finset

/-- The three admissible weight regimes of a high-`p₃` packet. -/
inductive WeightType
  | common
  | finiteTemplate
  | edgeDependent
  deriving DecidableEq, Repr

/-- A single high-`p₃` packet: an edge label, a declared weight type, and the
actual weight function on edges. -/
structure HighP3Packet (E : Type*) where
  /-- The edge the packet sits on. -/
  edge : E
  /-- The declared weight regime. -/
  weightType : WeightType
  /-- The actual weight, as a function of the edge. -/
  weight : E → ℂ

/-- The packet weight is *honest* when it matches its declared regime:
`common` means constant, `finiteTemplate` means valued in the declared finite
template, and `edgeDependent` imposes nothing. -/
def HighP3Packet.honest {E : Type*} (P : HighP3Packet E) (template : Finset ℂ) : Prop :=
  match P.weightType with
  | WeightType.common => ∀ e f : E, P.weight e = P.weight f
  | WeightType.finiteTemplate => ∀ e : E, P.weight e ∈ template
  | WeightType.edgeDependent => True

/-- **SOURCE-EXACT DICTIONARY (no real inhabitant here).**  A finite family of
high-`p₃` packets, each honest about its weight regime. -/
structure SourceExactWeightedHighP3PacketDictionary (E : Type*) where
  /-- The finite index set of packets. -/
  index : Type
  /-- The index set is finite. -/
  indexFintype : Fintype index
  /-- The packets themselves. -/
  packet : index → HighP3Packet E
  /-- The finite weight template used by `finiteTemplate` packets. -/
  template : Finset ℂ
  /-- Every packet is honest about its declared weight regime. -/
  honest : ∀ i, (packet i).honest template

/-- Sanity inhabitant of the *type* (empty index).  This is **not** a dictionary
for the actual high-`p₃` source. -/
def emptyHighP3Dictionary (E : Type*) : SourceExactWeightedHighP3PacketDictionary E where
  index := Empty
  indexFintype := inferInstance
  packet := fun i => i.elim
  template := ∅
  honest := fun i => i.elim

/-- A common-weight packet really is constant. -/
theorem common_weight_constant {E : Type*} (P : HighP3Packet E) (template : Finset ℂ)
    (hT : P.weightType = WeightType.common) (h : P.honest template) (e f : E) :
    P.weight e = P.weight f := by
  unfold HighP3Packet.honest at h
  rw [hT] at h
  exact h e f

/-- **Counterguard.**  Honesty for `edgeDependent` is vacuous, so an
edge-dependent packet may fail to be constant: the declared regime is genuine
data, not a derived property. -/
theorem edgeDependent_not_constant :
    ∃ P : HighP3Packet Bool, ∃ template : Finset ℂ,
      P.honest template ∧ P.weight true ≠ P.weight false := by
  refine ⟨⟨true, WeightType.edgeDependent, fun e => if e then 1 else 0⟩, ∅, trivial, ?_⟩
  simp

end Universal.SafeExtensions
