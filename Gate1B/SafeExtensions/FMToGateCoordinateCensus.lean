/-
# Gate 1B v13 — FM → Gate coordinate census (SOURCE-BLOCKED)

**Status: type PROVED to be source-blocked; no inhabitant is constructed.**

A coordinate census would match every coefficient slot produced by the literal
Ford–Maynard argument with a high-`p₃` packet coordinate.  Formally it needs
*both*

* `TwinPrimeProject.Gate1BV11.RealFordGrammarCertificate` — the literal Ford
  provenance datum, which this repository does not supply, and
* `Universal.SafeExtensions.SourceExactWeightedHighP3PacketDictionary` — the
  source-exact packet dictionary, for which no real inhabitant exists here.

`FMToGateCoordinateCensus` bundles the two with a slot-to-packet assignment.
`census_requires_fordProvenance` records the block: a census *contains* the
absent Ford certificate, so the census cannot be constructed until that source
gap is closed.  Nothing here weakens either requirement.
-/
import Universal.SafeExtensions.SourceExactHighP3PacketDictionary
import RequestProject.NANC.Gate1B.V11GeneratedExpression

namespace Gate1B.SafeExtensions

open Universal.SafeExtensions TwinPrimeProject.Gate1BV11

/-- **FM → GATE COORDINATE CENSUS (never inhabited here).**  Every literal Ford
coefficient slot is assigned a high-`p₃` packet whose edge is the slot's gate
coordinate. -/
structure FMToGateCoordinateCensus (E : Type) where
  /-- The literal Ford grammar certificate (absent in this repository). -/
  ford : RealFordGrammarCertificate
  /-- The source-exact high-`p₃` packet dictionary (no real inhabitant here). -/
  packets : SourceExactWeightedHighP3PacketDictionary E
  /-- The gate coordinate attached to each Ford slot. -/
  coordinate : ford.Slot → E
  /-- The packet assigned to each Ford slot. -/
  assign : ford.Slot → packets.index
  /-- The assigned packet sits on the slot's coordinate. -/
  edge_eq : ∀ s, (packets.packet (assign s)).edge = coordinate s

/-- Under a census every Ford coefficient slot is grammar-generated (this is the
only mathematical content the census transports). -/
theorem census_slots_generated {E : Type} (C : FMToGateCoordinateCensus E)
    (s : C.ford.Slot) : FMPerronGenerated (C.ford.fordCoefficient s) :=
  C.ford.grammar.generated s

/-- **SOURCE BLOCK.**  A census contains the literal Ford provenance
certificate, which this repository cannot supply; hence the census is blocked at
exactly that source datum. -/
theorem census_requires_fordProvenance {E : Type}
    (h : Nonempty (FMToGateCoordinateCensus E)) : Nonempty RealFordGrammarCertificate :=
  h.elim fun C => ⟨C.ford⟩

/-- **SOURCE BLOCK (second leaf).**  A census also contains a source-exact
packet dictionary. -/
theorem census_requires_packetDictionary {E : Type}
    (h : Nonempty (FMToGateCoordinateCensus E)) :
    Nonempty (SourceExactWeightedHighP3PacketDictionary E) :=
  h.elim fun C => ⟨C.packets⟩

end Gate1B.SafeExtensions
