/-
# NANC Gate 1A v9.8 — the Gate 0 / Gate 1A scope split

Sections 0, 18, 19, 20 and 22 of the v9.8 instructions all say the same thing in
different words: several real obligations are obligations of the **Gate 0 source
compiler**, not fields of the canonical Gate 1A Direct theorem.  This file makes
that split machine-visible.

* `scopeOf` assigns every obligation to `gate1ADirect`, `gate0Compiler` or
  `secondaryRoute`, and the assignment is checked by `decide`.
* `edgeDependentD2_is_gate0_adapter_obligation` and
  `rootDefect_is_secondary_route` are the two named scope theorems.
* `Gate0ToGate1AExhaustivenessCertificate` is the Gate 0 obligation itself, in a
  namespace of its own.  It is **not** a field of anything in
  `V98DirectClosure`, it has no inhabitant here, and
  `gate0Exhaustiveness_not_definitional` proves that it is not definitionally
  true: with an unroutable packet the certificate type is empty.
* `gate1ADirect_closure_independent_of_gate0` is the sharp separation: there is
  a configuration in which the Gate 1A Direct closure certificate is inhabited
  while the Gate 0 exhaustiveness certificate is empty.  Gate 1A Direct is
  therefore not blocked by the Gate 0 census — and, by the same theorem, closing
  Gate 1A Direct does not close Gate 0.

Nothing here deletes or weakens `EdgeDependentD2Data` or
`RootDefectSourceFactorization`; both stay exactly as banked.
-/
import Mathlib
import RequestProject.CenteredCRTRootNormalForm
import RequestProject.NANC.Gate1A.SafeExtensions.V98DirectClosure

namespace TwinPrimeProject.NANC.Gate1A.V98

open TwinPrimeProject.CenteredCRTRoot

/-! ## 1. The scope assignment -/

/-- The three scopes. -/
inductive ObligationScope
  /-- Part of the canonical Gate 1A Direct theorem. -/
  | gate1ADirect
  /-- Part of the Gate 0 / source compiler. -/
  | gate0Compiler
  /-- An independent secondary representation or alternate route. -/
  | secondaryRoute
  deriving DecidableEq, Repr

/-- The obligations that have to be placed. -/
inductive Obligation
  | canonicalDirectSource
  | commonPhysicalWeight
  | canonicalAllMRows
  | canonicalDirectEnergy
  | bppEnergyPin
  | bppExternalAnalyticInput
  | smoothSeparationTemplates
  | sourceExactPacketDictionary
  | packetMultiplicity
  | globalHighP3SourceAssembly
  | edgeDependentD2Adapter
  | exceptionalRouting
  | gate0ToGate1AExhaustiveness
  | rootDefectSourceFactorization
  deriving DecidableEq, Repr

/-- **The scope assignment.** -/
def scopeOf : Obligation → ObligationScope
  | .canonicalDirectSource => .gate1ADirect
  | .commonPhysicalWeight => .gate1ADirect
  | .canonicalAllMRows => .gate1ADirect
  | .canonicalDirectEnergy => .gate1ADirect
  | .bppEnergyPin => .gate1ADirect
  | .bppExternalAnalyticInput => .gate1ADirect
  | .smoothSeparationTemplates => .gate1ADirect
  | .sourceExactPacketDictionary => .gate0Compiler
  | .packetMultiplicity => .gate0Compiler
  | .globalHighP3SourceAssembly => .gate0Compiler
  | .edgeDependentD2Adapter => .gate0Compiler
  | .exceptionalRouting => .gate0Compiler
  | .gate0ToGate1AExhaustiveness => .gate0Compiler
  | .rootDefectSourceFactorization => .secondaryRoute

/-- All obligations, in ledger order. -/
def allObligations : List Obligation :=
  [ .canonicalDirectSource, .commonPhysicalWeight, .canonicalAllMRows
  , .canonicalDirectEnergy, .bppEnergyPin, .bppExternalAnalyticInput
  , .smoothSeparationTemplates, .sourceExactPacketDictionary, .packetMultiplicity
  , .globalHighP3SourceAssembly, .edgeDependentD2Adapter, .exceptionalRouting
  , .gate0ToGate1AExhaustiveness, .rootDefectSourceFactorization ]

theorem mem_allObligations (o : Obligation) : o ∈ allObligations := by
  cases o <;> simp [allObligations]

/-- **`edgeDependentD2_is_gate0_adapter_obligation`.**  An arbitrary
`EdgeDependentD2Data` is a Gate 0 / source-adapter obligation; it is not an
input of the canonical Gate 1A Direct theorem. -/
theorem edgeDependentD2_is_gate0_adapter_obligation :
    scopeOf .edgeDependentD2Adapter = ObligationScope.gate0Compiler := rfl

/-- The root-defect source factorisation is a secondary route. -/
theorem rootDefect_is_secondary_route :
    scopeOf .rootDefectSourceFactorization = ObligationScope.secondaryRoute := rfl

/-- The Gate 0 obligations are exactly the six listed ones. -/
theorem gate0_obligations :
    allObligations.filter (fun o => scopeOf o = ObligationScope.gate0Compiler)
      = [ .sourceExactPacketDictionary, .packetMultiplicity, .globalHighP3SourceAssembly
        , .edgeDependentD2Adapter, .exceptionalRouting, .gate0ToGate1AExhaustiveness ] := by
  decide

/-- No Gate 0 obligation is a Gate 1A Direct obligation. -/
theorem gate0_disjoint_from_gate1ADirect (o : Obligation)
    (h : scopeOf o = ObligationScope.gate0Compiler) :
    scopeOf o ≠ ObligationScope.gate1ADirect := by
  rw [h]; decide

/-- `EdgeDependentD2Data` itself is untouched and still available: the datum is
relocated in scope, never deleted. -/
theorem edgeDependentD2Data_still_available
    (Edge Pair Harm : Type) [Fintype Edge] [Fintype Pair] [Fintype Harm]
    (c ph : Edge → Pair → Harm → ℂ) :
    (V96.edgeData Edge Pair Harm c ph).coeff = c :=
  V96.edgeData_coeff Edge Pair Harm c ph

/-! ## 2. The Gate 0 → Gate 1A compiler obligation, in its own namespace -/

namespace Gate0

/-- The three destinations of a global source packet. -/
inductive Route
  /-- Routed to the canonical Gate 1A Direct engine. -/
  | gate1ADirect
  /-- Routed to Gate 1B. -/
  | gate1B
  /-- An already-closed exceptional family. -/
  | closedExceptional
  deriving DecidableEq, Repr

/-- **The Gate 0 → Gate 1A exhaustiveness certificate.**  `admissible` is the
externally given routing relation; the certificate is a total routing of the
actual packets compatible with it.  Its status is OPEN: no inhabitant is
constructed. -/
structure Gate0ToGate1AExhaustivenessCertificate (Packet : Type*) [Fintype Packet]
    (admissible : Packet → Route → Prop) where
  /-- The chosen route of each actual packet. -/
  route : Packet → Route
  /-- Every packet is routed admissibly: no `unclassified` escape hatch. -/
  routed : ∀ p, admissible p (route p)

/-- **The Gate 0 obligation is not definitionally true.**  If some actual packet
has no admissible route, the certificate type is empty. -/
theorem gate0Exhaustiveness_not_definitional :
    IsEmpty (Gate0ToGate1AExhaustivenessCertificate (Fin 1) (fun _ _ => False)) := by
  constructor
  rintro C
  exact C.routed 0

/-- Conversely, the certificate is exactly a choice of admissible routes. -/
theorem gate0Exhaustiveness_nonempty_iff {Packet : Type*} [Fintype Packet]
    (admissible : Packet → Route → Prop) :
    Nonempty (Gate0ToGate1AExhaustivenessCertificate Packet admissible) ↔
      ∀ p, ∃ r, admissible p r := by
  classical
  constructor
  · rintro ⟨C⟩ p; exact ⟨C.route p, C.routed p⟩
  · intro h
    exact ⟨{ route := fun p => (h p).choose, routed := fun p => (h p).choose_spec }⟩

end Gate0

/-! ## 3. The sharp separation -/

/-- **Gate 1A Direct closure is not blocked by the Gate 0 census, and does not
close it.**  There is a configuration in which the Gate 1A Direct closure
certificate is inhabited while the Gate 0 exhaustiveness certificate is
empty. -/
theorem gate1ADirect_closure_independent_of_gate0 :
    Nonempty (Gate1ADirectClosureCertificate emptyPacket emptyPhysical 0 1 0 0) ∧
      IsEmpty (Gate0.Gate0ToGate1AExhaustivenessCertificate (Fin 1) (fun _ _ => False)) :=
  ⟨⟨emptyClosureCertificate⟩, Gate0.gate0Exhaustiveness_not_definitional⟩

/-- **Ford–Maynard scope firewall (Section 22).**  The canonical Gate 1A Direct
statement is a statement about one physical source; it quantifies over nothing
else, so it cannot by itself express the Gate 0 routing obligation.  Formally:
the Gate 1A statement holds in a configuration where the Gate 0 certificate is
empty. -/
theorem gate1ADirect_does_not_imply_gate0 :
    Gate1ADirectAllMCommonWeightBPP emptyPhysical 0 1 0 0 ∧
      IsEmpty (Gate0.Gate0ToGate1AExhaustivenessCertificate (Fin 1) (fun _ _ => False)) :=
  ⟨emptyClosureCertificate.toCanonicalStatement, Gate0.gate0Exhaustiveness_not_definitional⟩

end TwinPrimeProject.NANC.Gate1A.V98
