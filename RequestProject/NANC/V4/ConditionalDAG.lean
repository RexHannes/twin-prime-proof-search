/-
NANC V4 — the conditional Gate-2 dependency DAG.

The purpose of this file is to formalize DEPENDENCIES, not to reproduce deep
analysis.  Each node is an abstract Prop supplied as data; the endgame package is
a structure whose fields are exactly the hypotheses of the informal argument,
including the conclusion `positiveTwinMassConclusion`.

Nothing here inhabits any analytic node, and no Ford–Maynard content is hidden
inside a proof term: every proof below is a projection.
-/
import Mathlib
import RequestProject.NANC.V4.TwinMass
import RequestProject.NANC.V4.TypeIICompiler
import RequestProject.NANC.V4.N2RepairInterface
import RequestProject.NANC.V4.EndgameInterfaces

namespace NANC.V4

/-- The abstract nodes of the Gate-0/Gate-2 dependency DAG. -/
structure EndgameNodes where
  /-- Exact Gate-0 Ford–Maynard Type-I input. -/
  Gate0FMTypeI : Prop
  /-- Full arbitrary-coefficient Ford–Maynard Type-II input. -/
  FullFMTypeII : Prop
  /-- Ford–Maynard comparison regularity (b.1, b.2, growth). -/
  FMComparisonRegularity : Prop
  /-- Positivity certificate coming from the sieve-conversion theorem. -/
  FMPositiveSieveCertificate : Prop
  /-- The shifted-prime endgame splice (proposed `N₂` repair). -/
  FMShiftedPrimeEndgameSplice : Prop
  /-- The desired conclusion: positive weighted twin mass. -/
  PositiveTwinMass : Prop

/-- A structured endgame package: all five inputs together with the conclusion
they are supposed to produce.  The implication from inputs to conclusion is the
content of the external Ford–Maynard analysis and is therefore carried as the
field `positiveTwinMassConclusion`, not proved here. -/
structure FMShiftedPrimeEndgamePackage (N : EndgameNodes) : Prop where
  typeI : N.Gate0FMTypeI
  typeII : N.FullFMTypeII
  comparisonRegularity : N.FMComparisonRegularity
  sievePositivity : N.FMPositiveSieveCertificate
  endgameSplice : N.FMShiftedPrimeEndgameSplice
  positiveTwinMassConclusion :
    N.Gate0FMTypeI → N.FullFMTypeII → N.FMComparisonRegularity →
      N.FMPositiveSieveCertificate → N.FMShiftedPrimeEndgameSplice → N.PositiveTwinMass

namespace FMShiftedPrimeEndgamePackage

variable {N : EndgameNodes}

theorem gate0 (P : FMShiftedPrimeEndgamePackage N) : N.Gate0FMTypeI := P.typeI
theorem typeII_proj (P : FMShiftedPrimeEndgamePackage N) : N.FullFMTypeII := P.typeII
theorem comparison_proj (P : FMShiftedPrimeEndgamePackage N) : N.FMComparisonRegularity :=
  P.comparisonRegularity
theorem sieve_proj (P : FMShiftedPrimeEndgamePackage N) : N.FMPositiveSieveCertificate :=
  P.sievePositivity
theorem splice_proj (P : FMShiftedPrimeEndgamePackage N) : N.FMShiftedPrimeEndgameSplice :=
  P.endgameSplice

/-- The DAG conclusion: from a complete package one obtains positive twin mass. -/
theorem positiveTwinMass (P : FMShiftedPrimeEndgamePackage N) : N.PositiveTwinMass :=
  P.positiveTwinMassConclusion P.typeI P.typeII P.comparisonRegularity P.sievePositivity
    P.endgameSplice

end FMShiftedPrimeEndgamePackage

/-- The full conditional chain, written as an implication DAG. -/
theorem endgame_dag {N : EndgameNodes}
    (himp : N.Gate0FMTypeI → N.FullFMTypeII → N.FMComparisonRegularity →
      N.FMPositiveSieveCertificate → N.FMShiftedPrimeEndgameSplice → N.PositiveTwinMass) :
    N.Gate0FMTypeI → N.FullFMTypeII → N.FMComparisonRegularity →
      N.FMPositiveSieveCertificate → N.FMShiftedPrimeEndgameSplice → N.PositiveTwinMass :=
  himp

/-- Bridging the abstract DAG conclusion to the concrete finite twin statement:
if the package's `PositiveTwinMass` node is instantiated by positivity of the
weighted twin mass of a finite set `S`, a twin-prime pair in `S` exists. -/
theorem package_gives_twin_pair {N : EndgameNodes} {S : Finset ℕ}
    (hnode : N.PositiveTwinMass = (0 < weightedTwinMass S))
    (P : FMShiftedPrimeEndgamePackage N) :
    ∃ p ∈ S, Nat.Prime p ∧ Nat.Prime (p + 2) := by
  have h := P.positiveTwinMass
  rw [hnode] at h
  exact positive_weightedTwinMass_exists_twin h

/-- **No-overclaim.**  A package for arbitrary abstract nodes proves nothing
unconditionally: there are nodes for which no package exists (all nodes `False`).
-/
theorem no_package_from_nothing :
    ∃ N : EndgameNodes, ¬ FMShiftedPrimeEndgamePackage N := by
  refine ⟨⟨False, False, False, False, False, False⟩, ?_⟩
  intro P
  exact P.typeI

end NANC.V4
