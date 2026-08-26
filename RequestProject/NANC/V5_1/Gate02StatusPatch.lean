/-
NANC V5.1 — GATE-0 / GATE-2 STATUS PATCH.

Controlling status banked by this run:

    GATE 0:  PERMANENT ANALYTIC PASS (research), analytic inputs external /
             Lean-uninhabited.  The parent Gate-0 compilers are preserved.

    GATE 2:  CLOSED ONLY CONDITIONAL ON
                 FullFMTypeII_OneSixth
             AND
                 FMLemma718RoughBound AS STATED.

    FULL FM TYPE II:            OPEN / LEAN-UNINHABITED.
    FULL TYPE-II REASSEMBLY:    OPEN / LEAN-UNINHABITED.
    TWIN PRIMES:                NOT PROVED.
    TWIN-PRIME INFINITUDE:      NOT DECLARED.

The Gate-2 dependency is carried as *data* (`gate2Dependencies`), not as an
inhabited proposition, and the two antecedents are kept separate: `CG-11` below
records that the Type-II hypothesis alone is not the Gate-2 antecedent package.

This file also extends the external/uninhabited analytic inventory with the
two-linear-form Selberg upper sieve and the Mertens/PNT prefix-volume input.
-/
import Mathlib
import RequestProject.NANC.V5_1.N2CellSumRepairs

namespace NANC.V5_1

open NANC.V5.Controlling

/-! ### 1. The external / uninhabited analytic inventory -/

/-- Helper: an external analytic ingredient with no Lean inhabitant. -/
def externalEntry (name notes : String) : V51Entry where
  name := name
  provenance := V51Provenance.uninhabitedInterface
  inspection := SourceInspection.notInspected
  notes := notes

/-- The V5.1 external / uninhabited analytic inventory.  The first two items are
the ones this run adds to the inherited list. -/
def externalAnalyticInventory : List V51Entry :=
  [ externalEntry "two-linear-form Selberg upper sieve"
      "added in V5.1; used by the N2 cellsum architecture; no Lean inhabitant",
    externalEntry "Mertens/PNT input for the prefix-volume identity"
      "added in V5.1; no Lean inhabitant",
    externalEntry "Ford–Maynard Theorem 2.7" "inherited external interface",
    externalEntry "Ford–Maynard Theorem 4.16" "inherited external interface",
    externalEntry "Ford–Maynard Theorem 8.2" "inherited external interface",
    externalEntry "Ford–Maynard Theorem 8.3" "inherited external interface",
    externalEntry "Bombieri–Vinogradov" "inherited external interface",
    externalEntry "Brun–Titchmarsh" "inherited external interface",
    externalEntry "comparison progression asymptotics" "inherited external interface",
    externalEntry "FM comparison conditions (b.1), (b.2), (w)" "inherited external interface",
    externalEntry "FM-N2-CELLSUM-UPPER45" "controlling Gate-2 aggregate interface",
    externalEntry "epsilon-uniform N2 splice" "inherited external interface",
    externalEntry "FMLemma718RoughBound" "V5.1; provenance assumedSourceReading",
    externalEntry "N2HUniformity" "V5.1; analytic assertion, field of the above",
    externalEntry "FMShiftedPrimeT82Splice" "inherited external interface",
    externalEntry "FullFMTypeII_OneSixth" "arbitrary divisor-bounded coefficients; OPEN",
    externalEntry "Full FM Type-II reassembly" "OPEN",
    externalEntry "Twin-prime infinitude" "NOT DECLARED" ]

/-- Nothing in the external inventory is Lean evidence. -/
theorem externalAnalyticInventory_no_leanEvidence :
    externalAnalyticInventory.all (fun E => ! V51Entry.IsLeanEvidence E) = true := by decide

/-- The two ingredients V5.1 adds to the inventory are present. -/
theorem externalAnalyticInventory_has_new_items :
    (externalAnalyticInventory.map V51Entry.name).take 2 =
      ["two-linear-form Selberg upper sieve",
       "Mertens/PNT input for the prefix-volume identity"] := rfl

/-! ### 2. Gate 0 -/

/-- Gate-0 research status: a permanent analytic pass (not a Lean proof). -/
def gate0ResearchStatus : V51Provenance := V51Provenance.opusAuditedAnalyticPass

/-- Gate-0 Lean analytic status: external / uninhabited. -/
def gate0LeanAnalyticStatus : V51Provenance := V51Provenance.uninhabitedInterface

/-- The V5.1 labels agree with the parent controlling layer: no reopening and no
strengthening of Gate 0. -/
theorem gate0ResearchStatus_matches_parent :
    gate0ResearchStatus = V51Provenance.ofControl Gate0FMTypeIStatus := rfl

/-- **Permanent guard.**  `Gate0ResearchClosed ≠ Gate0LeanAnalyticProof`. -/
theorem gate0ResearchStatus_ne_leanProved :
    gate0ResearchStatus ≠ V51Provenance.leanProved := by decide

theorem gate0LeanAnalyticStatus_ne_leanProved :
    gate0LeanAnalyticStatus ≠ V51Provenance.leanProved := by decide

theorem gate0ResearchStatus_ne_leanAnalyticStatus :
    gate0ResearchStatus ≠ gate0LeanAnalyticStatus := by decide

/-! ### 3. Gate 2: the exact two-antecedent form -/

/-- The status of one antecedent of the Gate-2 conditional closure. -/
structure DependencyStatus where
  /-- The name of the antecedent. -/
  label : String
  /-- What this bank asserts about it. -/
  provenance : V51Provenance
  /-- Whether it has a Lean inhabitant.  Both current antecedents: `false`. -/
  inhabitedInLean : Bool
  deriving DecidableEq, Repr

/-- The two antecedents Gate-2 closure is conditional on. -/
structure Gate2ConditionalDependencies where
  /-- The full arbitrary-coefficient Type-II hypothesis at `1/6`. -/
  fullTypeII : DependencyStatus
  /-- The Lemma-7.18 rough-bound reading, as stated. -/
  lemma718RoughBound : DependencyStatus
  deriving DecidableEq, Repr

/-- The current values: both antecedents open / uninhabited, the second one only
an assumed source reading. -/
def gate2Dependencies : Gate2ConditionalDependencies where
  fullTypeII :=
    { label := "FullFMTypeII_OneSixth"
      provenance := V51Provenance.openStatus
      inhabitedInLean := false }
  lemma718RoughBound :=
    { label := "FMLemma718RoughBound"
      provenance := V51Provenance.assumedSourceReading
      inhabitedInLean := false }

theorem gate2Dependencies_fullTypeII_open :
    gate2Dependencies.fullTypeII.provenance = V51Provenance.openStatus := rfl

theorem gate2Dependencies_lemma718_assumedSourceReading :
    gate2Dependencies.lemma718RoughBound.provenance = V51Provenance.assumedSourceReading := rfl

theorem gate2Dependencies_none_inhabited :
    gate2Dependencies.fullTypeII.inhabitedInLean = false ∧
      gate2Dependencies.lemma718RoughBound.inhabitedInLean = false := ⟨rfl, rfl⟩

/-- The two antecedents are distinct entries: neither subsumes the other. -/
theorem gate2Dependencies_two_distinct_antecedents :
    gate2Dependencies.fullTypeII ≠ gate2Dependencies.lemma718RoughBound := by decide

/-- **CG-11.**  The Type-II hypothesis alone is not the current Gate-2 antecedent
package: the package also carries the Lemma-7.18 reading, which is a different
dependency. -/
theorem fullTypeII_alone_ne_gate2_antecedents :
    gate2Dependencies ≠
      { gate2Dependencies with lemma718RoughBound := gate2Dependencies.fullTypeII } := by
  decide

/-- V5.1 Gate-2 status labels. -/
inductive Gate2Status51 where
  /-- Gate 2 is open. -/
  | openGate
  /-- Gate 2 is closed only conditional on the two antecedents above. -/
  | conditionalOnTwoAntecedents
  /-- Gate 2 is unconditionally closed. -/
  | closed
  deriving DecidableEq, Repr

/-- The status this run banks. -/
def gate2Status51 : Gate2Status51 := Gate2Status51.conditionalOnTwoAntecedents

theorem gate2Status51_not_closed : gate2Status51 ≠ Gate2Status51.closed := by decide

/-- Gate-2 Lean analytic status stays external / uninhabited. -/
def gate2LeanAnalyticStatus : V51Provenance := V51Provenance.uninhabitedInterface

theorem gate2LeanAnalyticStatus_ne_leanProved :
    gate2LeanAnalyticStatus ≠ V51Provenance.leanProved := by decide

/-- The Gate-2 status entry, in the exact conservative wording. -/
def gate2Entry51 : V51Entry where
  name := "GATE 2"
  provenance := V51Provenance.openStatus
  inspection := SourceInspection.notInspected
  notes :=
    "CLOSED CONDITIONAL ON FullFMTypeII_OneSixth AND FMLemma718RoughBound AS STATED. " ++
    "Lean analytic status: external / uninhabited.  Twin primes NOT proved."

theorem gate2Entry51_not_leanEvidence : V51Entry.IsLeanEvidence gate2Entry51 = false := rfl

/-! ### 4. The Theorem-8.2 shifted-prime splice -/

/-- Status entry for `FMShiftedPrimeT82Splice`: Lean-uninhabited, research status
conditional, dependency table only partially source-verified. -/
def t82SpliceEntry51 : V51Entry where
  name := "FMShiftedPrimeT82Splice"
  provenance := V51Provenance.uninhabitedInterface
  inspection := SourceInspection.notInspected
  notes :=
    "LEAN: UNINHABITED.  RESEARCH: CONDITIONAL.  DEPENDENCY TABLE: PARTIALLY " ++
    "SOURCE-VERIFIED (see fmDependencyTable).  Source-specific to the shifted-prime " ++
    "comparison architecture; no claim for arbitrary ordinary sequences."

theorem t82SpliceEntry51_not_leanEvidence :
    V51Entry.IsLeanEvidence t82SpliceEntry51 = false := rfl

/-! ### 5. The programme DAG, as data -/

/-- The nodes of the current programme DAG. -/
inductive ProgrammeNode where
  /-- Gate 0. -/
  | gate0
  /-- Gate 1A. -/
  | gate1A
  /-- Gate 1B. -/
  | gate1B
  /-- The full Type-II reassembly step. -/
  | fullTypeIIReassembly
  /-- The full arbitrary-coefficient Type-II hypothesis. -/
  | fullTypeII
  /-- Gate 2. -/
  | gate2
  /-- The twin-prime conclusion. -/
  | twinPrimes
  deriving DecidableEq, Repr

/-- The status labels of the programme DAG. -/
inductive ProgrammeStatus where
  /-- Analytically closed at research level (never a Lean proof). -/
  | analyticallyClosedResearch
  /-- Open. -/
  | openNode
  /-- A conditional endgame requiring explicit antecedents. -/
  | conditionalEndgame
  /-- Not proved. -/
  | notProved
  deriving DecidableEq, Repr

/-- The current programme DAG, banked as metadata only. -/
def programmeDag : ProgrammeNode → ProgrammeStatus
  | ProgrammeNode.gate0 => ProgrammeStatus.analyticallyClosedResearch
  | ProgrammeNode.gate1A => ProgrammeStatus.openNode
  | ProgrammeNode.gate1B => ProgrammeStatus.openNode
  | ProgrammeNode.fullTypeIIReassembly => ProgrammeStatus.openNode
  | ProgrammeNode.fullTypeII => ProgrammeStatus.openNode
  | ProgrammeNode.gate2 => ProgrammeStatus.conditionalEndgame
  | ProgrammeNode.twinPrimes => ProgrammeStatus.notProved

theorem programmeDag_twinPrimes_notProved :
    programmeDag ProgrammeNode.twinPrimes = ProgrammeStatus.notProved := rfl

theorem programmeDag_fullTypeII_open :
    programmeDag ProgrammeNode.fullTypeII = ProgrammeStatus.openNode := rfl

theorem programmeDag_gate2_conditional :
    programmeDag ProgrammeNode.gate2 = ProgrammeStatus.conditionalEndgame := rfl

/-- **No automatic promotion.**  Gate 1A and Gate 1B being recorded as open nodes
leaves the Type-II reassembly and the full Type-II hypothesis open, and leaves
twin primes not proved. -/
theorem programmeDag_no_promotion :
    programmeDag ProgrammeNode.gate1A = ProgrammeStatus.openNode ∧
      programmeDag ProgrammeNode.gate1B = ProgrammeStatus.openNode ∧
      programmeDag ProgrammeNode.fullTypeIIReassembly = ProgrammeStatus.openNode ∧
      programmeDag ProgrammeNode.fullTypeII = ProgrammeStatus.openNode ∧
      programmeDag ProgrammeNode.twinPrimes = ProgrammeStatus.notProved :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- No node of the programme DAG is recorded as a Lean proof of anything: the
research label of Gate 0 is not `leanProved` in the provenance universe. -/
theorem programmeDag_gate0_research_not_leanProved :
    programmeDag ProgrammeNode.gate0 = ProgrammeStatus.analyticallyClosedResearch ∧
      gate0ResearchStatus ≠ V51Provenance.leanProved :=
  ⟨rfl, by decide⟩

end NANC.V5_1
