/-
NANC V5.1 — THE CONSERVATIVE CONDITIONAL ENDGAME WRAPPER.

The parent controlling layer already carries the endgame package
`ShiftedPrimeFMEndgamePackage`; it is neither duplicated nor modified.  V5.1 only
*wraps* it so that the research DAG is exactly

    FullFMTypeII_OneSixth
        +  FMLemma718RoughBound
        +  Gate-0 analytic package
        +  Gate-2 source-specific cellsum / endgame package
             |
             v
      weightedTwinMassPositive
             |
             v
      a finite explicit twin pair.

Every deep analytic arrow stays an explicit package **field**; nothing is hidden
inside a proof term.  The only Lean deduction is the inherited finite step

    positive weighted twin mass  ⟹  ∃ p ∈ window, p and p+2 prime.

Twin-prime infinitude is NOT declared, and the implication
`FullFMTypeII_OneSixth → weightedTwinMassPositive` is deliberately NOT encoded on
its own: the Lemma-7.18 antecedent is carried alongside it.
-/
import Mathlib
import RequestProject.NANC.V5_1.Gate02StatusPatch

namespace NANC.V5_1

open NANC.V4 NANC.V5 NANC.V5.Controlling

/-- The data of the V5.1 endgame wrapper: the parent endgame data together with
the Lemma-7.18 rough-bound data. -/
structure V51EndgameData where
  /-- The inherited endgame data of the controlling layer. -/
  parent : EndgamePackageData
  /-- The data of the Lemma-7.18 rough-bound reading. -/
  lemma718 : Lemma718Data

/-- **UNINHABITED.**  The V5.1 conditional endgame package: the parent package
(which already carries Gate-0 Type I, comparison regularity, the arbitrary
coefficient Type-II hypothesis, `FM-N2-CELLSUM-UPPER45`, its ε-uniformity, the
Theorem-8.3 mass and the positivity certificate) **plus** the Lemma-7.18
rough-bound antecedent. -/
structure V51ShiftedPrimeEndgamePackage (E : V51EndgameData) : Prop where
  /-- The inherited controlling package. -/
  parentPackage : ShiftedPrimeFMEndgamePackage E.parent
  /-- The second Gate-2 antecedent: the Lemma-7.18 rough bound as stated. -/
  lemma718RoughBound : FMLemma718RoughBound E.lemma718

namespace V51ShiftedPrimeEndgamePackage

variable {E : V51EndgameData}

/-- Projection: the full arbitrary-coefficient Type-II antecedent. -/
theorem proj_fullFMTypeII (P : V51ShiftedPrimeEndgamePackage E) :
    FullFMTypeIIAtOneSixth E.parent.X E.parent.mRangeOf E.parent.nRangeOf E.parent.dwM
      E.parent.dwN E.parent.wC E.parent.eps E.parent.typeIITarget :=
  P.parentPackage.fullFMTypeII

/-- Projection: the Lemma-7.18 rough-bound antecedent. -/
theorem proj_lemma718 (P : V51ShiftedPrimeEndgamePackage E) :
    FMLemma718RoughBound E.lemma718 := P.lemma718RoughBound

/-- Projection: the Gate-0 Type-I antecedent. -/
theorem proj_gate0TypeI (P : V51ShiftedPrimeEndgamePackage E) :
    Gate0FMTypeI E.parent.X E.parent.mRange E.parent.intervals E.parent.tauWeight E.parent.w
      E.parent.typeITarget :=
  P.parentPackage.gate0TypeI

/-- Projection: the Gate-2 source-specific cell-sum antecedent. -/
theorem proj_n2CellSumUpper (P : V51ShiftedPrimeEndgamePackage E) :
    FMN2CellSumUpperAtScale E.parent.cellData E.parent.n2x E.parent.n2logx
      (E.parent.n2errOf E.parent.eps) :=
  P.parentPackage.n2CellSumUpper

/-- Projection: the conclusion carried by the package. -/
theorem proj_twinMassPositive (P : V51ShiftedPrimeEndgamePackage E) :
    0 < weightedTwinMass E.parent.window :=
  P.parentPackage.weightedTwinMassPositive

end V51ShiftedPrimeEndgamePackage

/-- **The only Lean deduction of the endgame layer** (inherited finite step): a
V5.1 package yields an explicit twin pair in its window. -/
theorem v51EndgamePackage_gives_twin_pair {E : V51EndgameData}
    (P : V51ShiftedPrimeEndgamePackage E) :
    ∃ p ∈ E.parent.window, Nat.Prime p ∧ Nat.Prime (p + 2) :=
  endgamePackage_gives_twin_pair P.parentPackage

/-- **Both antecedents are load-bearing.**  If the Lemma-7.18 rough bound fails
for the data, no V5.1 package exists, however strong the Type-II input is. -/
theorem no_v51Package_without_lemma718 (E : V51EndgameData)
    (h : ¬ FMLemma718RoughBound E.lemma718) : ¬ V51ShiftedPrimeEndgamePackage E :=
  fun P => h P.lemma718RoughBound

/-- **The parent firewall survives.**  If the positivity certificate is `False`,
no V5.1 package exists either. -/
theorem no_v51Package_from_nothing (E : V51EndgameData)
    (h : E.parent.fmPositiveCertificate = False) : ¬ V51ShiftedPrimeEndgamePackage E :=
  fun P => no_endgamePackage_from_nothing E.parent h P.parentPackage

/-- Positivity of the weighted twin mass is a genuine extra requirement, not a
formality: on the empty window it fails. -/
theorem twinMassPositive_not_automatic : ∃ S : Finset ℕ, ¬ (0 < weightedTwinMass S) := by
  refine ⟨∅, ?_⟩
  simp [weightedTwinMass]

/-- Status entry for the V5.1 endgame wrapper. -/
def v51EndgameEntry : V51Entry where
  name := "V51ShiftedPrimeEndgamePackage"
  provenance := V51Provenance.uninhabitedInterface
  inspection := SourceInspection.notInspected
  notes :=
    "Research DAG only: FullFMTypeII_OneSixth + FMLemma718RoughBound + Gate-0 package " ++
    "+ Gate-2 cellsum/endgame package -> weightedTwinMassPositive -> finite twin pair. " ++
    "No analytic arrow is proved; twin-prime infinitude is NOT declared."

theorem v51EndgameEntry_not_leanEvidence :
    V51Entry.IsLeanEvidence v51EndgameEntry = false := rfl

end NANC.V5_1
