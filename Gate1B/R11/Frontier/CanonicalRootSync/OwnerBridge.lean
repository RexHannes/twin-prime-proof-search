/-
# Gate1B / R11 / Frontier / CanonicalRootSync : old owner → canonical root bridge  (P2)

Append-only module.  Nothing pre-existing is edited, renamed, weakened or deleted, and **no old
owner is discharged**: the verdicts below are about the *canonical route*, never about the truth
of an owner.

The twelve currently open owners of `Gate1B/R11/Frontier/Latest/CurrentStatusLatest.lean` are
classified with the five labels of the brief.  The classification rule is fixed in advance and is
never by naming similarity:

* `independentOwner` — there is a **countermodel** in the repository proving the owner is not
  implied by the exact identities of the canonical layer.  This label overrides every other one;
* `absorbedByCanonicalRoot` — the owner is **not consumed** by the canonical route: the R11
  scalar target is derived without it by `r11_of_canonical_route`, whose binder list is the
  witness.  The absorption is *conditional on the exact bridges of that theorem*, which are
  hypotheses and are **not** inhabited for the physical chart (see `missingBridges`);
* `exactSubowner` — an exact identity of this layer exhibits the owner's quantity as a summand of
  the canonical root.  No owner earns this label yet;
* `interfaceOnly` — the node is an external analytic interface, not an owner;
* `bridgeNotProved` — neither a bridge theorem nor a countermodel exists.  This is the honest
  default and it is used wherever nothing is proved.
-/
import Gate1B.R11.Frontier.CanonicalRootSync.CanonicalConditionalClosure
import Gate1B.R11.Frontier.Latest.FrontierAlignment

namespace Gate1B.R11.Frontier.CanonicalRootSync

/-! ## 1. The owners and the verdicts -/

/-- The twelve currently open owners of the legacy minimal cut set to `R11`. -/
inductive OpenOwner
  | d2PositiveMoment
  | exceptionalZeroWedge
  | d2UnitCovariance
  | d1CenteredCovariance
  | globalSourceCrossEnergy
  | fullCircleFourierOwnership
  | rRestMasks
  | fivePrimeChamber
  | d3Construction
  | rowConsumerResidueOscillation
  | realFordGrammarObligation
  | conditionalConsumerComparison
  deriving DecidableEq, Repr, Fintype

/-- The five admissible verdicts of the old → canonical bridge audit. -/
inductive BridgeVerdict
  | absorbedByCanonicalRoot
  | exactSubowner
  | independentOwner
  | interfaceOnly
  | bridgeNotProved
  deriving DecidableEq, Repr

open OpenOwner BridgeVerdict

/-- The verdict of every open owner.  Each value is justified by a theorem or a countermodel in
§2; no verdict is assigned by naming similarity. -/
def bridge : OpenOwner → BridgeVerdict
  | d2PositiveMoment => absorbedByCanonicalRoot
  | exceptionalZeroWedge => absorbedByCanonicalRoot
  | d2UnitCovariance => absorbedByCanonicalRoot
  | d1CenteredCovariance => absorbedByCanonicalRoot
  | globalSourceCrossEnergy => absorbedByCanonicalRoot
  | fullCircleFourierOwnership => absorbedByCanonicalRoot
  | rRestMasks => absorbedByCanonicalRoot
  | fivePrimeChamber => absorbedByCanonicalRoot
  | d3Construction => absorbedByCanonicalRoot
  | rowConsumerResidueOscillation => independentOwner
  | realFordGrammarObligation => bridgeNotProved
  | conditionalConsumerComparison => bridgeNotProved

/-- **No owner is discharged.**  `absorbedByCanonicalRoot` is a statement about the canonical
route only; there is no verdict in this audit meaning "proved" or "discharged". -/
theorem no_owner_discharged :
    ∀ o : OpenOwner, bridge o = absorbedByCanonicalRoot ∨ bridge o = independentOwner
      ∨ bridge o = bridgeNotProved := by decide

/-- The owners absorbed by the canonical route. -/
def absorbedOwners : List OpenOwner :=
  [d2PositiveMoment, exceptionalZeroWedge, d2UnitCovariance, d1CenteredCovariance,
    globalSourceCrossEnergy, fullCircleFourierOwnership, rRestMasks, fivePrimeChamber,
    d3Construction]

/-- The owners that are still independent, or for which no bridge is proved. -/
def stillIndependentOwners : List OpenOwner :=
  [rowConsumerResidueOscillation, realFordGrammarObligation, conditionalConsumerComparison]

/-- The absorbed list is exactly the set of owners with the absorbed verdict. -/
theorem absorbedOwners_spec (o : OpenOwner) :
    o ∈ absorbedOwners ↔ bridge o = absorbedByCanonicalRoot := by revert o; decide

/-- The complementary list is exactly the set of owners that are not absorbed. -/
theorem stillIndependentOwners_spec (o : OpenOwner) :
    o ∈ stillIndependentOwners ↔ bridge o ≠ absorbedByCanonicalRoot := by revert o; decide

/-- Nine owners are absorbed by the canonical route, three are not. -/
theorem owner_counts : absorbedOwners.length = 9 ∧ stillIndependentOwners.length = 3 := by
  constructor <;> rfl

/-! ## 2. The justifications -/

/-- **Justification of every `absorbedByCanonicalRoot` verdict.**  The R11 scalar target is
derived from the canonical route, whose hypotheses are three exact bridges and six analytic
interfaces — and *no* legacy owner.  The statement is the witness: the binder list mentions none
of the twelve owners. -/
theorem absorption_witness
    {F Root Err B1 B2 B3 B4 B5 Cen Prin : ℝ → ℝ} {S0 : ℕ}
    (hroot : ∀ x, F x = Root x + Err x)
    (hdecomp : ∀ x, Root x = B1 x + B2 x + B3 x + B4 x + B5 x)
    (hj2 : ∀ x, B2 x = Cen x + Prin x)
    (hErr : CanonicalRootErrorBudget Err S0)
    (hB1 : ScalarBudget B1 (S0 + 2)) (hB3 : ScalarBudget B3 (S0 + 2))
    (hB4 : ScalarBudget B4 (S0 + 2)) (hB5 : ScalarBudget B5 (S0 + 2))
    (hPrin : ScalarBudget Prin (S0 + 2))
    (hCen : J2ResidualCenteredBound Cen S0) :
    R11ScalarTarget F S0 :=
  r11_of_canonical_route hroot hdecomp hj2 hErr hB1 hB3 hB4 hB5 hPrin hCen

/-- **Justification of the `independentOwner` verdict.**  The old node
`RowConsumerResidueOscillation` fails in the sharpness instance of the existing bank, so it is
not implied by any universally valid identity — in particular not by the canonical root
identity.  This is the pre-existing countermodel, re-ascribed here, not a new claim. -/
theorem independence_witness :
    ¬ Gate1B.R11.Frontier.ResidueProj.RowConsumerResidueOscillation
        (α := fun _ : Fin 1 => Fin 2) (fun _ => 1) {2} {0}
        Gate1B.R11.Frontier.ResidueProj.sharpK Gate1B.R11.Frontier.ResidueProj.sharpRes 0 :=
  Gate1B.R11.Frontier.Latest.sharp_rowConsumer_oscillation_fails

/-- The independence verdict is recorded only for the owner that has the countermodel. -/
theorem independence_verdict_unique (o : OpenOwner) :
    bridge o = independentOwner ↔ o = rowConsumerResidueOscillation := by revert o; decide

/-! ## 3. The missing bridges -/

/-- The exact bridges that the canonical route *assumes* and that are **not** proved for the
physical chart.  Absorption is conditional on these. -/
inductive MissingBridge
  /-- the canonical root chart: that the physical `F₁₁^new` really is the canonical root sum
  plus its error, for the physical source and comparison -/
  | rootChartRealisation
  /-- the K = 5 rank decomposition of the physical root into its five branch families -/
  | rankDecompositionRealisation
  /-- the centered / principal split of the physical `j = 2` branch -/
  | j2CenteredSplitRealisation
  deriving DecidableEq, Repr, Fintype

/-- The three missing bridges, listed. -/
def missingBridges : List MissingBridge :=
  [MissingBridge.rootChartRealisation, MissingBridge.rankDecompositionRealisation,
    MissingBridge.j2CenteredSplitRealisation]

/-- Exactly three exact bridges are missing. -/
theorem missingBridges_length : missingBridges.length = 3 := rfl

/-- **The bridges are satisfiable but not inhabited for the physical chart.**  They are
identities, so they are consistent (`canonical_route_bridges_satisfiable`); nothing in this
repository supplies them for the physical source, which is exactly why they are listed as
missing. -/
theorem missing_bridges_are_identities :
    ∃ (F Root Err B1 B2 B3 B4 B5 Cen Prin : ℝ → ℝ),
      (∀ x, F x = Root x + Err x) ∧ (∀ x, Root x = B1 x + B2 x + B3 x + B4 x + B5 x)
        ∧ (∀ x, B2 x = Cen x + Prin x) :=
  canonical_route_bridges_satisfiable

end Gate1B.R11.Frontier.CanonicalRootSync
