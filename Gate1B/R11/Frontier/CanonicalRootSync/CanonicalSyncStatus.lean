/-
# Gate1B / R11 / Frontier / CanonicalRootSync : the canonical-sync ledger  (P12, P13, final)

Append-only module.  It records, in kernel-checked form, the outcome of the canonical-root
reconciliation and answers the final question of the brief.

* §1 analytic interface discipline: every external analytic input of this layer is a named
  proposition; the list is explicit and nothing inhabits any of them;
* §2 the two cut sets and their sizes;
* §3 the classification counts of the twelve legacy owners;
* §4 the guards: `R11`, `HSTAR`, `Gate1B` remain open, and no owner is discharged.
-/
import Gate1B.R11.Frontier.CanonicalRootSync.RLocTop3Alignment

namespace Gate1B.R11.Frontier.CanonicalRootSync

/-! ## 1. Analytic interface discipline -/

/-- The external analytic inputs referenced by this layer.  All of them are *propositions*: they
are stated, never inhabited, and no axiom is introduced for any of them. -/
inductive AnalyticInterface
  /-- the Wright analytic proposition (`WrightAnalyticInput`) -/
  | wright
  /-- the literal Pascadi three-atom conditions (used only as a *predicate*, never as a theorem) -/
  | pascadi
  /-- the Blomer–Pascadi input of the previous bank -/
  | blomerPascadi
  /-- the KMS-type spectral input of the previous bank -/
  | kms
  /-- zero density -/
  | zeroDensity
  /-- Siegel–Walfisz -/
  | siegelWalfisz
  /-- the source-AP bank -/
  | sourceAPBank
  /-- the canonical root error budget -/
  | canonicalRootErrorBudget
  /-- the four non-`j=2` K = 5 branch budgets -/
  | kFiveBranchBudgets
  /-- the exact-principal budget of the `j = 2` operator -/
  | j2PrincipalBudget
  /-- the single surviving `j = 2` analytic owner -/
  | j2ResidualCenteredBound
  deriving DecidableEq, Repr, Fintype

/-- The analytic interfaces consumed by the canonical route to `R11`. -/
def routeInterfaces : List AnalyticInterface :=
  [AnalyticInterface.canonicalRootErrorBudget, AnalyticInterface.kFiveBranchBudgets,
    AnalyticInterface.j2PrincipalBudget, AnalyticInterface.j2ResidualCenteredBound]

/-- The canonical route consumes four analytic interface families, of which exactly one is the
`j = 2` residual owner. -/
theorem routeInterfaces_length : routeInterfaces.length = 4 := rfl

/-! ## 2. The two cut sets -/

/-- **Legacy cut: twelve.  Canonical-sync cut: ten.**  Both are computed from their graphs. -/
theorem cut_sizes :
    (Gate1B.R11.Frontier.Latest.cutSet Gate1B.R11.Frontier.Latest.Node.r11).length = 12
      ∧ (ccutSet CNode.r11Canonical).length = 10 :=
  ⟨legacy_cut_length, ccutSet_r11_length⟩

/-- The canonical-sync cut consists of three missing exact bridges and seven analytic nodes. -/
theorem canonical_cut_composition :
    (ccutSet CNode.r11Canonical).filter (fun n => cstatus n = CStatus.exactBridgeMissing)
        = [CNode.rootChartRealisation, CNode.rankDecompositionRealisation,
            CNode.j2CenteredSplitRealisation]
      ∧ ((ccutSet CNode.r11Canonical).filter (fun n => cstatus n = CStatus.analyticOpen)).length
        = 7 := by
  decide +kernel

/-! ## 3. The twelve legacy owners, classified -/

/-- The owners for which independence is *proved* (by countermodel). -/
def independenceProved : List OpenOwner := [OpenOwner.rowConsumerResidueOscillation]

/-- The owners for which no bridge and no countermodel exists. -/
def noBridgeProved : List OpenOwner :=
  [OpenOwner.realFordGrammarObligation, OpenOwner.conditionalConsumerComparison]

/-- **The classification counts**: 9 absorbed by the canonical route, 1 proved independent,
2 with no bridge either way — twelve in total. -/
theorem classification_counts :
    absorbedOwners.length = 9 ∧ independenceProved.length = 1 ∧ noBridgeProved.length = 2
      ∧ absorbedOwners.length + independenceProved.length + noBridgeProved.length = 12 := by
  refine ⟨rfl, rfl, rfl, rfl⟩

/-- The three lists are exactly the three verdict classes of `bridge`. -/
theorem classification_partition (o : OpenOwner) :
    (o ∈ absorbedOwners ↔ bridge o = BridgeVerdict.absorbedByCanonicalRoot)
      ∧ (o ∈ independenceProved ↔ bridge o = BridgeVerdict.independentOwner)
      ∧ (o ∈ noBridgeProved ↔ bridge o = BridgeVerdict.bridgeNotProved) := by
  revert o; decide

/-! ## 4. Guards -/

/-- **Nothing downstream is closed.**  `R11` is still a target with a nonempty open cut, and the
same holds for `HSTAR` and Gate 1B. -/
theorem downstream_still_open :
    (ccutSet CNode.r11Canonical) ≠ [] ∧ (ccutSet CNode.hstar) ≠ []
      ∧ (ccutSet CNode.gate1B) ≠ [] := by decide +kernel

/-- **No legacy owner is discharged** by this run: every verdict is `absorbed` (route-level),
`independent`, or `bridgeNotProved`. -/
theorem nothing_discharged :
    ∀ o : OpenOwner, bridge o = BridgeVerdict.absorbedByCanonicalRoot
      ∨ bridge o = BridgeVerdict.independentOwner
      ∨ bridge o = BridgeVerdict.bridgeNotProved :=
  no_owner_discharged

/-- **The absorption is conditional**: it rests on three exact bridges that are not proved for
the physical chart. -/
theorem absorption_is_conditional : missingBridges.length = 3 := missingBridges_length

end Gate1B.R11.Frontier.CanonicalRootSync
