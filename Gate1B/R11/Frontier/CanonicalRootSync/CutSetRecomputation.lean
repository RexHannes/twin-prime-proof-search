/-
# Gate1B / R11 / Frontier / CanonicalRootSync : cut-set recomputation  (P9)

Append-only module.  **No legacy node is deleted**: the legacy graph of
`Gate1B/R11/Frontier/Latest/CurrentStatusLatest.lean` is re-ascribed verbatim (§1), and the new
canonical-sync graph *contains* all twelve legacy owners as nodes (§2) — they are simply no
longer predecessors of the canonical route to `R11`.

Both minimal open cut sets are **computed** from the graphs and checked by the kernel.

* legacy cut to `R11`: the twelve owners (unchanged, still live);
* canonical-sync cut to `R11`: ten nodes — three *missing exact bridges* and seven analytic
  interfaces, of which exactly one, `j2ResidualCenteredBound`, is the surviving `j = 2` owner.

The reduction is therefore **conditional**: it trades twelve legacy analytic owners for ten open
nodes, three of which are exact-algebra bridges that are not yet proved for the physical chart.
-/
import Gate1B.R11.Frontier.CanonicalRootSync.OwnerBridge

namespace Gate1B.R11.Frontier.CanonicalRootSync

/-! ## 1. The legacy graph, preserved -/

/-- The legacy minimal open cut set to `R11`, re-ascribed from the previous bank.  If the legacy
computation ever changed, this theorem would break. -/
theorem legacy_cut_preserved :
    Gate1B.R11.Frontier.Latest.cutSet Gate1B.R11.Frontier.Latest.Node.r11 =
      [Gate1B.R11.Frontier.Latest.Node.d2PositiveMoment,
        Gate1B.R11.Frontier.Latest.Node.exceptionalZeroWedge,
        Gate1B.R11.Frontier.Latest.Node.d2UnitCovariance,
        Gate1B.R11.Frontier.Latest.Node.d1CenteredCovariance,
        Gate1B.R11.Frontier.Latest.Node.globalSourceCrossEnergy,
        Gate1B.R11.Frontier.Latest.Node.fullCircleFourierOwnership,
        Gate1B.R11.Frontier.Latest.Node.rRestMasks,
        Gate1B.R11.Frontier.Latest.Node.fivePrimeChamber,
        Gate1B.R11.Frontier.Latest.Node.d3Construction,
        Gate1B.R11.Frontier.Latest.Node.rowConsumerResidueOscillation,
        Gate1B.R11.Frontier.Latest.Node.realFordGrammarObligation,
        Gate1B.R11.Frontier.Latest.Node.conditionalConsumerComparison] :=
  Gate1B.R11.Frontier.Latest.cutSet_r11

/-- The legacy cut has twelve nodes. -/
theorem legacy_cut_length :
    (Gate1B.R11.Frontier.Latest.cutSet Gate1B.R11.Frontier.Latest.Node.r11).length = 12 := by
  rw [legacy_cut_preserved]; rfl

/-! ## 2. The canonical-sync graph -/

/-- The status of a node of the canonical-sync graph. -/
inductive CStatus
  /-- kernel-proved in this layer -/
  | kernelProved
  /-- an exact algebraic bridge that is *not* proved for the physical chart -/
  | exactBridgeMissing
  /-- an analytic interface, never inhabited -/
  | analyticOpen
  /-- a legacy owner, retained in the graph, neither proved nor refuted -/
  | legacyOpen
  /-- a downstream target -/
  | target
  deriving DecidableEq, Repr

/-- The nodes of the canonical-sync graph.  Every legacy owner is retained. -/
inductive CNode
  -- kernel-proved canonical algebra
  | canonicalRootIdentity
  | rootEqualsR11Residual
  | kFiveIdentity
  | j2RawSplit
  | pascadiFirewall
  | wrightPrefix
  | openBoxCertificate
  -- exact bridges still missing for the physical chart
  | rootChartRealisation
  | rankDecompositionRealisation
  | j2CenteredSplitRealisation
  -- analytic interfaces
  | canonicalRootErrorBudget
  | branchBound1
  | branchBound3
  | branchBound4
  | branchBound5
  | principalBudget
  | j2ResidualCenteredBound
  -- legacy owners, retained
  | legacyD2PositiveMoment
  | legacyExceptionalZeroWedge
  | legacyD2UnitCovariance
  | legacyD1CenteredCovariance
  | legacyGlobalSourceCrossEnergy
  | legacyFullCircleFourierOwnership
  | legacyRRestMasks
  | legacyFivePrimeChamber
  | legacyD3Construction
  | legacyRowConsumerResidueOscillation
  | legacyRealFordGrammarObligation
  | legacyConditionalConsumerComparison
  -- downstream
  | r11Canonical
  | r11ToHstarSplice
  | hstar
  | gate1B
  deriving DecidableEq, Repr

open CNode CStatus

/-- The status of every canonical-sync node. -/
def cstatus : CNode → CStatus
  | canonicalRootIdentity => kernelProved
  | rootEqualsR11Residual => kernelProved
  | kFiveIdentity => kernelProved
  | j2RawSplit => kernelProved
  | pascadiFirewall => kernelProved
  | wrightPrefix => kernelProved
  | openBoxCertificate => kernelProved
  | rootChartRealisation => exactBridgeMissing
  | rankDecompositionRealisation => exactBridgeMissing
  | j2CenteredSplitRealisation => exactBridgeMissing
  | canonicalRootErrorBudget => analyticOpen
  | branchBound1 => analyticOpen
  | branchBound3 => analyticOpen
  | branchBound4 => analyticOpen
  | branchBound5 => analyticOpen
  | principalBudget => analyticOpen
  | j2ResidualCenteredBound => analyticOpen
  | legacyD2PositiveMoment => legacyOpen
  | legacyExceptionalZeroWedge => legacyOpen
  | legacyD2UnitCovariance => legacyOpen
  | legacyD1CenteredCovariance => legacyOpen
  | legacyGlobalSourceCrossEnergy => legacyOpen
  | legacyFullCircleFourierOwnership => legacyOpen
  | legacyRRestMasks => legacyOpen
  | legacyFivePrimeChamber => legacyOpen
  | legacyD3Construction => legacyOpen
  | legacyRowConsumerResidueOscillation => legacyOpen
  | legacyRealFordGrammarObligation => legacyOpen
  | legacyConditionalConsumerComparison => legacyOpen
  | r11Canonical => target
  | r11ToHstarSplice => target
  | hstar => target
  | gate1B => target

/-- The dependencies of every canonical-sync node: exactly what `r11_of_canonical_route`
consumes, plus the retained legacy nodes (which nothing on the canonical route consumes). -/
def cdeps : CNode → List CNode
  | canonicalRootIdentity => []
  | rootEqualsR11Residual => [canonicalRootIdentity]
  | kFiveIdentity => []
  | j2RawSplit => [kFiveIdentity]
  | pascadiFirewall => []
  | wrightPrefix => []
  | openBoxCertificate => [pascadiFirewall, wrightPrefix]
  | rootChartRealisation => [canonicalRootIdentity, rootEqualsR11Residual]
  | rankDecompositionRealisation => [kFiveIdentity]
  | j2CenteredSplitRealisation => [j2RawSplit]
  | canonicalRootErrorBudget => []
  | branchBound1 => []
  | branchBound3 => []
  | branchBound4 => []
  | branchBound5 => []
  | principalBudget => []
  | j2ResidualCenteredBound => []
  | legacyD2PositiveMoment => []
  | legacyExceptionalZeroWedge => []
  | legacyD2UnitCovariance => []
  | legacyD1CenteredCovariance => []
  | legacyGlobalSourceCrossEnergy => []
  | legacyFullCircleFourierOwnership => []
  | legacyRRestMasks => []
  | legacyFivePrimeChamber => []
  | legacyD3Construction => []
  | legacyRowConsumerResidueOscillation => []
  | legacyRealFordGrammarObligation => []
  | legacyConditionalConsumerComparison => []
  | r11Canonical =>
      [rootChartRealisation, rankDecompositionRealisation, j2CenteredSplitRealisation,
        canonicalRootErrorBudget, branchBound1, branchBound3, branchBound4, branchBound5,
        principalBudget, j2ResidualCenteredBound]
  | r11ToHstarSplice => [r11Canonical]
  | hstar => [r11Canonical, r11ToHstarSplice]
  | gate1B => [hstar]

/-- Every node of the canonical-sync graph. -/
def callNodes : List CNode :=
  [canonicalRootIdentity, rootEqualsR11Residual, kFiveIdentity, j2RawSplit, pascadiFirewall,
    wrightPrefix, openBoxCertificate, rootChartRealisation, rankDecompositionRealisation,
    j2CenteredSplitRealisation, canonicalRootErrorBudget, branchBound1, branchBound3,
    branchBound4, branchBound5, principalBudget, j2ResidualCenteredBound,
    legacyD2PositiveMoment, legacyExceptionalZeroWedge, legacyD2UnitCovariance,
    legacyD1CenteredCovariance, legacyGlobalSourceCrossEnergy, legacyFullCircleFourierOwnership,
    legacyRRestMasks, legacyFivePrimeChamber, legacyD3Construction,
    legacyRowConsumerResidueOscillation, legacyRealFordGrammarObligation,
    legacyConditionalConsumerComparison, r11Canonical, r11ToHstarSplice, hstar, gate1B]

/-- One step of dependency expansion. -/
def cexpand (l : List CNode) : List CNode := (l ++ l.flatMap cdeps).eraseDups

/-- The dependency closure of a node (enough fuel for this graph). -/
def cclosure (n : CNode) : List CNode := Nat.rec [n] (fun _ prev => cexpand prev) 6

/-- A node is *open* if it is a missing exact bridge, an analytic interface, or a retained legacy
owner. -/
def copen (n : CNode) : Bool :=
  cstatus n = exactBridgeMissing || cstatus n = analyticOpen || cstatus n = legacyOpen

/-- The open cut set of a node in the canonical-sync graph. -/
def ccutSet (n : CNode) : List CNode :=
  callNodes.filter (fun m => m ∈ cclosure n ∧ copen m ∧ m ≠ n)

/-- **The canonical-sync minimal open cut set to `R11`** — computed, kernel-checked.  Ten nodes:
three missing exact bridges and seven analytic interfaces. -/
theorem ccutSet_r11 :
    ccutSet r11Canonical =
      [rootChartRealisation, rankDecompositionRealisation, j2CenteredSplitRealisation,
        canonicalRootErrorBudget, branchBound1, branchBound3, branchBound4, branchBound5,
        principalBudget, j2ResidualCenteredBound] := by
  decide +kernel

/-- The canonical-sync cut has ten nodes; the legacy cut has twelve. -/
theorem ccutSet_r11_length : (ccutSet r11Canonical).length = 10 := by
  rw [ccutSet_r11]; rfl

/-- **Exactly one analytic owner survives inside `j = 2`.** -/
theorem unique_j2_owner :
    (ccutSet r11Canonical).filter (fun n => n = j2ResidualCenteredBound)
      = [j2ResidualCenteredBound] := by
  decide +kernel

/-- The twelve retained legacy owner nodes. -/
def legacyOwnerNodes : List CNode :=
  [legacyD2PositiveMoment, legacyExceptionalZeroWedge, legacyD2UnitCovariance,
    legacyD1CenteredCovariance, legacyGlobalSourceCrossEnergy, legacyFullCircleFourierOwnership,
    legacyRRestMasks, legacyFivePrimeChamber, legacyD3Construction,
    legacyRowConsumerResidueOscillation, legacyRealFordGrammarObligation,
    legacyConditionalConsumerComparison]

/-- All twelve legacy owners are retained as nodes of the canonical-sync graph. -/
theorem legacy_owners_retained : ∀ n ∈ legacyOwnerNodes, n ∈ callNodes := by decide +kernel

/-- **No legacy owner is consumed by the canonical route**: none appears in the canonical-sync
cut set. -/
theorem legacy_owners_offroute : ∀ n ∈ legacyOwnerNodes, n ∉ ccutSet r11Canonical := by
  decide +kernel

/-- Twelve legacy owners are retained. -/
theorem legacyOwnerNodes_length : legacyOwnerNodes.length = 12 := rfl

/-- The additional cut from `R11` to Gate 1B is unchanged in the canonical-sync graph: the splice
and `HSTAR` are still downstream targets, and `R11` is still open. -/
theorem downstream_unchanged :
    cstatus r11Canonical = target ∧ cstatus hstar = target ∧ cstatus gate1B = target
      ∧ r11Canonical ∈ cclosure gate1B := by decide +kernel

end Gate1B.R11.Frontier.CanonicalRootSync
