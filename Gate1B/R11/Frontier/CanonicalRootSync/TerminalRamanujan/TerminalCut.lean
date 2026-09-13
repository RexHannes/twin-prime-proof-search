/-
# Gate1B / R11 / Frontier / CanonicalRootSync / TerminalRamanujan : the route-level cut update
(T13)

Append-only module.  Nothing pre-existing is edited, renamed, weakened or deleted.

**The canonical cut is not shrunk.**  Since no exact realisation of the canonical centered
`j = 2` residual as the EP-M2 row moment is established (`epM2RealisationBridge` is uninhabited), the
owner `J2ResidualCenteredBound` is *retained* in the canonical cut, and the terminal Ramanujan
nodes are recorded as a **subordinate experimental route**, not as a replacement.

Both statements are computed from an explicit graph and kernel-checked:

* the canonical-sync cut of the previous run is re-ascribed verbatim (§1);
* in the refined route graph, the `j = 2` owner is still in the cut to `R11`, and the four
  terminal nodes are *not* (§2);
* the cut of the *derived* node "`j = 2` owner obtained through EP-M2" is exactly the four
  terminal nodes (§2) — the price of the subordinate route.

No `sorry`, no `admit`, no custom axiom, no `native_decide`, no `unsafe`, no `opaque`.
-/
import Gate1B.R11.Frontier.CanonicalRootSync.CutSetRecomputation
import Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.CanonicalBridge

namespace Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan

open Gate1B.R11.Frontier.CanonicalRootSync

/-! ## 1. The canonical cut, re-ascribed -/

/-- The canonical-sync minimal open cut set to `R11` is unchanged by this run; in particular it
still contains `j2ResidualCenteredBound`.  If the previous computation had changed, this
theorem would break. -/
theorem canonical_cut_retained :
    ccutSet CNode.r11Canonical =
      [CNode.rootChartRealisation, CNode.rankDecompositionRealisation,
        CNode.j2CenteredSplitRealisation, CNode.canonicalRootErrorBudget, CNode.branchBound1,
        CNode.branchBound3, CNode.branchBound4, CNode.branchBound5, CNode.principalBudget,
        CNode.j2ResidualCenteredBound] :=
  ccutSet_r11

/-- The canonical cut still has ten nodes. -/
theorem canonical_cut_length_retained : (ccutSet CNode.r11Canonical).length = 10 :=
  ccutSet_r11_length

/-! ## 2. The refined route graph -/

/-- Status of a node of the refined terminal route graph. -/
inductive TStatus
  /-- an analytic interface, never inhabited -/
  | analyticOpen
  /-- an exact identification that is not proved -/
  | exactBridgeMissing
  /-- derived in Lean from its dependencies -/
  | derived
  /-- a downstream target -/
  | target
  deriving DecidableEq, Repr

/-- Nodes of the refined route graph: the canonical `j = 2` owner, the rest of the canonical
route (abstracted into one node), and the terminal Ramanujan route below the owner. -/
inductive TNode
  | epM2TopBound
  | crossTermBudget
  | lowRamanujanBudget
  | epM2RealisationBridge
  | epM2Bound
  | j2OwnerViaTerminal
  | j2Owner
  | canonicalRest
  | r11Canonical
  deriving DecidableEq, Repr

open TNode TStatus

/-- The status of every node of the refined graph. -/
def tstatus : TNode → TStatus
  | epM2TopBound => analyticOpen
  | crossTermBudget => analyticOpen
  | lowRamanujanBudget => analyticOpen
  | epM2RealisationBridge => exactBridgeMissing
  | epM2Bound => derived
  | j2OwnerViaTerminal => derived
  | j2Owner => analyticOpen
  | canonicalRest => analyticOpen
  | r11Canonical => target

/-- Dependencies in the refined graph.  `j2Owner` has **no** dependency: it is retained as an
open owner, precisely because `epM2RealisationBridge` is not established. -/
def tdeps : TNode → List TNode
  | epM2TopBound => []
  | crossTermBudget => []
  | lowRamanujanBudget => []
  | epM2RealisationBridge => []
  | epM2Bound => [epM2TopBound, crossTermBudget, lowRamanujanBudget]
  | j2OwnerViaTerminal => [epM2Bound, epM2RealisationBridge]
  | j2Owner => []
  | canonicalRest => []
  | r11Canonical => [canonicalRest, j2Owner]

/-- Every node of the refined graph. -/
def tallNodes : List TNode :=
  [epM2TopBound, crossTermBudget, lowRamanujanBudget, epM2RealisationBridge, epM2Bound,
    j2OwnerViaTerminal, j2Owner, canonicalRest, r11Canonical]

/-- One step of dependency expansion. -/
def texpand (l : List TNode) : List TNode := (l ++ l.flatMap tdeps).eraseDups

/-- Dependency closure (enough fuel for this graph). -/
def tclosure (n : TNode) : List TNode := Nat.rec [n] (fun _ prev => texpand prev) 5

/-- A node is open if it is an analytic interface or a missing exact identification. -/
def topen (n : TNode) : Bool :=
  tstatus n = analyticOpen || tstatus n = exactBridgeMissing

/-- The open cut set of a node of the refined graph. -/
def tcutSet (n : TNode) : List TNode :=
  tallNodes.filter (fun m => m ∈ tclosure n ∧ topen m ∧ m ≠ n)

/-- **The `j = 2` owner is retained**: the cut to `R11` still contains it, and the terminal
nodes do not appear — `EPM2TopBound` is subordinate, not a replacement. -/
theorem tcutSet_r11 : tcutSet r11Canonical = [j2Owner, canonicalRest] := by decide +kernel

/-- **The price of the subordinate route**: obtaining the `j = 2` owner *through* EP-M2 costs
exactly four open nodes — the three analytic budgets and the one missing exact realisation. -/
theorem tcutSet_j2ViaTerminal :
    tcutSet j2OwnerViaTerminal =
      [epM2TopBound, crossTermBudget, lowRamanujanBudget, epM2RealisationBridge] := by decide +kernel

/-- The terminal nodes are off the canonical route: none of them is in the cut to `R11`. -/
theorem terminal_nodes_offroute :
    epM2TopBound ∉ tcutSet r11Canonical ∧ crossTermBudget ∉ tcutSet r11Canonical
      ∧ lowRamanujanBudget ∉ tcutSet r11Canonical
      ∧ epM2RealisationBridge ∉ tcutSet r11Canonical := by decide +kernel

/-- Exactly one new missing exact bridge is created by this run. -/
theorem unique_new_bridge :
    tallNodes.filter (fun n => tstatus n = exactBridgeMissing) = [epM2RealisationBridge] := by
  decide +kernel

/-- Exactly one new terminal analytic owner is created by this run, and it sits strictly below
the retained `j = 2` owner. -/
theorem terminal_owner_below_j2 :
    epM2TopBound ∈ tclosure j2OwnerViaTerminal ∧ j2OwnerViaTerminal ∉ tclosure epM2TopBound := by
  decide +kernel

end Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan
