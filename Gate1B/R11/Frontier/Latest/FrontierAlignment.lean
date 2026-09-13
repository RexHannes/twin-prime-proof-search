/-
# Gate1B / R11 / Frontier / Latest : alignment of the old formal frontier with the new one

Append-only module.  Its purpose is the first task of the continuation: an exact dependency map
between the **old formal owner** (`R_loc-top,3` / residue-aware frontier, with its cut set
`RowConsumerResidueOscillation`, `Mod3CenteredCaller`, `RealFordGrammarObligationFor`,
`ConditionalConsumerComparison`) and the **new analytic coordinates** recorded in
`CurrentStatusLatest`.

Nothing pre-existing is edited, renamed, weakened or deleted, and no open proposition is
inhabited.  Two things are *proved* here rather than asserted:

* `sharp_rowConsumer_oscillation_fails` — the old node `RowConsumerResidueOscillation` is **not**
  discharged by any universally valid identity: in the sharpness instance of the existing bank it
  is false at accuracy `0`.  Hence it is an independent owner, and it must not be re-labelled as
  one of the new analytic objects;
* `oldFrontier_reduction_still_valid` — the old deterministic reduction is still exactly the one
  the new ledger consumes: the oscillation hypothesis plus the finite budget still yields
  `RLocTop3Bound`, unchanged.
-/
import Gate1B.R11.Frontier.Latest.CurrentStatusLatest
import Gate1B.R11.Frontier.RLocTop3Reduction

namespace Gate1B.R11.Frontier.Latest

open Finset

/-! ## 1. The old cut-set nodes and their alignment status -/

/-- The nodes of the previous formal minimal cut set. -/
inductive OldCutNode
  | rowConsumerResidueOscillation
  | mod3CenteredCaller
  | realFordGrammarObligation
  | conditionalConsumerComparison
  /-- The historical Ford-grammar obligation *as originally stated* (vacuously satisfiable). -/
  | historicalFordObligationAsStated
  /-- The historical ordinary local top, already superseded by the residue-aware coordinate. -/
  | ordinaryLocalTop
  deriving DecidableEq, Repr, Fintype

/-- The possible outcomes of the alignment audit. -/
inductive Alignment
  | stillLive
  | dischargedByNewMathematics
  | superseded
  | falseOrDefective
  | strictlyStrongerThanNeeded
  | independentOwner
  deriving DecidableEq, Repr

open OldCutNode Alignment

/-- The alignment verdict for every old cut-set node. -/
def alignment : OldCutNode → Alignment
  | rowConsumerResidueOscillation => independentOwner
  | mod3CenteredCaller => independentOwner
  | realFordGrammarObligation => stillLive
  | conditionalConsumerComparison => stillLive
  | historicalFordObligationAsStated => falseOrDefective
  | ordinaryLocalTop => superseded

/-- The node of the *current* graph that each still-live old node maps to. -/
def alignmentTarget : OldCutNode → Option Node
  | rowConsumerResidueOscillation => some Node.rowConsumerResidueOscillation
  | mod3CenteredCaller => some Node.mod3CenteredCaller
  | realFordGrammarObligation => some Node.realFordGrammarObligation
  | conditionalConsumerComparison => some Node.conditionalConsumerComparison
  | historicalFordObligationAsStated => none
  | ordinaryLocalTop => none

/-- **No old node is discharged by the new mathematics.**  The audit records this explicitly, so
a later run cannot quietly delete an old owner. -/
theorem no_old_node_discharged :
    ∀ n : OldCutNode, alignment n ≠ Alignment.dischargedByNewMathematics := by decide

/-- Every still-live or independent old node maps into the current graph, and its target is
recorded there as open (or as an external analytic input, for the mod-3 caller). -/
theorem alignment_targets_are_open :
    evidence Node.rowConsumerResidueOscillation = Evidence.open_
      ∧ evidence Node.realFordGrammarObligation = Evidence.open_
      ∧ evidence Node.conditionalConsumerComparison = Evidence.open_
      ∧ evidence Node.mod3CenteredCaller = Evidence.externalAnalytic := by decide

/-- Every old node that the current graph still consumes appears in the computed cut set to
`R11`. -/
theorem old_live_nodes_in_cutSet :
    Node.rowConsumerResidueOscillation ∈ cutSet Node.r11
      ∧ Node.realFordGrammarObligation ∈ cutSet Node.r11
      ∧ Node.conditionalConsumerComparison ∈ cutSet Node.r11 := by decide

/-! ## 2. The bridge theorems -/

open ResidueProj

/-- **The old node is not a rename of anything already proved.**  In the sharpness instance of
the existing bank the residue-fibre oscillation of the selected row consumer is *not* zero: if it
were, the row consumer would be residue-determined and `R_loc-top,3` would vanish exactly, which
contradicts the kernel-proved value `1`.

Consequently `RowConsumerResidueOscillation` is an independent owner: no universally valid
identity — in particular none of the deterministic identities banked in this layer — can
discharge it. -/
theorem sharp_rowConsumer_oscillation_fails :
    ¬ RowConsumerResidueOscillation (α := fun _ : Fin 1 => Fin 2) (fun _ => 1) {2} {0}
        sharpK sharpRes 0 := by
  intro h
  obtain ⟨rho, hdet, happrox⟩ := rowConsumerResidueProfile_of_oscillation h
  have heq : rowConsumer (fun _ => 1) {2} {0} sharpK = rho := by
    funext z
    have hz := happrox z
    have : |rowConsumer (fun _ => 1) {2} {0} sharpK z - rho z| = 0 :=
      le_antisymm hz (abs_nonneg _)
    have := abs_eq_zero.mp this
    linarith
  have hdet' : ResidueDetermined sharpRes (rowConsumer (fun _ => 1) {2} {0} sharpK) := by
    rw [heq]; exact hdet
  have hzero :
      RlocTop3 (fun _ => 1) {2} {0} sharpK sharpRes [0] sharpW = 0 :=
    RlocTop3_eq_zero_of_residueDetermined_rowConsumer (fun _ => 1) {2} {0} sharpK sharpRes
      (by simp) (by simp) sharpW hdet'
  exact sharp_RlocTop3_ne_zero hzero

/-- **The old deterministic reduction is still exactly the consumer of the new ledger.**  The
oscillation hypothesis together with the finite arithmetic budget still gives the physical
`R_loc-top,3` bound: the new analytic coordinates changed nothing on this path, and the old
reduction is preserved verbatim. -/
theorem oldFrontier_reduction_still_valid {ι : Type} [Fintype ι] [DecidableEq ι]
    {α : ι → Type} [∀ i, Fintype (α i)] [∀ i, Nonempty (α i)]
    {lam : ℕ → ℚ} {Ds Ns : Finset ℕ} {K : (∀ i, α i) → ℕ → ℚ} {res : ∀ i, α i → ℕ}
    {eps Mw : ℚ} {l : List ι} (hl : l.Nodup) (hne : l ≠ []) (W : (∀ i, α i) → ℚ)
    (h : RowConsumerResidueOscillation lam Ds Ns K res eps)
    (hW : ∑ x, |W x| ≤ Mw) {xr L S0 C : ℝ}
    (hfinal : ((Mw * 2 ^ l.length * eps : ℚ) : ℝ) ≤ C * xr * L ^ (-S0)) :
    RLocTop3Bound lam Ds Ns K res l W xr L S0 C :=
  RLocTop3Bound_of_oscillation hl hne W h hW hfinal

/-! ## 3. What the alignment does *not* claim -/

/-- The alignment audit does not claim that the old frontier is closed: `R_loc-top,3` remains
open, and its owner is still recorded in the current cut set. -/
theorem old_frontier_still_open :
    evidence Node.rowConsumerResidueOscillation = Evidence.open_
      ∧ Node.rowConsumerResidueOscillation ∈ cutSet Node.r11 := by decide

end Gate1B.R11.Frontier.Latest
