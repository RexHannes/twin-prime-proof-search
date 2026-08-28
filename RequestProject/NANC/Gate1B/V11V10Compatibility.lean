import RequestProject.NANC.Gate1B.V11PairModToV10Leaves

/-!
# V11 · Gate 1B — safe logical compatibility with V10

**V10's closure theorem is not duplicated.**  The single theorem below
*applies* `TwinPrimeProject.Gate1BV10.gate1B_closed_of_exact_inputs` after
assembling its input structure from

* the v11 analytic-leaf bundle (the four open analytic leaves), and
* the V10 source pins, normalisation pins and packet census, which are
  **separate explicit hypotheses supplied by the user** and are *not* produced
  by any v11 construction.

Nothing here inhabits `Gate1BClosureInputs`, and Gate 1B remains open.
-/

namespace TwinPrimeProject
namespace Gate1BV11

open Finset Gate1BDet2

/-- **SAFE V10 COMPATIBILITY.**  Given the four v11 analytic leaves *and* the
V10 zero/source pins, normalisation pins, packet census and budget, V10's own
closure theorem applies.  Every non-analytic ingredient is an explicit
hypothesis: v11 supplies none of them. -/
theorem gate1B_closed_of_v11_leaves_and_v10_pins
    {SourceIdx : Type} [Fintype SourceIdx] [DecidableEq SourceIdx]
    {sourceValue : SourceIdx → ℝ} {total bound uncovered : ℝ}
    (face : Gate1BV10.Gate1BLeaf → Finset SourceIdx)
    (leafValue leafBudget : Gate1BV10.Gate1BLeaf → ℝ)
    (canonicalTotal residual residualBudget : ℝ)
    -- the v11 analytic-leaf bundle
    (bundle : V11AnalyticLeafBundle leafValue leafBudget)
    -- the V10 packet census
    (sourcePartitionExact : ∀ x : SourceIdx, ∃ l, x ∈ face l)
    (noDoubleSpendingBookkeeping : ∀ l l', l ≠ l' → Disjoint (face l) (face l'))
    (fixedSwitchedReassemblyExact : ∀ l, leafValue l = ∑ x ∈ face l, sourceValue x)
    -- the V10 normalisation pins
    (S1NormalizationPin : canonicalTotal = ∑ x : SourceIdx, sourceValue x)
    (S2DeltaScalarPin : total = canonicalTotal - residual)
    -- the banked remainder leaf
    (allBankedLeafBounds : |leafValue .banked| ≤ leafBudget .banked)
    -- the V10 zero/source fork
    (zeroFork : residual = 0 ∨ |residual| ≤ residualBudget)
    (residualBudget_nonneg : 0 ≤ residualBudget)
    (multiplicityBudget : (∑ l, leafBudget l) + residualBudget ≤ bound)
    (gate0Exhaustive : GlobalGate0Exhaustive uncovered) :
    Gate1BClosed total bound uncovered :=
  Gate1BV10.gate1B_closed_of_exact_inputs
    { face := face
      leafValue := leafValue
      leafBudget := leafBudget
      canonicalTotal := canonicalTotal
      residual := residual
      residualBudget := residualBudget
      sourcePartitionExact := sourcePartitionExact
      noDoubleSpendingBookkeeping := noDoubleSpendingBookkeeping
      fixedSwitchedReassemblyExact := fixedSwitchedReassemblyExact
      S1NormalizationPin := S1NormalizationPin
      S2DeltaScalarPin := S2DeltaScalarPin
      highPrimeLeaf := bundle.highPrimeLeaf
      sameQLeaf := bundle.sameQLeaf
      crossModLeaf := bundle.crossModLeaf
      H9Leaf := bundle.H9Leaf
      allBankedLeafBounds := allBankedLeafBounds
      zeroFork := zeroFork
      residualBudget_nonneg := residualBudget_nonneg
      multiplicityBudget := multiplicityBudget
      gate0Exhaustive := gate0Exhaustive }

/-- **Guard.**  The analytic leaves alone do not close Gate 1B: a bundle exists
for data whose `Gate1BClosed` conclusion is false, so the V10 source pins are
load-bearing. -/
theorem leaves_alone_do_not_close_gate1B :
    Nonempty (V11AnalyticLeafBundle (fun _ => 0) (fun _ => 0)) ∧
      ¬ Gate1BClosed 2 1 0 := by
  refine ⟨⟨⟨by norm_num, by norm_num, by norm_num, by norm_num⟩⟩, ?_⟩
  exact Gate1BV10.gate1BClosed_not_automatic

end Gate1BV11
end TwinPrimeProject
