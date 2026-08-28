import RequestProject.NANC.Gate1B.V10PacketReassembly
import RequestProject.NANC.Gate1B.V10HistoricalResidual
import RequestProject.NANC.Gate1BDet2.Gate1BInterfaces

/-!
# V10 · Gate 1B — the conditional closure compiler and the Type-II compiler

## Part A — Gate-1B conditional closure

`Gate1BClosureInputs` packages **exactly** the remaining independent
prerequisites as fields.  It deliberately contains **no** field
`gate1BClosed : Prop`; the four open analytic leaves
(HIGHPRIME-MSWITCH, SAMEQ, CROSSMOD, H9) appear only as per-leaf numerical bounds
that nothing in this project supplies.  The conclusion is the project's own
`TwinPrimeProject.Gate1BDet2.Gate1BClosed`.

`gate1B_closed_of_exact_inputs` is a genuine finite composition:
source partition ⟶ packet reassembly ⟶ leaf bounds ⟶ canonical/historical fork.

## Part B — the Type-II reassembly certificate

### FIRST FORMAL BLOCKER

The definition `FullFMTypeII_OneSixth` **does not exist anywhere in this
project** (nor does `FMTypeIIExactAtScale`, `Gate1AOutput`, `Gate1BOutput`, or
`Gate1ABReassemblyCertificate`).  The exact missing declaration is

    def FullFMTypeII_OneSixth : ...      -- ABSENT

Consequently **no theorem below concludes `FullFMTypeII_OneSixth`**, and none is
created as a substitute for it.  What *is* available in the bank is the
project's own uninhabited target predicate

    TwinPrimeProject.Gate1BDet2.FullTypeIIBound (typeIISum X delta : ℝ) : Prop
      := |typeIISum| ≤ X ^ (1 - delta)

and the compiler in Part B is stated against that existing predicate, with the
explicit warning that it is **not** the Ford–Maynard one-sixth statement.

Gate-1A is *not* a logical premise of the implication below; per the brief the
premises are weakened rather than padded.
-/

namespace TwinPrimeProject
namespace Gate1BV10

open Finset Gate1BDet2

/-! ## Part A — the Gate-1B closure inputs -/

/-- The five Gate-1B leaves.  The first four are the open analytic leaves; the
fifth collects everything already banked. -/
inductive Gate1BLeaf
  | highPrime
  | sameQ
  | crossMod
  | h9
  | banked
  deriving DecidableEq, Fintype, Repr

/-- **The remaining independent prerequisites of Gate-1B closure.**

Every field is an input.  There is no `gate1BClosed` field, and no field asserts
the conclusion.  This structure is *not* inhabited in this project. -/
structure Gate1BClosureInputs (SourceIdx : Type) [Fintype SourceIdx] [DecidableEq SourceIdx]
    (sourceValue : SourceIdx → ℝ) (total bound uncovered : ℝ) where
  /-- The face of the source index set carrying each leaf. -/
  face : Gate1BLeaf → Finset SourceIdx
  /-- The value of each leaf. -/
  leafValue : Gate1BLeaf → ℝ
  /-- The budget allotted to each leaf. -/
  leafBudget : Gate1BLeaf → ℝ
  /-- The canonical (comparison-centred) total. -/
  canonicalTotal : ℝ
  /-- The historical residual `R_E`. -/
  residual : ℝ
  /-- The budget allotted to the residual. -/
  residualBudget : ℝ
  /-- **sourcePartitionExact** — every physical source index is carried by a leaf. -/
  sourcePartitionExact : ∀ x : SourceIdx, ∃ l, x ∈ face l
  /-- **noDoubleSpendingBookkeeping** — no source index is carried twice. -/
  noDoubleSpendingBookkeeping : ∀ l l', l ≠ l' → Disjoint (face l) (face l')
  /-- **fixedSwitchedReassemblyExact** — each leaf value is exactly its face sum. -/
  fixedSwitchedReassemblyExact : ∀ l, leafValue l = ∑ x ∈ face l, sourceValue x
  /-- **S1NormalizationPin** — the canonical total is the raw source, unscaled. -/
  S1NormalizationPin : canonicalTotal = ∑ x : SourceIdx, sourceValue x
  /-- **S2DeltaScalarPin** — the historical total is the canonical total minus the
  residual (the sign convention of `switchedOperator_hist_eq_can_sub_residual`). -/
  S2DeltaScalarPin : total = canonicalTotal - residual
  /-- **highPrimeLeaf** — OPEN ANALYTIC LEAF (HIGHPRIME-MSWITCH). -/
  highPrimeLeaf : |leafValue .highPrime| ≤ leafBudget .highPrime
  /-- **sameQLeaf** — OPEN ANALYTIC LEAF (SAMEQ). -/
  sameQLeaf : |leafValue .sameQ| ≤ leafBudget .sameQ
  /-- **crossModLeaf** — OPEN ANALYTIC LEAF (CROSSMOD). -/
  crossModLeaf : |leafValue .crossMod| ≤ leafBudget .crossMod
  /-- **H9Leaf** — OPEN ANALYTIC LEAF (H9). -/
  H9Leaf : |leafValue .h9| ≤ leafBudget .h9
  /-- **allBankedLeafBounds** — the banked remainder respects its budget. -/
  allBankedLeafBounds : |leafValue .banked| ≤ leafBudget .banked
  /-- **zeroFork** — either the historical centring *is* the canonical one
  (`E = M`, residual `0`), or the residual is bounded.  Neither branch is proved
  here. -/
  zeroFork : residual = 0 ∨ |residual| ≤ residualBudget
  /-- The residual budget is a budget. -/
  residualBudget_nonneg : 0 ≤ residualBudget
  /-- **multiplicityBudget** — the budgets, counted with multiplicity one, fit. -/
  multiplicityBudget : (∑ l, leafBudget l) + residualBudget ≤ bound
  /-- Gate-0 exhaustiveness, the project's own interface. -/
  gate0Exhaustive : GlobalGate0Exhaustive uncovered

namespace Gate1BClosureInputs

variable {SourceIdx : Type} [Fintype SourceIdx] [DecidableEq SourceIdx]
  {sourceValue : SourceIdx → ℝ} {total bound uncovered : ℝ}

/-- The raw source is the sum of the leaf values: exact reassembly from the
partition. -/
theorem rawSource_eq_sum_leafValue
    (h : Gate1BClosureInputs SourceIdx sourceValue total bound uncovered) :
    ∑ x : SourceIdx, sourceValue x = ∑ l, h.leafValue l := by
  classical
  have hcover : (Finset.univ : Finset SourceIdx)
      = (Finset.univ : Finset Gate1BLeaf).biUnion h.face := by
    ext x
    constructor
    · intro _
      obtain ⟨l, hl⟩ := h.sourcePartitionExact x
      exact Finset.mem_biUnion.mpr ⟨l, Finset.mem_univ l, hl⟩
    · intro _
      exact Finset.mem_univ x
  have hdisj : (↑(Finset.univ : Finset Gate1BLeaf) : Set Gate1BLeaf).PairwiseDisjoint h.face := by
    intro l _ l' _ hne
    exact h.noDoubleSpendingBookkeeping l l' hne
  calc ∑ x : SourceIdx, sourceValue x
      = ∑ x ∈ (Finset.univ : Finset Gate1BLeaf).biUnion h.face, sourceValue x := by
        rw [← hcover]
    _ = ∑ l, ∑ x ∈ h.face l, sourceValue x := Finset.sum_biUnion hdisj
    _ = ∑ l, h.leafValue l :=
        Finset.sum_congr rfl fun l _ => (h.fixedSwitchedReassemblyExact l).symm

/-- Each leaf respects its budget. -/
theorem leaf_bound (h : Gate1BClosureInputs SourceIdx sourceValue total bound uncovered)
    (l : Gate1BLeaf) : |h.leafValue l| ≤ h.leafBudget l := by
  cases l
  · exact h.highPrimeLeaf
  · exact h.sameQLeaf
  · exact h.crossModLeaf
  · exact h.H9Leaf
  · exact h.allBankedLeafBounds

end Gate1BClosureInputs

/-- **GATE-1B CONDITIONAL CLOSURE COMPILER.**  From the exact inputs — and only
from them — the project's own `Gate1BClosed` follows.  The inputs are never
supplied: the four analytic leaves and the zero fork remain open. -/
theorem gate1B_closed_of_exact_inputs
    {SourceIdx : Type} [Fintype SourceIdx] [DecidableEq SourceIdx]
    {sourceValue : SourceIdx → ℝ} {total bound uncovered : ℝ}
    (h : Gate1BClosureInputs SourceIdx sourceValue total bound uncovered) :
    Gate1BClosed total bound uncovered := by
  classical
  refine ⟨?_, h.gate0Exhaustive⟩
  have hleaves : |∑ l, h.leafValue l| ≤ ∑ l, h.leafBudget l :=
    le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun l _ => h.leaf_bound l)
  have hres : |h.residual| ≤ h.residualBudget := by
    rcases h.zeroFork with hz | hb
    · rw [hz]; simpa using h.residualBudget_nonneg
    · exact hb
  have hcan : |h.canonicalTotal| ≤ ∑ l, h.leafBudget l := by
    rw [h.S1NormalizationPin, h.rawSource_eq_sum_leafValue]
    exact hleaves
  calc |total| = |h.canonicalTotal - h.residual| := congrArg abs h.S2DeltaScalarPin
    _ ≤ |h.canonicalTotal| + |h.residual| := by
        simpa [sub_eq_add_neg] using abs_add_le h.canonicalTotal (-h.residual)
    _ ≤ (∑ l, h.leafBudget l) + h.residualBudget := add_le_add hcan hres
    _ ≤ bound := h.multiplicityBudget

/-! ### Part A hostile tests -/

/-- **Hostile test 3 (Gate-1B form).**  Without leaf bounds the closure fails:
`Gate1BClosed` is not automatic. -/
theorem gate1BClosed_not_automatic : ¬ Gate1BClosed 2 1 0 := by
  unfold Gate1BClosed
  norm_num

/-- **Hostile test 5 (Gate-1B form).**  An empty source family forces the raw
source to vanish, so it cannot certify a nonzero physical total. -/
theorem empty_source_forces_zero (sourceValue : Fin 0 → ℝ) :
    ∑ x, sourceValue x = 0 := by simp

/-! ## Part B — the Type-II reassembly certificate -/

/-- **The reassembly certificate.**

It requires, for *every* legal coefficient datum: an exact packet decomposition,
legality of the transformed coefficients, a packet/source match, full coverage of
the source interval, a multiplicity (nuclear) budget and an error bound.

It does **not** contain `FullTypeIIBound` — let alone `FullFMTypeII_OneSixth`,
which is absent from the project — as a field. -/
structure FMReassemblyCertificate (Coeff SourceIdx Packet : Type)
    [Fintype SourceIdx] [DecidableEq SourceIdx] [Fintype Packet] [DecidableEq Packet]
    (legal : Coeff → Prop) (typeIISum : Coeff → ℝ) (X delta : ℝ) where
  /-- The physical source values attached to a coefficient datum. -/
  sourceValue : Coeff → SourceIdx → ℝ
  /-- The face of the source interval carried by each packet. -/
  face : Packet → Finset SourceIdx
  /-- The value of each packet. -/
  packetValue : Coeff → Packet → ℝ
  /-- The budget of each packet. -/
  packetBudget : Coeff → Packet → ℝ
  /-- The coefficient transformation performed by the reassembly. -/
  transform : Coeff → Coeff
  /-- **transformed coefficient legality.** -/
  transformedCoefficientLegality : ∀ a, legal a → legal (transform a)
  /-- **exact packet decomposition** of the Type-II sum over the source. -/
  exactPacketDecomposition : ∀ a, legal a → typeIISum a = ∑ x : SourceIdx, sourceValue a x
  /-- **packet source match.** -/
  packetSourceMatch : ∀ a p, packetValue a p = ∑ x ∈ face p, sourceValue a x
  /-- **full interval coverage.** -/
  fullIntervalCoverage : ∀ x : SourceIdx, ∃ p, x ∈ face p
  /-- No packet multiplicity: the faces are disjoint. -/
  packetDisjointness : ∀ p p', p ≠ p' → Disjoint (face p) (face p')
  /-- **error bound** on each packet. -/
  errorBound : ∀ a, legal a → ∀ p, |packetValue a p| ≤ packetBudget a p
  /-- **packet multiplicity / nuclear budget.** -/
  nuclearBudget : ∀ a, legal a → ∑ p, packetBudget a p ≤ X ^ (1 - delta)

namespace FMReassemblyCertificate

variable {Coeff SourceIdx Packet : Type}
  [Fintype SourceIdx] [DecidableEq SourceIdx] [Fintype Packet] [DecidableEq Packet]
  {legal : Coeff → Prop} {typeIISum : Coeff → ℝ} {X delta : ℝ}

/-- The source sum is the packet sum. -/
theorem sum_source_eq_sum_packet
    (cert : FMReassemblyCertificate Coeff SourceIdx Packet legal typeIISum X delta)
    (a : Coeff) :
    ∑ x : SourceIdx, cert.sourceValue a x = ∑ p, cert.packetValue a p := by
  classical
  have hcover : (Finset.univ : Finset SourceIdx)
      = (Finset.univ : Finset Packet).biUnion cert.face := by
    ext x
    constructor
    · intro _
      obtain ⟨p, hp⟩ := cert.fullIntervalCoverage x
      exact Finset.mem_biUnion.mpr ⟨p, Finset.mem_univ p, hp⟩
    · intro _
      exact Finset.mem_univ x
  have hdisj : (↑(Finset.univ : Finset Packet) : Set Packet).PairwiseDisjoint cert.face := by
    intro p _ p' _ hne
    exact cert.packetDisjointness p p' hne
  calc ∑ x : SourceIdx, cert.sourceValue a x
      = ∑ x ∈ (Finset.univ : Finset Packet).biUnion cert.face, cert.sourceValue a x := by
        rw [← hcover]
    _ = ∑ p, ∑ x ∈ cert.face p, cert.sourceValue a x := Finset.sum_biUnion hdisj
    _ = ∑ p, cert.packetValue a p :=
        Finset.sum_congr rfl fun p _ => (cert.packetSourceMatch a p).symm

end FMReassemblyCertificate

/-- **CONDITIONAL TYPE-II COMPILER.**

From the reassembly certificate — packet decomposition, source match, coverage,
error bounds and nuclear budget — the project's existing (uninhabited) predicate
`Gate1BDet2.FullTypeIIBound` follows for every legal coefficient datum.

**This is NOT `FullFMTypeII_OneSixth`**, which is absent from the project; see the
blocker note at the top of this file.  Gate-1A output is not a premise because it
is not logically necessary for this implication. -/
theorem fullTypeIIBound_of_reassemblyCertificate
    {Coeff SourceIdx Packet : Type}
    [Fintype SourceIdx] [DecidableEq SourceIdx] [Fintype Packet] [DecidableEq Packet]
    {legal : Coeff → Prop} {typeIISum : Coeff → ℝ} {X delta : ℝ}
    (cert : FMReassemblyCertificate Coeff SourceIdx Packet legal typeIISum X delta)
    (a : Coeff) (ha : legal a) :
    FullTypeIIBound (typeIISum a) X delta := by
  classical
  unfold FullTypeIIBound
  calc |typeIISum a| = |∑ p, cert.packetValue a p| := by
        rw [cert.exactPacketDecomposition a ha, cert.sum_source_eq_sum_packet a]
    _ ≤ ∑ p, |cert.packetValue a p| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p, cert.packetBudget a p :=
        Finset.sum_le_sum fun p _ => cert.errorBound a ha p
    _ ≤ X ^ (1 - delta) := cert.nuclearBudget a ha

/-! ## Part C — non-circularity guards -/

/-- **Guard (hostile test 6).**  The compiler concludes the *existing* project
predicate, unfolded here to its literal definition. -/
theorem compiler_uses_existing_fullTypeII (t X delta : ℝ) :
    FullTypeIIBound t X delta ↔ |t| ≤ X ^ (1 - delta) := Iff.rfl

/-- **Guard (hostile test 4).**  The conclusion is not vacuously true: there are
data for which `FullTypeIIBound` fails, so it cannot be derived without the
certificate. -/
theorem fullTypeII_not_automatic : ¬ FullTypeIIBound 2 1 0 := by
  unfold FullTypeIIBound
  norm_num

/-- **Guard (non-circularity / data-type nonemptiness).**  The certificate *type*
is inhabited in a finite toy example in which the Type-II problem plays no role
whatsoever — one source index, one packet, zero source values.  This shows the
structure is not definitionally the target proposition; it demonstrates nothing
whatever about the real analytic certificate. -/
theorem certificate_dataType_nonempty :
    Nonempty (FMReassemblyCertificate Unit (Fin 1) (Fin 1)
      (fun _ => True) (fun _ => (0 : ℝ)) 1 0) := by
  refine ⟨{
    sourceValue := fun _ _ => 0
    face := fun _ => Finset.univ
    packetValue := fun _ _ => 0
    packetBudget := fun _ _ => 0
    transform := id
    transformedCoefficientLegality := fun _ _ => trivial
    exactPacketDecomposition := by intro a _; simp
    packetSourceMatch := by intro a p; simp
    fullIntervalCoverage := fun x => ⟨0, Finset.mem_univ x⟩
    packetDisjointness := by
      intro p p' hne
      exact absurd (Subsingleton.elim p p') hne
    errorBound := by intro a _ p; simp
    nuclearBudget := by intro a _; simp }⟩

/-- **Guard.**  A `Gate1BClosed` conclusion does not by itself produce a Type-II
certificate: the two propositions are independent, as witnessed by data where the
first holds and the Type-II bound fails. -/
theorem gate1BClosed_does_not_give_fullTypeII :
    Gate1BClosed 0 1 0 ∧ ¬ FullTypeIIBound 2 1 0 := by
  refine ⟨⟨by norm_num, rfl⟩, ?_⟩
  unfold FullTypeIIBound
  norm_num

end Gate1BV10
end TwinPrimeProject
