/-
# Universal / D0WP — the conditional RUN1B compiler

**Status of this module: CONDITIONAL_KERNEL.**

The compiler below is a genuine implication: *all six* inputs

1. `PhysicalQMuPrimeAnalyticInput` — the external analytic provider bound;
2. `HardP3PhysicalRange` (the hard-`P3` range pin);
3. `DwpSeparationPin`;
4. `P3CenteringPin`;
5. `PerronNuclearLedger`;
6. `FirstParentSourceCensusPin`;

are used in the proof.  Each of items 2–6 is a source pin with **no inhabitant**
in this repository, and item 1 is an external analytic statement that is **not**
proved here.  Consequently the RUN1B conclusion is available only conditionally.

Research metadata (not a Lean claim):

* analytic core: `PAPER_CLOSED_EXTERNAL`;
* source-exhaustive RUN1B: `PENDING HOSTILE AUDIT`.
-/
import Universal.D0WP.SourcePins
import Universal.D0WP.PerronLedger
import Universal.D0WP.FirstParentCensus
import Universal.D0WP.FinitePacketCompiler

namespace Universal.D0WP

open Finset

/-- The structural data of a RUN1B row family.  Nothing here is an estimate. -/
structure Run1BData (ι : Type*) where
  /-- The finite family of rows. -/
  rows : Finset ι
  /-- The raw physical packet. -/
  raw : ι → ℂ
  /-- The model packet. -/
  model : ι → ℂ
  /-- The inner `d0 · wp` source of each row. -/
  inner : ι → D0WPSource
  /-- The separation data of the family. -/
  sep : SeparationData ι
  /-- The kernel factor multiplying the coefficient in the model packet. -/
  kernelFactor : ι → ℂ
  /-- Structural identity: the model packet is coefficient × kernel factor. -/
  modelEq : ∀ i, model i = sep.coeff i * kernelFactor i
  /-- The Perron / nuclear source data. -/
  perron : PerronSourceData
  /-- The row count is one of the counted dyadic cells. -/
  rowsLeCells : (rows.card : ℝ) ≤ perron.cellCount
  /-- The Perron separators are all trivial for this family (the row count is
  the whole mass): a structural bookkeeping identity, not an estimate. -/
  massEq : perron.totalMass = perron.cellCount
  /-- The first-parent census predicate. -/
  ownerPred : FirstParentOwner → ι → Bool

/-- **External analytic input (`PAPER_CLOSED_EXTERNAL`).**

For every census-owned row whose inner source satisfies the hard-`P3` physical
range, the *separated* packet is bounded by `B`.  This is the physical
`Q`-`μ`-prime analytic statement; it is not proved in this repository. -/
structure PhysicalQMuPrimeAnalyticInput {ι : Type*} (data : Run1BData ι)
    (α β : ℕ → ℂ) (X eps B : ℝ) : Prop where
  /-- The external per-packet conclusion. -/
  perPacket : ∀ i ∈ data.rows,
    HardP3PhysicalRange X eps (data.inner i) →
    (∃ c, data.ownerPred c i = true) →
    ‖data.sep.outer i * (α (data.sep.d0 i) * β (data.sep.wp i) * data.kernelFactor i)‖ ≤ B

/-- **RUN1B CONDITIONAL COMPILER (kernel-proved implication).**

All six inputs are load-bearing: the range pin feeds the analytic input, the
separation pin rewrites the coefficient, the centering pin passes from the model
to the raw packet, the census pin supplies the owner witness, and the Perron
ledger converts the row count into a polylog factor. -/
theorem run1b_conditional {ι : Type*} (data : Run1BData ι) (α β : ℕ → ℂ)
    (X eps B : ℝ) (hB : 0 ≤ B)
    (analytic : PhysicalQMuPrimeAnalyticInput data α β X eps B)
    (rangePin : ∀ i ∈ data.rows, HardP3RangePin X eps (data.inner i))
    (sepPin : DwpSeparationPin data.sep α β)
    (centerPin : ∀ i ∈ data.rows, P3CenteringPin ⟨data.raw i, data.model i⟩)
    (ledger : PerronNuclearLedger data.perron)
    (censusPin : FirstParentSourceCensusPin data.rows data.ownerPred) :
    ∃ C : ℝ, ‖∑ i ∈ data.rows, data.raw i‖ ≤ data.perron.L ^ C * B := by
  obtain ⟨C, hC⟩ := perron_totalMass_le ledger
  refine ⟨C, ?_⟩
  have hpacket : ∀ i ∈ data.rows, ‖data.raw i‖ ≤ B := by
    intro i hi
    have hcentre : data.raw i = data.model i := centerPin i hi
    have hsep : data.sep.coeff i
        = data.sep.outer i * α (data.sep.d0 i) * β (data.sep.wp i) := sepPin.separated i
    have hrewrite : data.raw i
        = data.sep.outer i * (α (data.sep.d0 i) * β (data.sep.wp i) * data.kernelFactor i) := by
      rw [hcentre, data.modelEq i, hsep]
      ring
    rw [hrewrite]
    exact analytic.perPacket i hi (rangePin i hi) (censusPin i hi)
  have hsum : ‖∑ i ∈ data.rows, data.raw i‖ ≤ (data.rows.card : ℝ) * B :=
    finite_packet_bound data.rows data.raw B hpacket
  have hcard : (data.rows.card : ℝ) ≤ data.perron.L ^ C := by
    calc (data.rows.card : ℝ) ≤ data.perron.cellCount := data.rowsLeCells
      _ = data.perron.totalMass := data.massEq.symm
      _ ≤ data.perron.L ^ C := hC
  exact hsum.trans (mul_le_mul_of_nonneg_right hcard hB)

end Universal.D0WP
