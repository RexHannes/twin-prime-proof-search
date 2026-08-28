import RequestProject.CurrentProgramme.CurrentStatusCharacterBundle
import RequestProject.CurrentProgramme.EndpointAllKCompilerV2

/-!
# Status graph after the high-`k` short-shift bank

**Append-only.**  All historical ledgers (`Ledger.gate1B`, `LedgerMixed.full`,
`LedgerCharacterBundle.full`) are untouched.

Frontier state recorded by this layer:

* `ENDPOINT-CHAR-TWISTED-FACTORMOD-SQUARE45` is still `analyticOpen` here (it is
  demoted to a *stronger sufficient socket* only in the next, operator, layer);
* the frequency-gain lane `RANKONE-HIGHK-FREQUENCY-GAIN45` is
  `supersededAsControllingFrontier` — the revised all-`k` compiler
  (`AllKV2.allK_v2_needs_no_frequency_gain`) uses no `K^{-δ}` hypothesis;
* `PHASE-VARIATION-IMPLIES-KDECAY45` is `falseRoute` **as a generic logical
  mechanism only** (`BandKernel.phaseVariation_alone_does_not_force_decay`); no
  claim is made that the actual source has no frequency decay.

```
GATE1B : OPEN.
```
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace LedgerHighKShift

open Status

set_option maxRecDepth 40000

/-- The high-`k` short-shift status layer. -/
def full : List LedgerEntry :=
  [ ⟨"ENDPOINT-CHAR-TWISTED-FACTORMOD-SQUARE45", Status.analyticOpen,
     "OPEN_ANALYTIC / FIRST EXACT ANALYTIC RESIDUAL at this layer. CharSquareSocket interface; UNINHABITED."⟩,
    ⟨"HIGHK-BETA-PHASE45", Status.externallyAudited,
     "RESEARCH BANK. Not formalised from a literal source: the physical beta_{D,P} line is still absent."⟩,
    ⟨"HIGHK-DETERMINANT-DEFECT-PHASE45", Status.provedAlgebraic,
     "LEAN_PROVED_ALGEBRAIC. ShiftedDet.determinantDefect_phase_identity and determinantDefect_eq_shift."⟩,
    ⟨"HIGHK-SHIFTED-DETERMINANT45", Status.provedAlgebraic,
     "LEAN_PROVED_ALGEBRAIC. ShiftedDet.shifted_lineDet2, shiftedDeterminant_betaForm, shiftedMAM_mod_u, shiftedMAM_mod_ell (both shift-independent)."⟩,
    ⟨"HIGHK-BAND-TO-SHORTSHIFT45", Status.provedFinite,
     "LEAN_PROVED_FINITE. BandKernel.bandPairing_eq_shiftKernelSum and bandPairing_eq_shiftSum: exact DFT identity, no decay used."⟩,
    ⟨"HIGHK-BAND-LOCALIZATION45", Status.analyticOpen,
     "EXTERNAL / OPEN. BandKernel.BandKernelLocalizationInput; UNINHABITED. L1 budget alone gives only the trivial bound (kernelL1_gives_only_trivial_bound)."⟩,
    ⟨"PHASE-VARIATION-IMPLIES-KDECAY45", Status.falseRoute,
     "FALSE AS A GENERIC LOGICAL MECHANISM. BandKernel.phaseVariation_alone_does_not_force_decay. NOT a claim that the actual source lacks frequency decay."⟩,
    ⟨"RANKONE-HIGHK-FREQUENCY-GAIN45", Status.supersededAsControllingFrontier,
     "SUPERSEDED AS FIRST HIGH-k TARGET. AllK.HighKFrequencyGainInput kept, not deleted; the revised compiler needs no K^{-delta}."⟩,
    ⟨"HIGHK-ONE-DIMENSIONAL-LANE45", Status.open_,
     "NONCLOSING ON THE ENTROPY GAP. Research metadata."⟩,
    ⟨"MQW-BP-HIGHK-LITERAL-DICTIONARY45", Status.sourceOpen,
     "SOURCE MISMATCH / NOT CURRENTLY APPLICABLE."⟩,
    ⟨"RANKONE-HIGHK-SHORTSHIFT-MAM45", Status.analyticOpen,
     "CURRENT HIGH-k DIAGNOSTIC FRONTIER / umbrella. Split into MIDK and TOPK below."⟩,
    ⟨"RANKONE-MIDK-SHIFTAVERAGED-MAM45", Status.analyticOpen,
     "OPEN_ANALYTIC. ShiftedMAM.MidKShiftAveragedMAMInput; UNINHABITED."⟩,
    ⟨"RANKONE-TOPK-FINITESHIFT-MAM45", Status.analyticOpen,
     "OPEN_ANALYTIC. ShiftedMAM.TopKFiniteShiftMAMInput; UNINHABITED; contains the r=0 child explicitly."⟩,
    ⟨"SHIFTED-MAM-FAMILY45", Status.analyticOpen,
     "OPEN_ANALYTIC / UNINHABITED. ShiftedMAM.ShiftedMAMFamilyInput, with logical specialisations to native, top-k and mid-k."⟩,
    ⟨"NATIVE-PURE5-MAM-ADAPTER45", Status.sourceOpen,
     "SOURCE_OPEN / UNINHABITED. ShiftedMAM.NativePure5SourceAdapter: the literal native Pure5/MAM object is absent."⟩,
    ⟨"ZERO-SHIFT-SURVIVES45", Status.provedFinite,
     "LEAN_PROVED_FINITE. BandKernel.zeroShift_survives and zeroShift_isolated."⟩,
    ⟨"RANKONE-SMALLK-ENDPOINT45", Status.open_, "OPEN."⟩,
    ⟨"RANKONE-ENDPOINT-ALLK45", Status.conditionalCompiler,
     "OPEN / CONDITIONAL COMPILER ONLY. AllKV2.allK_endpoint_of_three_sockets; all three antecedents open."⟩,
    ⟨"PURE5-COMPARISON-MAINTERM-PIN", Status.sourceOpen,
     "SOURCE_OPEN. Kept independent: AllKV2.allKV2_comparison_not_included."⟩,
    ⟨"GATE1B", Status.open_, "OPEN."⟩ ]

/-! ## Honesty invariants -/

/-- **No row is `closed`.** -/
theorem no_closed_rows : ∀ e ∈ full, e.status ≠ Status.closed := by decide

/-- **The layer is honest.** -/
theorem ledger_is_honest : ∀ e ∈ full, e.honest := fun e he =>
  LedgerEntry.honest_of_not_closed (no_closed_rows e he)

/-- Gate 1B remains open. -/
theorem gate1B_open : (⟨"GATE1B", Status.open_, "OPEN."⟩ : LedgerEntry) ∈ full := by
  decide

/-- **Preservation.**  The previous layer's controlling analytic row is still
present in `LedgerCharacterBundle.full`. -/
theorem historical_charSquare_row_preserved :
    (⟨"ENDPOINT-CHAR-TWISTED-FACTORMOD-SQUARE45", Status.analyticOpen,
      "OPEN_ANALYTIC. CharSquareSocket.EndpointCharTwistedFactorModSquareInput; UNINHABITED. CURRENT FIRST ANALYTIC OPEN."⟩
        : LedgerEntry) ∈ LedgerCharacterBundle.full := by decide

/-- **Reduced, not false.**  The frequency-gain lane is superseded, which is
neither a refutation nor a kernel proof. -/
theorem frequencyGain_superseded_not_false :
    (⟨"RANKONE-HIGHK-FREQUENCY-GAIN45", Status.supersededAsControllingFrontier,
      "SUPERSEDED AS FIRST HIGH-k TARGET. AllK.HighKFrequencyGainInput kept, not deleted; the revised compiler needs no K^{-delta}."⟩
        : LedgerEntry) ∈ full ∧
    Status.supersededAsControllingFrontier ≠ Status.falseRoute := by
  refine ⟨by decide, by decide⟩

end LedgerHighKShift
end CurrentProgramme
end TwinPrimeProject
