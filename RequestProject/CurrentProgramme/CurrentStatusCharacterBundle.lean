import RequestProject.CurrentProgramme.CurrentStatusMixed
import RequestProject.CurrentProgramme.EndpointAllKCompiler
import RequestProject.CurrentProgramme.EndpointCharacterBundleNorm

/-!
# Phase K · status graph after the centered-character-bundle bank

**Append-only.**  The historical ledgers `Ledger.gate1B` and `LedgerMixed.full`
are left byte-for-byte unchanged; this module adds the next status layer.

Frontier reset recorded here:

* `ENDPOINT-MIXED-2x2-LICHTMAN-T18-DICTIONARY45` is
  `supersededAsControllingFrontier` — **reduced, not false**.  The Lichtman
  theorem itself is *not* marked false anywhere.
* the new controlling frontier is
  `ENDPOINT-CHAR-TWISTED-FACTORMOD-SQUARE45 : analyticOpen`.

```
GATE1B : OPEN.
```
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace LedgerCharacterBundle

open Status

set_option maxRecDepth 20000

/-! ## 1. Frontier reset -/

/-- The Lichtman lane is retired as the *current route*, not refuted. -/
def frontierReset : List LedgerEntry :=
  [ ⟨"ENDPOINT-MIXED-2x2-LICHTMAN-T18-DICTIONARY45", Status.supersededAsControllingFrontier,
     "SUPERSEDED AS CONTROLLING FRONTIER. Historical rows kept in LedgerMixed.full. The Lichtman theorem is NOT marked false."⟩,
    ⟨"LICHTMAN-T18-LANE", Status.supersededAsControllingFrontier,
     "SUPERSEDED / RETIRED AS CURRENT ROUTE. NONDEGENERATE-2x2-T18-DICTIONARY45 false for the current source; DEGENERATE-APFOURIER representation power-nonclosing."⟩,
    ⟨"ENDPOINT-LICHTMAN-T18-LITERAL-CAPACITY45", Status.capacityOnly,
     "POWER NONCLOSING BY X^(1/6-o(1)). Capacity metadata only."⟩,
    ⟨"ENDPOINT-ONECOMPLETION-T18-DICHOTOMY45", Status.externallyAudited,
     "PASS RESEARCH BANK. Not a Lean theorem."⟩,
    ⟨"ENDPOINT-SECOND-COMPLETION-KLOOSTERMAN45", Status.open_,
     "REPRESENTATION LOOP / NONCLOSING."⟩ ]

/-! ## 2. The new controlling chain -/

/-- The controlling Gate-1B chain after the character-bundle bank. -/
def controllingChain : List LedgerEntry :=
  [ ⟨"ENDPOINT-A-CENTERING45", Status.leanProved,
     "LEAN_PROVED / PROVED_FINITE. Centering.centeredKernel_row_sum_units (historical)."⟩,
    ⟨"ENDPOINT-2x2-MODEL-SPLIT45", Status.provedFinite,
     "LEAN_PROVED / PROVED_FINITE. TwoByTwo.conv4_eq_conv2_conv2 (historical)."⟩,
    ⟨"ENDPOINT-MIXED-ADDMULT-SEQUENCE45", Status.provedFinite,
     "LEAN_PROVED / PROVED_FINITE. MixedAddMult (historical)."⟩,
    ⟨"ENDPOINT-CENTERED-CHAR-SEPARATION45", Status.leanProved,
     "LEAN_PROVED. CharacterCentering.centeredKernel_eq_nonprincipalCharacterSum and centeredEnergy_eq_nonprincipalCharacterSquareBundle, on the unit sector, unit hypotheses explicit."⟩,
    ⟨"ENDPOINT-CHAR-2x2-TWIST45", Status.provedFinite,
     "PROVED_FINITE. TwoStageChar.twoByTwo_character_twist and twoByTwo_dirichlet_twist; no estimates, no smoothness."⟩,
    ⟨"ENDPOINT-BETA-PHYSICAL-DICTIONARY45", Status.sourceOpen,
     "SOURCE_OPEN / UNINHABITED. Repository searched again: literal beta_{D,P} = mu_D * Lambda_P line is absent. BetaDP.BetaDPPhysicalSourceAdapter exposed, never inhabited."⟩,
    ⟨"ENDPOINT-BETA-CONVOLUTION-ALGEBRA45", Status.provedFinite,
     "PROVED_FINITE. BetaDP.betaDP_open_line and factorModKernel_principal_centered; exact finite data, no asymptotics."⟩,
    ⟨"ENDPOINT-TWOSTAGE-NORMALFORM45", Status.conditionalCompiler,
     "PROVED_FINITE / CONDITIONAL_SOURCE_COMPILER. TwoStageChar.twoStage_normalForm_of_adapter; comparison remainder kept separate (comparisonRemainder_not_absorbed)."⟩,
    ⟨"ENDPOINT-TWOSTAGE-NORM45", Status.provedFinite,
     "NATURAL SCALE / PROVED_FINITE. BundleNorm.characterParseval_real and characterBundleEnergy_le_multiplicity with the exact finite fibre multiplicity."⟩,
    ⟨"ENDPOINT-TWOSTAGE-NATURAL-SCALE-LEDGER45", Status.provedAlgebraic,
     "PROVED_ALGEBRAIC / CAPACITY_ONLY. ScaleLedger.naturalScale_routes_agree: both routes have Y-exponent 13."⟩,
    ⟨"ENDPOINT-SCALARIZATION-ENERGY-TAX45", Status.capacityOnly,
     "PROVED_ALGEBRAIC / CAPACITY_ONLY. ScaleLedger.scalarizationEnergyTax = 5/18."⟩,
    ⟨"ENDPOINT-SCALARIZATION-AMPLITUDE-TAX45", Status.capacityOnly,
     "PROVED_ALGEBRAIC / CAPACITY_ONLY. ScaleLedger.scalarizationAmplitudeTax = 5/36."⟩,
    ⟨"ENDPOINT-HILBERT-FIREWALL45", Status.provedFinite,
     "PROVED_FINITE. HilbertFirewall.sharedCharacterProduct_not_singleLinearLift. Does NOT claim impossibility of every vector-valued theorem."⟩,
    ⟨"ENDPOINT-CHAR-TWISTED-FACTORMOD-SQUARE45", Status.analyticOpen,
     "OPEN_ANALYTIC. CharSquareSocket.EndpointCharTwistedFactorModSquareInput; UNINHABITED. CURRENT FIRST ANALYTIC OPEN."⟩,
    ⟨"RANKONE-SMALLK-ENDPOINT45", Status.open_,
     "OPEN. AllK.smallK_compiler pays exactly #SmallK(K0) as an explicit budget multiplier."⟩,
    ⟨"RANKONE-HIGHK45", Status.open_,
     "OPEN. AllK.HighKFrequencyGainInput exposed; no delta claimed, never inhabited."⟩,
    ⟨"RANKONE-ENDPOINT-ALLK45", Status.conditionalCompiler,
     "OPEN / CONDITIONAL_COMPILER ONLY. AllK.allK_endpoint_compiler; both analytic antecedents open."⟩,
    ⟨"PURE5-COMPARISON-MAINTERM-PIN", Status.sourceOpen,
     "SOURCE_OPEN. Kept independent: AllK.comparison_not_automatic."⟩,
    ⟨"PURE5-DP-SIGNED45", Status.open_, "OPEN."⟩,
    ⟨"QK56-FULL-PARENT", Status.open_, "OPEN."⟩,
    ⟨"QK56-EXHAUSTIVENESS", Status.open_, "OPEN."⟩,
    ⟨"GATE1B", Status.open_, "OPEN."⟩ ]

/-- The full new-layer ledger. -/
def full : List LedgerEntry := frontierReset ++ controllingChain

/-! ## 3. Honesty invariants -/

/-- **No row of the new layer is `closed`.** -/
theorem no_closed_rows : ∀ e ∈ full, e.status ≠ Status.closed := by decide

/-- **The new layer is honest.** -/
theorem ledger_is_honest : ∀ e ∈ full, e.honest := fun e he =>
  LedgerEntry.honest_of_not_closed (no_closed_rows e he)

/-- Gate 1B is recorded `open_`. -/
theorem gate1B_open : (⟨"GATE1B", Status.open_, "OPEN."⟩ : LedgerEntry) ∈ full := by
  decide

/-! ## 4. Preservation and frontier consistency -/

/-- **Preservation.**  The previous layer's frontier row is still present in
`LedgerMixed.full`: nothing was deleted or rewritten. -/
theorem historical_lichtman_row_preserved :
    (⟨"ENDPOINT-MIXED-2x2-LICHTMAN-T18-DICTIONARY45", Status.sourceOpen,
      "CURRENT FIRST ANALYTIC/SOURCE FRONTIER. Schema LichtmanSocket.LichtmanT18Dictionary; UNINHABITED."⟩
        : LedgerEntry) ∈ LedgerMixed.full := by decide

/-- **Reduced, not false.**  In the new layer the Lichtman lane is
`supersededAsControllingFrontier`, which is neither `falseRoute` nor a kernel
proof. -/
theorem lichtman_superseded_not_false :
    (⟨"LICHTMAN-T18-LANE", Status.supersededAsControllingFrontier,
      "SUPERSEDED / RETIRED AS CURRENT ROUTE. NONDEGENERATE-2x2-T18-DICTIONARY45 false for the current source; DEGENERATE-APFOURIER representation power-nonclosing."⟩
        : LedgerEntry) ∈ full ∧
    Status.supersededAsControllingFrontier ≠ Status.falseRoute ∧
    Status.supersededAsControllingFrontier.isKernelProved = false := by
  refine ⟨by decide, by decide, by decide⟩

/-- **The current first analytic open** is the character-twisted factor-mod
square. -/
theorem current_analytic_frontier :
    (⟨"ENDPOINT-CHAR-TWISTED-FACTORMOD-SQUARE45", Status.analyticOpen,
      "OPEN_ANALYTIC. CharSquareSocket.EndpointCharTwistedFactorModSquareInput; UNINHABITED. CURRENT FIRST ANALYTIC OPEN."⟩
        : LedgerEntry) ∈ full := by decide

/-- **The current first source open** is the physical `β_{D,P}` dictionary. -/
theorem current_source_frontier :
    (⟨"ENDPOINT-BETA-PHYSICAL-DICTIONARY45", Status.sourceOpen,
      "SOURCE_OPEN / UNINHABITED. Repository searched again: literal beta_{D,P} = mu_D * Lambda_P line is absent. BetaDP.BetaDPPhysicalSourceAdapter exposed, never inhabited."⟩
        : LedgerEntry) ∈ full := by decide

/-- **End-of-run non-claims.**  Gate 1B, small-`k`, high-`k`, all-`k`,
comparison and QK56 all remain open. -/
theorem end_of_run_nonclaims :
    (⟨"GATE1B", Status.open_, "OPEN."⟩ : LedgerEntry) ∈ full ∧
    (⟨"RANKONE-SMALLK-ENDPOINT45", Status.open_,
      "OPEN. AllK.smallK_compiler pays exactly #SmallK(K0) as an explicit budget multiplier."⟩
        : LedgerEntry) ∈ full ∧
    (⟨"RANKONE-HIGHK45", Status.open_,
      "OPEN. AllK.HighKFrequencyGainInput exposed; no delta claimed, never inhabited."⟩
        : LedgerEntry) ∈ full ∧
    (⟨"QK56-FULL-PARENT", Status.open_, "OPEN."⟩ : LedgerEntry) ∈ full ∧
    (⟨"QK56-EXHAUSTIVENESS", Status.open_, "OPEN."⟩ : LedgerEntry) ∈ full := by
  refine ⟨by decide, by decide, by decide, by decide, by decide⟩

end LedgerCharacterBundle
end CurrentProgramme
end TwinPrimeProject
