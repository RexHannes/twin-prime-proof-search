import RequestProject.CurrentProgramme.CurrentStatusHighKShift
import RequestProject.CurrentProgramme.EndpointCharacterPairing

/-!
# Status graph after the shifted-MAM operator bank (current layer)

**Append-only.**  Every earlier ledger is untouched:
`Ledger.gate1B`, `LedgerMixed.full`, `LedgerCharacterBundle.full`,
`LedgerHighKShift.full`.

Frontier state:

* `ENDPOINT-CHAR-TWISTED-FACTORMOD-SQUARE45` is now
  `supersededAsControllingFrontier` — a **stronger sufficient socket**, obtained
  from the source-minimal pairing by Cauchy–Schwarz
  (`CharPairing.characterSquare_is_Cauchy_strengthening`).  It is **not** false.
* The new first exact analytic residual is
  `SHIFTED-MAM-FIVEFOLD-OPERATOR45 : analyticOpen`.
* `MOTOHASHI-SHIFTED-MAM-DICTIONARY45` fails at the source-coupled operator slot
  (`MAMOperator.betaMultiplier_not_sourceDecoupled`); this is a *dictionary*
  failure, not a refutation of any Motohashi theorem.

```
GATE1B : OPEN.
```
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace LedgerMAMOperator

open Status

set_option maxRecDepth 40000

/-- The current status layer. -/
def full : List LedgerEntry :=
  [ ⟨"DETERMINANT-CHARACTER-TRANSFER45", Status.leanProved,
     "LEAN_PROVED. CharTransfer.shiftedDet_character_product, shiftedDet_character_transfer, determinantResidue_character_transfer; unit hypotheses explicit."⟩,
    ⟨"DETERMINANT-CHARACTER-TO-SHIFTED-MAM45", Status.provedFinite,
     "LEAN_PROVED_FINITE. CharTransfer.shiftedMAM_character_transfer_uniform: the transfer is uniform in the shift hSh."⟩,
    ⟨"SOURCE-MINIMAL-CHARACTER-PAIRING45", Status.provedFinite,
     "LEAN_PROVED / PROVED_FINITE. CharPairing.fullCharacterPairing and centeredPairing_eq_nonprincipalCharacterPairing on the unit sector with canonical zero mean."⟩,
    ⟨"ENDPOINT-CHAR-TWISTED-FACTORMOD-SQUARE45", Status.supersededAsControllingFrontier,
     "SUPERSEDED AS CONTROLLING FRONTIER / STRONGER SUFFICIENT SOCKET. CharPairing.characterSquare_is_Cauchy_strengthening. NOT false; the interface is kept and still uninhabited."⟩,
    ⟨"FIVE-DEFECT-RESIDUE-ADAPTER45", Status.sourceOpen,
     "SOURCE_OPEN / UNINHABITED. CharPairing.FiveDefectResidueSourceAdapter; the physical five-defect residue discrepancy is absent."⟩,
    ⟨"FINITE-SHIFT-STABILITY45", Status.provedAlgebraic,
     "PROVED_ALGEBRAIC / SOURCE METADATA. ShiftedMAM.finiteShift_sameArithmeticArchitecture for h = 0,+1,-1; values may still differ (finiteShift_values_may_differ)."⟩,
    ⟨"POLYLOG-SHIFT-STABILITY45", Status.analyticOpen,
     "SOURCE PASS / ANALYTIC OPEN. Only the abstract shift-budget metadata is banked (ShiftLedger.FrequencySplit); analytic uniformity is open."⟩,
    ⟨"SHIFTED-MAM-DIVISOR-SWITCH45", Status.provedAlgebraic,
     "LEAN_PROVED_ALGEBRAIC. ShiftedDet.shiftedMAM_divisorSwitch, shiftedMAM_prime_solve, shiftedMAM_solve_v, shiftedMAM_solve_p."⟩,
    ⟨"SHIFTED-MAM-FIVEFOLD-OPERATOR45", Status.analyticOpen,
     "OPEN_ANALYTIC / FIRST EXACT ANALYTIC RESIDUAL. MAMOperator.ShiftedMAMFivefoldOperatorInput; UNINHABITED; canonical local term M_h^can kept explicit."⟩,
    ⟨"PHYSICAL-SHIFT-KERNEL-CLASS45", Status.provedFinite,
     "PROVED_FINITE. MAMOperator.PhysicalShiftKernel with explicit L1 budget; ofWeights covers low-k inverse-DFT and dyadic band kernels."⟩,
    ⟨"MOTOHASHI-SHIFTED-MAM-DICTIONARY45", Status.falseRoute,
     "FAIL AT SOURCE-COUPLED OPERATOR SLOT. MAMOperator.betaMultiplier_not_sourceDecoupled. Dictionary failure only; no Motohashi theorem is claimed false."⟩,
    ⟨"NATIVE-PURE5-MAM-ADAPTER45", Status.sourceOpen,
     "SOURCE_OPEN / UNINHABITED. ShiftedMAM.NativePure5SourceAdapter."⟩,
    ⟨"RANKONE-ENDPOINT-ALLK45", Status.conditionalCompiler,
     "OPEN / CONDITIONAL COMPILER. AllKV2.allK_operator_compiler and allK_endpoint_of_three_sockets; no antecedent inhabited; comparison excluded."⟩,
    ⟨"PURE5-COMPARISON-MAINTERM-PIN", Status.sourceOpen,
     "SOURCE_OPEN. Independent of every endpoint bound (AllKV2.allKV2_comparison_not_included)."⟩,
    ⟨"PURE5-DP-SIGNED45", Status.open_, "OPEN."⟩,
    ⟨"LOWER-DEFECTS", Status.open_,
     "OPEN. No blanket monotonicity (Strata.no_blanket_monotonicity); one propagation input per defect order is required."⟩,
    ⟨"NEARPRIM", Status.open_, "OPEN."⟩,
    ⟨"R-GREATER-THAN-ONE", Status.open_, "OPEN."⟩,
    ⟨"QK56-FULL-PARENT", Status.open_, "OPEN."⟩,
    ⟨"QK56-EXHAUSTIVENESS", Status.open_, "OPEN."⟩,
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

/-- **The current first analytic open.** -/
theorem current_analytic_frontier :
    (⟨"SHIFTED-MAM-FIVEFOLD-OPERATOR45", Status.analyticOpen,
      "OPEN_ANALYTIC / FIRST EXACT ANALYTIC RESIDUAL. MAMOperator.ShiftedMAMFivefoldOperatorInput; UNINHABITED; canonical local term M_h^can kept explicit."⟩
        : LedgerEntry) ∈ full := by decide

/-- **The character square is superseded, not false.** -/
theorem charSquare_superseded_not_false :
    (⟨"ENDPOINT-CHAR-TWISTED-FACTORMOD-SQUARE45", Status.supersededAsControllingFrontier,
      "SUPERSEDED AS CONTROLLING FRONTIER / STRONGER SUFFICIENT SOCKET. CharPairing.characterSquare_is_Cauchy_strengthening. NOT false; the interface is kept and still uninhabited."⟩
        : LedgerEntry) ∈ full ∧
    Status.supersededAsControllingFrontier ≠ Status.falseRoute ∧
    Status.supersededAsControllingFrontier.isKernelProved = false := by
  refine ⟨by decide, by decide, by decide⟩

/-- **Preservation.**  The high-`k` layer's row for the character square is still
present, unchanged. -/
theorem historical_highk_row_preserved :
    (⟨"ENDPOINT-CHAR-TWISTED-FACTORMOD-SQUARE45", Status.analyticOpen,
      "OPEN_ANALYTIC / FIRST EXACT ANALYTIC RESIDUAL at this layer. CharSquareSocket interface; UNINHABITED."⟩
        : LedgerEntry) ∈ LedgerHighKShift.full := by decide

/-- **End-of-run non-claims.** -/
theorem end_of_run_nonclaims :
    (⟨"GATE1B", Status.open_, "OPEN."⟩ : LedgerEntry) ∈ full ∧
    (⟨"PURE5-DP-SIGNED45", Status.open_, "OPEN."⟩ : LedgerEntry) ∈ full ∧
    (⟨"QK56-FULL-PARENT", Status.open_, "OPEN."⟩ : LedgerEntry) ∈ full ∧
    (⟨"QK56-EXHAUSTIVENESS", Status.open_, "OPEN."⟩ : LedgerEntry) ∈ full := by
  refine ⟨by decide, by decide, by decide, by decide⟩

end LedgerMAMOperator
end CurrentProgramme
end TwinPrimeProject
