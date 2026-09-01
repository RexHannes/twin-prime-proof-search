import RequestProject.CurrentProgramme.StatusTypes
import RequestProject.CurrentProgramme.FordGeneratedCensus

/-!
# Twin-prime programme · current status ledger

This module is the current controlling status ledger for the **Twin Prime / fixed-shift
Ford–Maynard programme only**.  Historical cross-project rows remain available in Git
history, but are deliberately absent from this living ledger.

No row below claims `closed`; source and analytic interfaces remain explicit.
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace Ledger

open Status

/-! ## Gate 1B current status -/

def gate1B : List LedgerEntry :=
  [ ⟨"MOTOHASHI-ABC-EXACT-PIN45", Status.externallyAudited,
     "A/B/C interface stated; analytic input remains uninhabited."⟩,
    ⟨"MOTOHASHI-FAMILY-UNIFORMITY45", Status.externallyAudited,
     "Publication pin: uniform constant dependence in (Y, tau)."⟩,
    ⟨"TWISTED-DEFECT-ABC45", Status.externallyAudited, "Not formalised."⟩,
    ⟨"FIVEFOLD-MOTOHASHI-ITERATION45", Status.externallyAudited,
     "BV discrepancy; not formalised."⟩,
    ⟨"LOCALIZED-FIVEFOLD-MOTOHASHI45", Status.conditionalCompiler,
     "Lean-safe transfer exists; BV input remains open."⟩,
    ⟨"NORMALISATION-FIREWALL-DELTA-I", Status.leanProved,
     "Prime specialisation exact; pointwise logarithmic claim is not inferred."⟩,
    ⟨"RANKONE-LINE-SOURCE-ALGEBRA", Status.provedAlgebraic,
     "Kernel-checked line algebra."⟩,
    ⟨"RANKONE-POLYLOGK-INTERIOR45", Status.externallyAudited,
     "Analytically closed modulo comparison; not formalised."⟩,
    ⟨"RANKONE-ENDPOINT-U-DIAGONAL45", Status.capacityOnly,
     "Exponent margin banked; analytic variance input open."⟩,
    ⟨"RANKONE-ENDPOINT-U-OFFDIAG45", Status.analyticOpen,
     "Exact off-diagonal source identity proved; analytic estimate open."⟩,
    ⟨"RANKONE-HIGHK45", Status.analyticOpen,
     "Separate Parseval is not a closure mechanism."⟩,
    ⟨"PURE5-COMPARISON-MAINTERM-PIN", Status.sourceOpen,
     "Physical comparison source remains explicit."⟩,
    ⟨"ENDPOINT-OFFDIAG-STRATIFICATION-SHAPE", Status.provedAlgebraic,
     "Exact stratification only; source label map remains separate."⟩,
    ⟨"PURE5-DP-SIGNED45", Status.sourceOpen, "Source packet absent."⟩,
    ⟨"LOWER-DEFECT-ORDER-CENSUS", Status.provedAlgebraic,
     "Finite order census; no blanket monotonicity is inferred."⟩,
    ⟨"PROPER-DIVISOR-RECURSION-MEASURE", Status.provedAlgebraic,
     "Well-founded proper-divisor relation banked; no analytic closure stated."⟩,
    ⟨"NEARPRIM-DP-SIGNED45", Status.sourceOpen, "Source packet absent."⟩,
    ⟨"R>1-SQUARE-CHARACTER-FAMILY", Status.sourceOpen, "Source packet absent."⟩,
    ⟨"CSTAR-CNW-TRANSITION-STRIP", Status.sourceOpen, "Source packet absent."⟩,
    ⟨"QK56-FULL-PARENT", Status.conditionalCompiler,
     "Existing compilers reused conditionally; leaves not supplied."⟩,
    ⟨"QK56-EXHAUSTIVENESS", Status.sourceOpen,
     "No literal source enumeration in the repository."⟩,
    ⟨"SHIFTED-TTSTAR", Status.sourceOpen,
     "Literal source certificate remains uninhabited."⟩,
    ⟨"GATE1B-REASSEMBLY", Status.conditionalCompiler,
     "Endpoint compiler exists; Gate1BClosed is not proved."⟩,
    ⟨"SHIFT-SOURCE-LINKED-CHAR45", Status.supersededAsControllingFrontier,
     "Historical first-open; no longer controlling."⟩,
    ⟨"GATE1B", Status.open_, "OPEN."⟩ ]

/-! ## Gate 0 / Gate 1A / Gate 2 -/

def gates : List LedgerEntry :=
  [ ⟨"GATE0", Status.open_,
     "Finite banks reused; exhaustive source-partition identity not proved."⟩,
    ⟨"GATE1A", Status.open_,
     "Substantial safe bank preserved; current closure status remains explicit."⟩,
    ⟨"GATE1A_REQUIRED", Status.sourceOpen,
     "Derived predicate of the packet census; census remains a source obligation."⟩,
    ⟨"GATE2", Status.conditionalCompiler,
     "Downstream compiler only; requires the complete Type-I/Type-II input actually stated."⟩,
    ⟨"FULL_FM_TYPEII", Status.open_, "OPEN."⟩,
    ⟨"FULL_ROUTED_PIECE_POWER_SAVING_REFUTED_AS_STATED", Status.falseRoute,
     "High-conductor power saving is not whole-piece power saving."⟩,
    ⟨"TWO_OUTER_VARIABLE_F3_KERNEL", Status.notCurrentlyRequired,
     "Open research object; current census does not automatically demand it."⟩ ]

/-! ## Ford-generated source / packet census used by the twin-prime compiler -/

def ford : List LedgerEntry :=
  [ ⟨"FORD-GENERATED-PACKET-CENSUS", Status.sourceBlocked,
     "Published/source packet data must be supplied literally; not reconstructed from prose."⟩,
    ⟨"RealFordGrammarCertificate", Status.sourceBlocked,
     "Type exists but physical repository data remain uninhabited."⟩,
    ⟨"R9-LEAKAGE-MEMBERSHIP", Status.sourceOpen,
     "Leakage membership is a source classification, not an automatic disqualification."⟩,
    ⟨"R9-GDN-SPECIALIZATION", Status.sourceOpen,
     "Physical Ford coefficient source remains explicit."⟩,
    ⟨"R9-PEPSILON-FINITE-ARITHMETIC", Status.provedFinite,
     "Finite parameter separations proved."⟩ ]

/-! ## Twin-prime conclusion -/

def conclusion : List LedgerEntry :=
  [ ⟨"TWIN_PRIME_CONJECTURE", Status.open_, "OPEN."⟩ ]

/-- The full current Twin-Prime ledger. -/
def full : List LedgerEntry := gate1B ++ gates ++ ford ++ conclusion

/-- No row of the current ledger is `closed`. -/
theorem no_closed_rows : ∀ e ∈ full, e.status ≠ Status.closed := by
  decide

/-- Every current row satisfies the project honesty predicate. -/
theorem ledger_is_honest : ∀ e ∈ full, e.honest := fun e he =>
  LedgerEntry.honest_of_not_closed (no_closed_rows e he)

/-- The headline downstream nonclaims. -/
theorem end_of_run_nonclaims :
    (⟨"GATE1B", Status.open_, "OPEN."⟩ : LedgerEntry) ∈ full ∧
    (⟨"FULL_FM_TYPEII", Status.open_, "OPEN."⟩ : LedgerEntry) ∈ full ∧
    (⟨"TWIN_PRIME_CONJECTURE", Status.open_, "OPEN."⟩ : LedgerEntry) ∈ full := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

end Ledger
end CurrentProgramme
end TwinPrimeProject
