import RequestProject.CurrentProgramme.StatusTypes
import RequestProject.CurrentProgramme.FordGeneratedCensus

/-!
# Current programme · master status ledger (append-only)

This module records the *current controlling* status of every named item.  It
refers to old theorem names and source objects; it does not duplicate their
mathematics, and it does not modify any historical bank.

## Frontier reset

The old v13 human ledger entry

  `FIRST GATE1B ANALYTIC OPEN : SHIFT-SOURCE-LINKED-CHAR45`

is recorded here as `supersededAsControllingFrontier` — **not** as false.  The
current first analytic open is

  `RANKONE-ENDPOINT-U-OFFDIAG45`.

## Honesty invariant

`ledger_is_honest` proves that no row of the ledger claims `closed` without a
kernel-proof status, and `no_closed_rows` proves that in fact **no** row is
`closed` at all.
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace Ledger

open Status

/-! ## Gate 1B current status -/

/-- Gate-1B rows. -/
def gate1B : List LedgerEntry :=
  [ ⟨"MOTOHASHI-ABC-EXACT-PIN45", Status.externallyAudited,
     "A/B/C interface stated (Interfaces.MotohashiABCInput); uninhabited."⟩,
    ⟨"MOTOHASHI-FAMILY-UNIFORMITY45", Status.externallyAudited,
     "Publication pin: uniform constant dependence in (Y, tau). Interface only."⟩,
    ⟨"TWISTED-DEFECT-ABC45", Status.externallyAudited, "Not formalised."⟩,
    ⟨"FIVEFOLD-MOTOHASHI-ITERATION45", Status.externallyAudited,
     "BV discrepancy; not formalised."⟩,
    ⟨"LOCALIZED-FIVEFOLD-MOTOHASHI45", Status.conditionalCompiler,
     "Lean-safe transfer proved (SmoothLocalisation.wDiscrepancy_le); BV input open."⟩,
    ⟨"NORMALISATION-FIREWALL-DELTA-I", Status.leanProved,
     "Prime specialisation exact; pointwise (log X)^{-1} claim refuted."⟩,
    ⟨"RANKONE-LINE-SOURCE-ALGEBRA", Status.provedAlgebraic,
     "u v_t + 2 = l z_t; kernel-checked over the integers."⟩,
    ⟨"RANKONE-POLYLOGK-INTERIOR45", Status.externallyAudited,
     "Analytically closed modulo comparison; not formalised."⟩,
    ⟨"RANKONE-ENDPOINT-U-DIAGONAL45", Status.capacityOnly,
     "Exponent margin X^(-1/12) banked exactly; analytic variance input open."⟩,
    ⟨"RANKONE-ENDPOINT-U-OFFDIAG45", Status.analyticOpen,
     "FIRST EXACT ANALYTIC OPEN. Exact identity z2-z1 = u dt + j v_{t2} proved."⟩,
    ⟨"RANKONE-HIGHK45", Status.analyticOpen,
     "Separate Parseval is not a closure mechanism (finite countermodel banked)."⟩,
    ⟨"PURE5-COMPARISON-MAINTERM-PIN", Status.sourceOpen,
     "Physical comparison source absent; no fake equality created."⟩,
    ⟨"ENDPOINT-OFFDIAG-STRATIFICATION-SHAPE", Status.provedAlgebraic,
     "Exhaustive disjoint stratification of offdiagEnergy, and the p1=p2 / p1!=p2 split for an arbitrary prime label. Identity only; awaits the beta label map."⟩,
    ⟨"PURE5-DP-SIGNED45", Status.sourceOpen, "Source packet absent."⟩,
    ⟨"LOWER-DEFECT-ORDER-CENSUS", Status.provedAlgebraic,
     "Five-row |J|=5..1 census; no_blanket_monotonicity proves |J|=5 does not entail the lower orders."⟩,
    ⟨"PROPER-DIVISOR-RECURSION-MEASURE", Status.provedAlgebraic,
     "Well-founded proper-divisor relation banked. No recursive closure is stated."⟩,
    ⟨"NEARPRIM-DP-SIGNED45", Status.sourceOpen, "Source packet absent."⟩,
    ⟨"R>1-SQUARE-CHARACTER-FAMILY", Status.sourceOpen, "Source packet absent."⟩,
    ⟨"CSTAR-CNW-TRANSITION-STRIP", Status.sourceOpen, "Source packet absent."⟩,
    ⟨"QK56-FULL-PARENT", Status.conditionalCompiler,
     "v11/v10 compilers reused; leaves not supplied."⟩,
    ⟨"QK56-EXHAUSTIVENESS", Status.sourceOpen,
     "No literal source enumeration in the repository."⟩,
    ⟨"SHIFTED-TTSTAR", Status.sourceOpen,
     "ShiftTTStar literal source certificate remains uninhabited."⟩,
    ⟨"GATE1B-REASSEMBLY", Status.conditionalCompiler,
     "Endpoint compiler proved; Gate1BClosed not proved."⟩,
    ⟨"SHIFT-SOURCE-LINKED-CHAR45", Status.supersededAsControllingFrontier,
     "Historical v13 first-open; no longer the controlling analytic frontier."⟩,
    ⟨"GATE1B", Status.open_, "OPEN."⟩ ]

/-! ## Gate 0 / Gate 1A / Gate 2 -/

/-- Gate-0/1A/2 rows. -/
def gates : List LedgerEntry :=
  [ ⟨"GATE0", Status.open_,
     "Finite banks reused; exhaustive source-partition identity not proved."⟩,
    ⟨"GATE1A", Status.open_,
     "Substantial safe bank preserved; not closed. Requirement is census-derived."⟩,
    ⟨"GATE1A_REQUIRED", Status.sourceOpen,
     "Derived predicate of the packet census; census unpopulated."⟩,
    ⟨"GATE2", Status.conditionalCompiler,
     "Uses the strongest existing project target only; no invented FullFMTypeII_OneSixth."⟩,
    ⟨"FULL_FM_TYPEII", Status.open_, "OPEN."⟩,
    ⟨"FULL_ROUTED_PIECE_POWER_SAVING_REFUTED_AS_STATED", Status.falseRoute,
     "Preserved: high-conductor power saving is not whole-piece power saving."⟩,
    ⟨"TWO_OUTER_VARIABLE_F3_KERNEL", Status.notCurrentlyRequired,
     "Genuine open research object; census does not currently demand it."⟩ ]

/-! ## Ford-generated / R9 / FCL -/

/-- Ford-generated rows. -/
def ford : List LedgerEntry :=
  [ ⟨"FORD-GENERATED-PACKET-CENSUS", Status.sourceBlocked,
     "Prop 7.22 / eq (7.23) / C(R) / R(P) / G(d;n) absent; not reconstructed."⟩,
    ⟨"RealFordGrammarCertificate", Status.sourceBlocked,
     "Present as a v11 type but repo data absent; kept uninhabited."⟩,
    ⟨"R9-LEAKAGE-MEMBERSHIP", Status.sourceOpen,
     "Direction CORRECTED: outside C(R(P)) is leakage, not disqualification."⟩,
    ⟨"R9-GDN-SPECIALIZATION", Status.sourceOpen,
     "G(d;n) absent; 70 is not identified with a physical Ford coefficient."⟩,
    ⟨"R9-PEPSILON-FINITE-ARITHMETIC", Status.provedFinite,
     "nu=1/6, eps<=1/600, eta<1/90 separations and the 4/5 cutoffs proved."⟩,
    ⟨"FCL", Status.sourceOpen,
     "Fixed-certificate leakage target needs the actual source; provider assignment is proof-specific."⟩ ]

/-! ## Erdős #287 -/

/-- Erdős-#287 rows. -/
def erdos287 : List LedgerEntry :=
  [ ⟨"OMEGA7-FACTORIAL-EULER-POLARIZATION45", Status.provedAlgebraic,
     "7^7 [z1..z7] (a_z^7/7!) = prod omega_i, including repeated primes."⟩,
    ⟨"OMEGA7-LOCAL-EULER-VONMANGOLDT-PATTERN", Status.provedAlgebraic,
     "Lambda_F(p)=a log p, Lambda_F(p^e)=0 for e>=2, pinned by the log-derivative recursion plus uniqueness. Class-C nomenclature stays a DEFINITION PIN."⟩,
    ⟨"POLARIZED-EXPECTED-TERM-LINEARITY45", Status.provedAlgebraic,
     "Coefficient extraction commutes with linear maps; M_fac = M_phys NOT concluded."⟩,
    ⟨"PASCADI-PROOF-PARAMETER-NOGO", Status.provedFinite,
     "Audit of supplied parameters only; not a claim that the theorem is impossible."⟩,
    ⟨"AFFINE287-FACTORIAL-OMEGA7-SIGNED-ENDPOINT45", Status.analyticOpen,
     "Uninhabited interface."⟩,
    ⟨"AFFINE287-MULOG-COMPARISON-LOWCOND-MATCH45", Status.sourceOpen,
     "Uninhabited interface."⟩,
    ⟨"AFFINE287-BALANCED7-MODULUS-AVERAGE45", Status.conditionalCompiler,
     "Compiler proved from the two inputs plus an exposed source split."⟩,
    ⟨"K0-SMOOTH-PARITY", Status.sourceOpen,
     "Fixed-certificate finite algebra preserved; structural fragmentation is not parity cancellation."⟩,
    ⟨"POSITIVE-AFFINE-MASS", Status.open_,
     "No positivity from isolated packet estimates."⟩,
    ⟨"WINDOWPAIRSUPPLY", Status.sourceBlocked,
     "No WindowPairSupply object exists in this repository; the #287 finite compiler is absent."⟩,
    ⟨"ERDOS287", Status.open_, "OPEN."⟩,
    ⟨"TWIN_PRIME_CONJECTURE", Status.open_,
     "OPEN. No implication either way with ERDOS287."⟩ ]

/-- The full current ledger. -/
def full : List LedgerEntry := gate1B ++ gates ++ ford ++ erdos287

/-! ## Honesty invariants -/

/-- **No row of the current ledger is `closed`.** -/
theorem no_closed_rows : ∀ e ∈ full, e.status ≠ Status.closed := by
  decide

/-- **The ledger is honest**: every row satisfies `LedgerEntry.honest`. -/
theorem ledger_is_honest : ∀ e ∈ full, e.honest := fun e he =>
  LedgerEntry.honest_of_not_closed (no_closed_rows e he)

/-- The four end-of-run non-claims, as ledger facts. -/
theorem end_of_run_nonclaims :
    (⟨"GATE1B", Status.open_, "OPEN."⟩ : LedgerEntry) ∈ full ∧
    (⟨"FULL_FM_TYPEII", Status.open_, "OPEN."⟩ : LedgerEntry) ∈ full ∧
    (⟨"ERDOS287", Status.open_, "OPEN."⟩ : LedgerEntry) ∈ full ∧
    (⟨"TWIN_PRIME_CONJECTURE", Status.open_,
      "OPEN. No implication either way with ERDOS287."⟩ : LedgerEntry) ∈ full := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

end Ledger
end CurrentProgramme
end TwinPrimeProject
