import RequestProject.CurrentProgramme.CurrentStatus
import RequestProject.CurrentProgramme.EndpointMixedCompiler

/-!
# Phase I · current status graph after the mixed `2|2` / Lichtman-socket bank

**Append-only.**  The historical ledger `Ledger.full` is left byte-for-byte
unchanged; this module adds the *next* status layer and proves the two
consistency facts that matter:

* `historical_offdiag_row_preserved` — the historical
  `RANKONE-ENDPOINT-U-OFFDIAG45` row is still present in the old ledger, i.e.
  nothing was deleted;
* `offdiag_superseded_not_false` — in the new layer that endpoint object is
  recorded as `supersededAsControllingFrontier`, which by
  `StatusTypes.status_dichotomy` is *not* `falseRoute` and *not* a kernel
  proof.  **Reduced, not false.**

The controlling frontier is now

```
ENDPOINT-MIXED-2x2-LICHTMAN-T18-DICTIONARY45 : CURRENT FIRST ANALYTIC/SOURCE FRONTIER
```

and

```
GATE1B : OPEN.
```
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace LedgerMixed

open Status

/-! ## 1. The frontier reset -/

/-- Frontier-reset rows.  The historical endpoint objects are **kept**. -/
def frontierReset : List LedgerEntry :=
  [ ⟨"RANKONE-ENDPOINT-U-OFFDIAG45", Status.supersededAsControllingFrontier,
     "SUPERSEDED AS CONTROLLING FRONTIER / REDUCED, NOT FALSE. Historical row kept in Ledger.gate1B."⟩,
    ⟨"ENDPOINT-CENTERED-BETA-RANK2-TWOFREQ45", Status.open_,
     "REDUCED, NOT CLOSED."⟩,
    ⟨"ENDPOINT-MIXED-2x2-LICHTMAN-T18-DICTIONARY45", Status.sourceOpen,
     "CURRENT FIRST ANALYTIC/SOURCE FRONTIER. Schema LichtmanSocket.LichtmanT18Dictionary; UNINHABITED."⟩ ]

/-! ## 2. The Gate 1B controlling chain -/

/-- The controlling Gate-1B chain after this run. -/
def gate1BChain : List LedgerEntry :=
  [ ⟨"MOTOHASHI-ABC", Status.externallyAudited,
     "BANKED RESEARCH / SOURCE LEVEL. Interface only (Interfaces.MotohashiABCInput)."⟩,
    ⟨"POLYLOG-K-INTERIOR", Status.externallyAudited,
     "CLOSED MODULO COMPARISON. Not formalised here."⟩,
    ⟨"ENDPOINT-FINITE-POWER-ROUTERS", Status.capacityOnly,
     "BANKED / CAPACITY. Exponent arithmetic only (EndpointExponentBank)."⟩,
    ⟨"ENDPOINT-A-CENTERING45", Status.leanProved,
     "LEAN_PROVED_FINITE. Centering.centeredKernel_row_sum_units and sum_mul_conj_eq_sum_centered_mul_conj; physical adapter SOURCE_OPEN."⟩,
    ⟨"ENDPOINT-2x2-MODEL-SPLIT45", Status.provedFinite,
     "LEAN_PROVED_FINITE. TwoByTwo.conv4_eq_conv2_conv2, exact multiplicity, no injectivity."⟩,
    ⟨"ENDPOINT-2x2-CENTERED-REWRITING45", Status.provedFinite,
     "LEAN_PROVED_FINITE. CenteredRewriting.rCent_two_by_two, source-neutral."⟩,
    ⟨"ENDPOINT-MIXED-ADDMULT-SEQUENCE45", Status.provedFinite,
     "LEAN_PROVED_FINITE. MixedAddMult.nonzero_congruence_iff_unique_j and nonzeroCongruence_regroup."⟩,
    ⟨"ENDPOINT-MIXED-COLLISION-PARAM45", Status.provedAlgebraic,
     "PROVED. Collision.collision_param and collision_param_converse over the integers."⟩,
    ⟨"ENDPOINT-MIXED-COEFF-L2-45", Status.provedFinite,
     "PROVED_FINITE with the ACTUAL fibre multiplicity as an explicit hypothesis (Collision.sum_sq_bMix_le). No 1+rho, no X^{o(1)}."⟩,
    ⟨"ENDPOINT-MIXED-GCD-MOMENT45", Status.sourceOpen,
     "MixedGcdMomentInput exposed as an UNINHABITED arithmetic/source interface."⟩,
    ⟨"ENDPOINT-66107-RATIONAL-SIGNAL45", Status.capacityOnly,
     "PROVED_ALGEBRAIC / CAPACITY_ONLY: 66/107 - 8/13 = 2/1391 > 0. NOT an endpoint capacity PASS."⟩,
    ⟨"ENDPOINT-MIXED-2x2-LICHTMAN-T18-DICTIONARY45", Status.sourceOpen,
     "SOURCE_OPEN / UNINHABITED."⟩,
    ⟨"LICHTMAN-T18-COEFF-NORM-DICTIONARY45", Status.sourceOpen,
     "SOURCE_OPEN. b and tilde-b norm obligations recorded; tilde-b definition NOT guessed."⟩,
    ⟨"LICHTMAN-T18-HILBERT-LIFT45", Status.notCurrentlyRequired,
     "NOT CURRENTLY REQUIRED FOR SMALL-k: fixed polylog many k, scalar route costs #k (finite_k_sum_cost)."⟩,
    ⟨"ENDPOINT-LICHTMAN-T18-LITERAL-CAPACITY45", Status.conditionalCompiler,
     "CONDITIONAL / OPEN. endpointMixedLichtmanCapacity_of_inputs; no antecedent inhabited."⟩,
    ⟨"ENDPOINT-MIXED-CONDITIONAL-COMPILER45", Status.conditionalCompiler,
     "endpoint_bound_of_socket_input; dictionary, analytic input and capacity all open."⟩,
    ⟨"ENDPOINT-BETA-PHYSICAL-DICTIONARY45", Status.sourceBlocked,
     "SOURCE_BLOCKED / UNINHABITED. beta = mu_D * Lambda_P searched for again and still absent."⟩,
    ⟨"RANKONE-SMALLK-ENDPOINT45", Status.open_, "OPEN."⟩,
    ⟨"RANKONE-HIGHK45", Status.open_, "OPEN."⟩,
    ⟨"PURE5-COMPARISON-MAINTERM-PIN", Status.sourceOpen,
     "SOURCE_OPEN. Not connected by the new compiler (comparison_remains_independent)."⟩,
    ⟨"GATE1B", Status.open_, "OPEN."⟩ ]

/-- The full new-layer ledger. -/
def full : List LedgerEntry := frontierReset ++ gate1BChain

/-! ## 3. Honesty invariants -/

/-- **No row of the new layer is `closed`.** -/
theorem no_closed_rows : ∀ e ∈ full, e.status ≠ Status.closed := by decide

/-- **The new layer is honest.** -/
theorem ledger_is_honest : ∀ e ∈ full, e.honest := fun e he =>
  LedgerEntry.honest_of_not_closed (no_closed_rows e he)

/-- Gate 1B is recorded `open_`. -/
theorem gate1B_open : (⟨"GATE1B", Status.open_, "OPEN."⟩ : LedgerEntry) ∈ full := by
  decide

/-! ## 4. Frontier-reset consistency -/

/-- **Preservation.**  The historical off-diagonal row is still in the old
ledger: nothing was deleted. -/
theorem historical_offdiag_row_preserved :
    (⟨"RANKONE-ENDPOINT-U-OFFDIAG45", Status.analyticOpen,
      "FIRST EXACT ANALYTIC OPEN. Exact identity z2-z1 = u dt + j v_{t2} proved."⟩
        : LedgerEntry) ∈ Ledger.gate1B := by decide

/-- **Reduced, not false.**  In the new layer the same object is
`supersededAsControllingFrontier`, which is neither a refutation nor a kernel
proof. -/
theorem offdiag_superseded_not_false :
    (⟨"RANKONE-ENDPOINT-U-OFFDIAG45", Status.supersededAsControllingFrontier,
      "SUPERSEDED AS CONTROLLING FRONTIER / REDUCED, NOT FALSE. Historical row kept in Ledger.gate1B."⟩
        : LedgerEntry) ∈ full ∧
    Status.supersededAsControllingFrontier ≠ Status.falseRoute ∧
    Status.supersededAsControllingFrontier.isKernelProved = false := by
  refine ⟨by decide, by decide, by decide⟩

/-- **The current first frontier is the Lichtman dictionary socket.** -/
theorem current_frontier :
    (⟨"ENDPOINT-MIXED-2x2-LICHTMAN-T18-DICTIONARY45", Status.sourceOpen,
      "CURRENT FIRST ANALYTIC/SOURCE FRONTIER. Schema LichtmanSocket.LichtmanT18Dictionary; UNINHABITED."⟩
        : LedgerEntry) ∈ full := by decide

/-- **End-of-run non-claims.**  Gate 1B is open, the small-`k` endpoint is open,
the high-`k` endpoint is open, and the comparison pin is source-open. -/
theorem end_of_run_nonclaims :
    (⟨"GATE1B", Status.open_, "OPEN."⟩ : LedgerEntry) ∈ full ∧
    (⟨"RANKONE-SMALLK-ENDPOINT45", Status.open_, "OPEN."⟩ : LedgerEntry) ∈ full ∧
    (⟨"RANKONE-HIGHK45", Status.open_, "OPEN."⟩ : LedgerEntry) ∈ full := by
  refine ⟨by decide, by decide, by decide⟩

end LedgerMixed
end CurrentProgramme
end TwinPrimeProject
