/-
NANC V5 CONTROLLING LAYER — GATE-2 STATUS AND THE POST-RUN PATCH HOOK.

Recorded status:

    GATE2:        OPEN
    FIRST OPEN:   FM-N2-CELLSUM-UPPER45
    RESEARCH:     Gate2ReducedToOneSourceSpecificAggregateUpperSieveLemma

Deliberately NOT recorded: `Gate2Closed`, `Gate2ConditionalClosed`.  Both labels
exist in the datatype below only so that the current status can be proved
*different* from them.

The patch hook `N2ProVerdict` records the verdict of a later analytic run.  Even
the verdict `pass` is mapped to `opusAuditedAnalyticPass`, never to `leanProved`:
promotion to a Lean proof requires an actual Lean proof.
-/
import Mathlib
import RequestProject.NANC.V5.Controlling.N2CellSumInterface

namespace NANC.V5.Controlling

/-- Possible Gate-2 status labels. -/
inductive Gate2Status where
  /-- Gate 2 is open. -/
  | openGate
  /-- Gate 2 has been reduced to one source-specific aggregate upper-sieve lemma. -/
  | reducedToOneSourceSpecificAggregateUpperSieveLemma
  /-- Gate 2 is closed conditionally on stated interfaces. -/
  | conditionalClosed
  /-- Gate 2 is closed. -/
  | closed
  deriving DecidableEq, Repr

/-- The **current** Gate-2 status: open, reduced to one source-specific aggregate
upper-sieve lemma. -/
def gate2Status : Gate2Status :=
  Gate2Status.reducedToOneSourceSpecificAggregateUpperSieveLemma

/-- The first open item of Gate 2. -/
def gate2FirstOpen : String := "FM-N2-CELLSUM-UPPER45"

/-- Gate 2 is **not** recorded as closed. -/
theorem gate2_not_closed : gate2Status ≠ Gate2Status.closed := by decide

/-- Gate 2 is **not** recorded as conditionally closed either. -/
theorem gate2_not_conditionalClosed : gate2Status ≠ Gate2Status.conditionalClosed := by decide

/-- The reduction status is a research statement, not a Lean proof. -/
def gate2ControlStatus : ControlStatus := ControlStatus.openStatus

theorem gate2ControlStatus_ne_leanProved :
    gate2ControlStatus ≠ ControlStatus.leanProved := by decide

/-- Status entry for Gate 2. -/
def gate2Entry : ControlEntry where
  name := "GATE2"
  status := gate2ControlStatus
  notes :=
    "OPEN.  First open item: FM-N2-CELLSUM-UPPER45.  Research status: reduced to one " ++
    "source-specific aggregate upper-sieve lemma.  Neither Gate2Closed nor " ++
    "Gate2ConditionalClosed is recorded."

theorem gate2Entry_not_leanEvidence : ControlEntry.IsLeanEvidence gate2Entry = false := rfl

/-! ### Post-run patch hook -/

/-- The verdict of a later analytic run on `FM-N2-CELLSUM-UPPER45`. -/
inductive N2ProVerdict where
  /-- No verdict yet. -/
  | pending
  /-- The analytic run reports a pass. -/
  | pass
  /-- The run reduces the target to an explicit sieve remainder. -/
  | reducedToExplicitSieveRemainder
  /-- The run fails at the short-interval step. -/
  | shortIntervalFail
  /-- The run fails at the ε-uniformity step. -/
  | epsilonUniformityFail
  /-- The run fails at the endgame step. -/
  | endgameFail
  deriving DecidableEq, Repr

/-- The current verdict. -/
def n2ProVerdict : N2ProVerdict := N2ProVerdict.pending

theorem n2ProVerdict_is_pending : n2ProVerdict = N2ProVerdict.pending := rfl

/-- How a verdict is allowed to affect the bank status.  A reported `pass` becomes
an *audited analytic pass*, never a Lean proof; failures become `failedRoute`; the
pending and partial verdicts leave the item open. -/
def N2ProVerdict.toControlStatus : N2ProVerdict → ControlStatus
  | pending => ControlStatus.openStatus
  | pass => ControlStatus.opusAuditedAnalyticPass
  | reducedToExplicitSieveRemainder => ControlStatus.openStatus
  | shortIntervalFail => ControlStatus.failedRoute
  | epsilonUniformityFail => ControlStatus.failedRoute
  | endgameFail => ControlStatus.failedRoute

/-- **Permanent patch-hook firewall.**  No verdict — including `pass` — promotes
the item to `leanProved`. -/
theorem verdict_never_leanProved (v : N2ProVerdict) :
    v.toControlStatus ≠ ControlStatus.leanProved := by
  cases v <;> decide

/-- In particular a reported `FM_N2_CELLSUM_UPPER45_PASS` yields only the audited
analytic-pass status. -/
theorem pass_gives_only_audited :
    N2ProVerdict.pass.toControlStatus = ControlStatus.opusAuditedAnalyticPass := rfl

/-- Status entry for the patch hook. -/
def n2ProVerdictEntry : ControlEntry where
  name := "N2 PRO VERDICT"
  status := n2ProVerdict.toControlStatus
  notes := "PENDING.  A later `pass` may only be recorded as an audited analytic pass."

theorem n2ProVerdictEntry_not_leanEvidence :
    ControlEntry.IsLeanEvidence n2ProVerdictEntry = false := rfl

end NANC.V5.Controlling
