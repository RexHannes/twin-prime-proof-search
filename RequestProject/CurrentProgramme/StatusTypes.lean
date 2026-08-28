import Mathlib.Tactic

/-!
# Current programme · status taxonomy (append-only layer)

This module opens a **new, append-only status namespace** for the current
controlling frontier.  It does *not* rename, delete or weaken any historical
bank (V8.x / V9.x / V10 / V11 / Gate01 / Gate1A / Gate1B / Gate04Root).  Older
status blocks stay exactly as they are; where an old label was once accurate but
is no longer the controlling priority, the new layer records
`Status.supersededAsControllingFrontier` and *not* "false".

The repository did not previously contain a single project-wide status
datatype (each bank carried its own markdown / `#print axioms` ledger), so one
is introduced here and used uniformly by the `CurrentProgramme` modules.

## Firewall

`Status` is *metadata*.  A `Status` value is never evidence for a mathematical
proposition.  In particular:

* nothing in this file, or in any file that imports it, converts a `Status`
  into an inhabitant of an analytic interface;
* the statuses `externallyAudited`, `sourceOpen`, `sourceBlocked`,
  `analyticOpen` explicitly mean *not proved in Lean here*;
* `conditionalCompiler` means a deterministic implication was proved, and
  emphatically **not** that its antecedent holds.

`Status.closed` is deliberately *not* derivable from `conditionalCompiler`; see
`not_closed_of_conditionalCompiler`.
-/

namespace TwinPrimeProject
namespace CurrentProgramme

/-- Conservative status taxonomy for the current programme layer.

Only `leanProved`, `provedFinite` and `provedAlgebraic` assert that a kernel
proof exists in this repository. -/
inductive Status where
  /-- A full Lean theorem, kernel-checked here. -/
  | leanProved
  /-- A finite/decidable statement, kernel-checked here. -/
  | provedFinite
  /-- An exact algebraic identity, kernel-checked here. -/
  | provedAlgebraic
  /-- Only the exponent/parameter budget is banked; no analytic input proved. -/
  | capacityOnly
  /-- A deterministic implication is proved; its antecedents are NOT supplied. -/
  | conditionalCompiler
  /-- Audited outside Lean.  Metadata only. -/
  | externallyAudited
  /-- The literal source object is missing from the repository. -/
  | sourceOpen
  /-- The literal source object is missing and blocks a named promotion. -/
  | sourceBlocked
  /-- A genuine analytic theorem remains unproved. -/
  | analyticOpen
  /-- Once accurate, no longer the controlling frontier.  NOT "false". -/
  | supersededAsControllingFrontier
  /-- Refuted here by an explicit countermodel. -/
  | falseRoute
  /-- The literal packet census does not currently demand this provider. -/
  | notCurrentlyRequired
  /-- Open, uncategorised. -/
  | open_
  /-- Fully closed by a kernel proof with no open antecedent. -/
  | closed
  deriving DecidableEq, Repr, Inhabited

namespace Status

/-- The statuses that assert a kernel-checked proof *in this repository*. -/
def isKernelProved : Status → Bool
  | leanProved | provedFinite | provedAlgebraic | closed => true
  | _ => false

/-- The statuses that leave a mathematical obligation genuinely open. -/
def isOpenObligation : Status → Bool
  | capacityOnly | conditionalCompiler | externallyAudited | sourceOpen
  | sourceBlocked | analyticOpen | open_ => true
  | _ => false

end Status

/-- **Firewall theorem.**  `conditionalCompiler` is not `closed`.  This is the
Lean-level form of the instruction "never write CLOSED merely because a
conditional compiler exists". -/
theorem not_closed_of_conditionalCompiler :
    Status.conditionalCompiler ≠ Status.closed := by decide

/-- **Firewall theorem.**  `externallyAudited` is not a kernel proof. -/
theorem externallyAudited_not_kernelProved :
    Status.externallyAudited.isKernelProved = false := by decide

/-- **Firewall theorem.**  Every non-kernel-proved status in the taxonomy is
recorded as an open obligation or as an explicitly retired route. -/
theorem status_dichotomy (s : Status) :
    s.isKernelProved = true ∨ s.isOpenObligation = true ∨
      s = Status.supersededAsControllingFrontier ∨ s = Status.falseRoute ∨
      s = Status.notCurrentlyRequired := by
  cases s <;> simp [Status.isKernelProved, Status.isOpenObligation]

/-- A single row of the current programme ledger.  `label` is the literal
status label used in the human reports. -/
structure LedgerEntry where
  /-- Literal label as used in the markdown reports. -/
  label : String
  /-- The conservative status. -/
  status : Status
  /-- Free-text note: source pin, blocker, or provenance. -/
  note : String
  deriving DecidableEq, Repr, Inhabited

/-- A ledger row is *honest* when a `closed` claim is backed by a kernel
proof status. -/
def LedgerEntry.honest (e : LedgerEntry) : Prop :=
  e.status = Status.closed → e.status.isKernelProved = true

theorem LedgerEntry.honest_of_not_closed {e : LedgerEntry}
    (h : e.status ≠ Status.closed) : e.honest := fun hc => absurd hc h

theorem LedgerEntry.honest_closed {label note : String} :
    LedgerEntry.honest ⟨label, Status.closed, note⟩ := by
  intro _; rfl

end CurrentProgramme
end TwinPrimeProject
