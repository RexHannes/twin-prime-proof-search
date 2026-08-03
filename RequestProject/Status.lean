/-!
# Status taxonomy (banking update)

This module fixes, as a Lean datatype, the exact status classes used throughout
the primitive-Form-C / balanced-two-outer banking update.  It is the single
source of truth referenced by `FrontierStatus.lean` and `LEDGER.md`.

No mathematical claim is attached to a `BankStatus` value; it is bookkeeping.
-/

namespace Banking

/-- The status classes used in the ledger.  See `LEDGER.md` for prose. -/
inductive BankStatus
  /-- Complete stated assertion machine-checked in Lean (no `sorry`/`axiom`/…). -/
  | leanProved
  /-- Algebraic / modular / arithmetic core machine-checked; analytic estimate
      is an explicit theorem parameter (hypothesis). -/
  | leanProvedCore
  /-- Survived an external hostile audit; full analytic proof not formalized. -/
  | externallyAudited
  /-- Statement/framework confirmed from a primary published/arXiv source. -/
  | literatureVerified
  /-- A precisely stated implication from an explicit new analytic input. -/
  | conditionalInterface
  /-- Coherent, useful reduction by a model, not yet fully hostile-audited. -/
  | provisionalReduction
  /-- Numerical threshold reported but not located in an exact source. -/
  | numericalSourcePending
  /-- An exact theorem still required. -/
  | openInput
  /-- A false assertion or failed route. -/
  | refuted
  /-- An earlier status replaced by a later audit. -/
  | superseded
  /-- Literature context, not an integer-theorem interface. -/
  | literatureVerifiedContext
  /-- Coherent model-level reduction, not yet hostile-audited (audited-update
      spelling of `provisionalReduction`). -/
  | provisional
  /-- A claimed source could not be located. -/
  | sourceNotFound
  /-- A route (not the underlying conjecture) shown to fail. -/
  | refutedRoute
  /-- A route superseded by a later, stronger route. -/
  | supersededRoute
  /-- Formal consequence of an explicitly supplied exact source theorem. -/
  | provedModuloExactSource
  /-- Claimed externally but not independently audited. -/
  | openUnaudited
  /-- Useful proof architecture, not a theorem. -/
  | proofSketchTemplate
  /-- A named source theorem does not presently match the application. -/
  | hypothesisMismatch
  /-- A route failed for a precise audited mathematical reason. -/
  | auditedFailedRoute
  /-- False or materially overstated declaration, retired from use. -/
  | falseRetired
  /-- Final target explicitly not established. -/
  | notProved
  deriving DecidableEq, Repr

end Banking
