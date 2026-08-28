/-
# Gate 1B v12 — prior-ledger compatibility record (DATA ONLY)

**Status: finite status record.  No proposition here encodes a research PASS.**

This module records, as *data*, what is currently known about the older named
claims

    JQ7-QCOMMONSEQ45
    JQ7-QCHAR7-ALLCONDUCTOR45
    QK5-XMOD-ALLQ-PROPER45
    SAMEQ

with respect to the four reconciliation questions:

* is there an exact theorem object in this repository?
* is the source dictionary the same?
* does it handle the *moving* multiplier?
* does it handle cross-character terms?

Every entry is `false`/`unknown` at v12: no reconciliation has been carried out
inside this bank.  The fields are booleans in a record, never propositions, so
nothing here can be mistaken for a proved analytic statement.  A later
reconciliation can be recorded by editing the record only.

Contents:

* `PriorClaim`, `PriorClaimStatus`, `priorStatus`;
* `no_prior_claim_handles_movingMultiplier` — the audit fact (by `decide`).
-/
import Mathlib

namespace Gate1B.SafeExtensions

/-- The older named claims that must eventually be reconciled. -/
inductive PriorClaim
  | jq7QCommonSeq45
  | jq7QChar7AllConductor45
  | qk5XModAllQProper45
  | sameQ
  deriving DecidableEq, Fintype, Repr

/-- The four reconciliation questions, as data. -/
structure PriorClaimStatus where
  /-- Is an exact theorem object present in this repository? -/
  exactTheoremObjectFound : Bool
  /-- Is the source dictionary literally the same? -/
  sameSourceDictionary : Bool
  /-- Does the claim handle the *moving* multiplier? -/
  handlesMovingMultiplier : Bool
  /-- Does the claim handle cross-character terms? -/
  handlesCrossCharacterTerms : Bool
  deriving DecidableEq, Repr

/-- The v12 record: nothing has been reconciled. -/
def priorStatus : PriorClaim → PriorClaimStatus
  | .jq7QCommonSeq45 => ⟨false, false, false, false⟩
  | .jq7QChar7AllConductor45 => ⟨false, false, false, false⟩
  | .qk5XModAllQProper45 => ⟨false, false, false, false⟩
  | .sameQ => ⟨false, false, false, false⟩

/-- **Audit fact.**  As recorded at v12, no prior claim is registered as handling
the moving multiplier.  This is a statement about the record, not about the
literature. -/
theorem no_prior_claim_handles_movingMultiplier :
    ∀ c : PriorClaim, (priorStatus c).handlesMovingMultiplier = false := by
  decide

/-- **Audit fact.**  Nor is any prior claim registered as handling
cross-character terms. -/
theorem no_prior_claim_handles_crossCharacter :
    ∀ c : PriorClaim, (priorStatus c).handlesCrossCharacterTerms = false := by
  decide

end Gate1B.SafeExtensions
