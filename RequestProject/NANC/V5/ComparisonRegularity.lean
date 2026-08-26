/-
NANC V5 — COMPARISON REGULARITY CONDITIONS FOR THE TWIN CANDIDATE.

The Ford–Maynard comparison framework requires of the comparison sequence `b`
three conditions, here called (b.1), (b.2) and (w).  They are *analytic*
statements about the specific sequence and the parameters, and they are NOT
proved anywhere in this bank.

What is formalized is the exact dependency of each condition on its data:
sequence, scale, parameter `ε`, multiplier range, interval family, and the
admissible error.  A `TwinComparisonRegularityPackage` bundles proofs of the
three conditions; it has no default constructor and is never inhabited here.
-/
import Mathlib
import RequestProject.NANC.V5.ComparisonEuler

namespace NANC.V5

open scoped BigOperators
open NANC.V4

/-- The data on which the twin comparison-regularity conditions depend. -/
structure TwinComparisonData where
  /-- The comparison sequence `b`. -/
  b : ℕ → ℝ
  /-- The dyadic scale. -/
  X : ℕ
  /-- The shrinking parameter `ε`. -/
  eps : ℚ
  /-- The admissible multipliers. -/
  mRange : Finset ℕ
  /-- The admissible interval family. -/
  intervals : Finset (Finset ℕ)
  /-- The admissible error in the regularity estimates. -/
  err : ℝ
  /-- Condition (b.1) for this data — an external analytic statement. -/
  b1 : Prop
  /-- Condition (b.2) for this data — an external analytic statement. -/
  b2 : Prop
  /-- Condition (w) for this data — an external analytic statement. -/
  conditionW : Prop

/-- Ford–Maynard comparison condition (b.1) for the twin candidate.  UNINHABITED. -/
def FMComparisonB1Twin (D : TwinComparisonData) : Prop := D.b1

/-- Ford–Maynard comparison condition (b.2) for the twin candidate.  UNINHABITED. -/
def FMComparisonB2Twin (D : TwinComparisonData) : Prop := D.b2

/-- Ford–Maynard condition (w) for the twin candidate.  UNINHABITED. -/
def FMConditionWTwin (D : TwinComparisonData) : Prop := D.conditionW

/-- All three comparison-regularity conditions, bundled.  There is no default
constructor: every field must be supplied by an external analytic proof. -/
structure TwinComparisonRegularityPackage (D : TwinComparisonData) : Prop where
  /-- Condition (b.1). -/
  b1 : FMComparisonB1Twin D
  /-- Condition (b.2). -/
  b2 : FMComparisonB2Twin D
  /-- Condition (w). -/
  conditionW : FMConditionWTwin D

namespace TwinComparisonRegularityPackage

variable {D : TwinComparisonData}

theorem proj_b1 (P : TwinComparisonRegularityPackage D) : FMComparisonB1Twin D := P.b1
theorem proj_b2 (P : TwinComparisonRegularityPackage D) : FMComparisonB2Twin D := P.b2
theorem proj_w (P : TwinComparisonRegularityPackage D) : FMConditionWTwin D := P.conditionW

end TwinComparisonRegularityPackage

/-- A concrete instantiation of the data at the twin candidate: the comparison
sequence is `b = twinComparisonWeight C₂`.  Building this record asserts nothing:
the three condition fields are supplied as abstract Props. -/
noncomputable def twinCandidateComparisonData (C2 : ℝ) (X : ℕ) (eps : ℚ) (mRange : Finset ℕ)
    (intervals : Finset (Finset ℕ)) (err : ℝ) (b1 b2 conditionW : Prop) :
    TwinComparisonData where
  b := twinComparisonWeight C2
  X := X
  eps := eps
  mRange := mRange
  intervals := intervals
  err := err
  b1 := b1
  b2 := b2
  conditionW := conditionW

/-- **Firewall.**  The regularity package is genuinely contentful: for data whose
condition fields are `False` no package exists.  In particular a package can never
be produced by bookkeeping alone. -/
theorem no_regularity_package_from_nothing :
    ∀ D : TwinComparisonData, D.b1 = False → ¬ TwinComparisonRegularityPackage D := by
  intro D hD P
  have := P.b1
  rw [FMComparisonB1Twin, hD] at this
  exact this

/-- Provenance of the three conditions: external analytic input. -/
def comparisonRegularityProvenance : Provenance :=
  provenanceExternalTheorem "Ford–Maynard comparison conditions (b.1), (b.2), (w)"
    "arXiv:2407.14368" "conditions on the comparison sequence; not formalized"

theorem comparisonRegularityProvenance_not_leanEvidence :
    Provenance.IsLeanEvidence comparisonRegularityProvenance = false := rfl

end NANC.V5
