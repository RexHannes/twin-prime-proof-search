import Gate1B.FullNineCanonicalOwner
import Gate1B.CanonicalSwitchedAggregate
import Gate1B.R9GlobalComparisonAdapter

/-!
# Gate 1B · canonical `h = 0` HIGH-HIGH conditional compiler (append-only)

The research bank records

```
CANONICAL-HZERO-HIGHHIGH45 : ANALYTICALLY CLOSED
```

for the fresh balanced-R9 packet.  **That is research metadata, not a Lean
theorem.**  What is formalised here is the *logical* compiler: an explicit,
deterministic implication from a complete list of named premises to the
canonical `h = 0` target inequality.  Every analytic and source premise is an
explicit field of `CanonicalHZeroInputs`; none of them is supplied here, and
none of them disappears.

The owner list is exhaustive by construction (`coverage`), so no contribution
is silently dropped and none is counted twice.
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace CanonicalHZero

open Finset

/-- The complete list of owners of the canonical `h = 0` HIGH-HIGH packet. -/
inductive HZeroOwner
  /-- The full-nine first-remainder telescope owner. -/
  | fullNineFirstRemainder
  /-- The nonzero determinant analytic owner. -/
  | nonzeroDeterminant
  /-- The product-Fourier owner. -/
  | productFourier
  /-- The top-E-strip owner. -/
  | topEStrip
  /-- The conditional-minor owner. -/
  | conditionalMinor
  /-- The Leaf-5 nonzero determinant owner. -/
  | leaf5NonzeroDeterminant
  /-- The canonical switched residual owner (`R_can = 0`). -/
  | canonicalResidual
  /-- The projector-robustness owner. -/
  | projectorRobustness
  /-- The `q = 2` local owner. -/
  | qTwoOwner
  /-- The nonunit owner. -/
  | nonunitOwner
  /-- The exceptional owner. -/
  | exceptionalOwner
  /-- The prime-power correction owner. -/
  | primePowerCorrection
  deriving DecidableEq, Fintype, Repr

/-- All premises of the canonical `h = 0` HIGH-HIGH compiler, made explicit.

`parts` is the owner decomposition of the packet, `partBounds` collects the
analytic/source inputs (one per owner) and `budgetFits` is the arithmetic of
the budget.  Nothing here is proved: the structure is a list of obligations. -/
structure CanonicalHZeroInputs where
  /-- The canonical `h = 0` HIGH-HIGH packet value. -/
  S : ℂ
  /-- Its owner decomposition. -/
  parts : HZeroOwner → ℂ
  /-- The budget assigned to each owner. -/
  budgets : HZeroOwner → ℝ
  /-- The target bound. -/
  target : ℝ
  /-- **Complete coverage**: every contribution is owned exactly once. -/
  coverage : S = ∑ o, parts o
  /-- The full-nine first-remainder identity is the source of the
  decomposition (kernel-proved separately as
  `fullNine_canonical_firstRemainder_telescope`). -/
  firstRemainderIdentity : Prop
  /-- The canonical switched residual vanishes (kernel-proved separately as
  `canonicalSwitchedResidual_eq_zero`). -/
  canonicalResidualZero : Prop
  /-- The analytic/source bound attached to each owner.  **These are the
  premises that are not proved in this repository.** -/
  partBounds : ∀ o, ‖parts o‖ ≤ budgets o
  /-- The budgets fit inside the target. -/
  budgetFits : ∑ o, budgets o ≤ target

/-- **`canonicalHZeroHighHigh_of_bank`.**  The canonical `h = 0` target
inequality follows from the explicit bank of premises.  This is a purely
logical compiler: it consumes the analytic inputs, it does not create them. -/
theorem canonicalHZeroHighHigh_of_bank (B : CanonicalHZeroInputs) :
    ‖B.S‖ ≤ B.target := by
  calc ‖B.S‖ = ‖∑ o, B.parts o‖ := by rw [B.coverage]
    _ ≤ ∑ o, ‖B.parts o‖ := norm_sum_le _ _
    _ ≤ ∑ o, B.budgets o := Finset.sum_le_sum fun o _ => B.partBounds o
    _ ≤ B.target := B.budgetFits

/-- **Firewall: the compiler is not unconditional.**  Without analytic input
there is no bank at all; in particular no bank can certify a nonzero packet
against a zero target. -/
theorem canonicalHZero_no_free_lunch :
    ¬ ∃ B : CanonicalHZeroInputs, B.S = 1 ∧ B.target = 0 := by
  rintro ⟨B, hS, ht⟩
  have h := canonicalHZeroHighHigh_of_bank B
  rw [hS, ht] at h
  norm_num at h

/-- **Firewall: research closure is not kernel closure.**  The research status
`ANALYTICALLY CLOSED` is a string of metadata, and is recorded as such. -/
def canonicalHZeroResearchStatus : String :=
  "CANONICAL-HZERO-HIGHHIGH45: ANALYTICALLY CLOSED (research bank); " ++
    "formal status: conditional compiler with every analytic/source input explicit."

end CanonicalHZero
end CurrentProgramme
end TwinPrimeProject
