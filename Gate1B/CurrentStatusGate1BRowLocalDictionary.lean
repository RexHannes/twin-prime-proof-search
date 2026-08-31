import Gate1B.CurrentStatusGate1BPuncturedProductFourier
import Gate1B.Gate1BPhysicalRowLocalDictionaryInterface

/-!
# Gate 1B · row-local dictionary status layer (append-only)

This layer **appends** the row-local dictionary status rows on top of
`LedgerPuncturedProductFourier.full`.  Historical layers are imported, never
edited: every historical row remains visible and unchanged in its own module
(`previous_layer_preserved`, `historical_research_rows_preserved`).

## The distinction this layer enforces

```
kernel theorem bank  ≠  current research status.
```

* The punctured Fourier frame, the product-Fourier algebra, the primitive
  determinant arithmetic, the Möbius/gcd identities and the
  original-zero/cyclic-zero firewall stay **kernel-proved / permanent bank**.
* Their *analytic closure mechanisms* — "product-Fourier closes `h = 0`" and
  "the joint determinant-character / punctured-frame Gram supplies the missing
  `M^{-1/2}` contraction" — are **retracted**.  Retraction of a mechanism does
  not touch the algebra (`algebra_banked_while_mechanism_retracted`).
* `C4SHIFT-SAWTOOTH-APRECIPROCAL-MISMATCH45` as the *current first residual* is
  **superseded** (historical, not false); the row recorded in the previous
  layer is preserved unchanged.

```
CURRENT FIRST SOURCE RESIDUAL :
  ORIGINAL-E(q) / Z_E(q) PHYSICAL-ROWLOCAL-DICTIONARY45.

LEAF 4          : ANALYTICALLY CLOSED MODULO LOCAL SOURCE IDENTIFICATION.
LEAVES 1-3      : OPEN / NOT PROMOTED.
LEAF 5          : PURE LOCAL MODEL; BARE LEAF 5 IS NOT THE LEAF-4 OWNER.
h = 0 HIGH-HIGH : ANALYTICALLY CLOSED MODULO PHYSICAL LOCAL TREE MATCH.
HNE             : NOT RUN.
LOWER-D         : OPEN.
GATE1B          : OPEN.

EXACT REMAINING LEAF-4 ANALYTIC SAVING : NONE
  (an exact source-normalisation identity, not a missing power/log saving).
```
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace LedgerGate1BRowLocalDictionary

open Status
open TwinPrimeProject.CurrentProgramme.Gate1BRowLocal

set_option maxRecDepth 40000

/-! ## The appended ledger -/

/-- The row-local dictionary layer, appended on top of
`LedgerPuncturedProductFourier.full`. -/
def full : List LedgerEntry :=
  [ ⟨"BEZOUTROW-DET-INVARIANT45", Status.provedAlgebraic,
     "SOURCE-EXACT / FORMAL BANK: PASS (kernel-checked). f*b_h - c*a_h = N along the Bezout line; scaled form f*B_h - c*A_h = d*N."⟩,
    ⟨"HZERO-J4-ALPHA4-PRODUCTDIFF45-ARITHMETIC", Status.provedAlgebraic,
     "SOURCE-EXACT / FORMAL BANK: PASS (kernel-checked). c*u1*v1 - f*u2*v2 = -d*N and the literal -d*ell*r form. Arithmetic kernel only; the analytic reading is metadata."⟩,
    ⟨"DIRICHLET-ADDITIVE-CONV-FIREWALL45", Status.provedFinite,
     "FIREWALL: explicit countermodel. Dirichlet and additive convolution are never identified. No universal inequality between them is claimed."⟩,
    ⟨"NONCOMMUTATIVE-MAJORTREE-INTERFACE45", Status.provedAlgebraic,
     "SOURCE-EXACT / FORMAL BANK: ordered slots M1,M2,M3,M5 with ordered composition; countermodel forbids replacing composition by a scalar product. Fourier(alpha_4) = Fourier(lambda_1)*Fourier(lambda_2) is NOT formalised."⟩,
    ⟨"LEAF4-FORMAL-LOCAL-SPLIT45", Status.provedAlgebraic,
     "SOURCE-EXACT / FORMAL BANK: gamma_4 = gamma4Loc + gamma4Rem with rho_5 = delta_5 - lambda_5; c44Loc = lambda1 *_D lambda2 *_D lambda3 *_D lambda5 by associativity."⟩,
    ⟨"LEAF4-OWNER-FIREWALL45", Status.provedFinite,
     "FIREWALL: c44Loc != c45 by explicit countermodel. Equality is proved ONLY under the supplied hypothesis lambda_4 = lambda_5. Bare Leaf 5 is not the Leaf-4 owner."⟩,
    ⟨"HZERO-J4-ALPHA4-PRODUCTDIFF45", Status.externallyAudited,
     "LATEST ANALYTIC BANK: PASS in the external research bank. Metadata only; the Lean content is the arithmetic identity row above."⟩,
    ⟨"HZERO-J4-ALPHA4-NONCOMMUTATIVE-MAJORTREE45", Status.externallyAudited,
     "LATEST ANALYTIC BANK: PASS in the external research bank. Metadata only."⟩,
    ⟨"HZERO-J4-ALPHA4-BEZOUTROW-NONRESONANT45", Status.externallyAudited,
     "LATEST ANALYTIC BANK: CLOSED in the external research bank. Metadata only."⟩,
    ⟨"HZERO-J4-ALPHA4-BEZOUTROW-CENTREDGRAM45", Status.externallyAudited,
     "LATEST ANALYTIC BANK: ANALYTICALLY CLOSED AT FORMAL TREE LEVEL in the external research bank. Metadata only."⟩,
    ⟨"PRODUCT-FOURIER-CLOSURE-MECHANISM45", Status.falseRoute,
     "RETRACTED MECHANISM: product-Fourier does NOT close h = 0. The product-Fourier ALGEBRA remains kernel-proved and banked."⟩,
    ⟨"JOINT-FRAME-MSQRT-GAIN45", Status.falseRoute,
     "RETRACTED MECHANISM: the joint determinant-character / punctured-frame Gram does NOT supply the missing M^(-1/2) contraction. The punctured frame itself remains kernel-proved."⟩,
    ⟨"C4SHIFT-SAWTOOTH-APRECIPROCAL-MISMATCH45", Status.supersededAsControllingFrontier,
     "SUPERSEDED as current first residual (historical only, NOT false). The previous layer's own row is preserved unchanged."⟩,
    ⟨"HZeroPrimitiveDetNonzeroFull", Status.supersededAsControllingFrontier,
     "SUPERSEDED research annotation: 'candidateResearchClosed' is historical and is NOT current research truth. Historical row preserved."⟩,
    ⟨"HZeroHighHighAnalytic", Status.supersededAsControllingFrontier,
     "SUPERSEDED research annotation: 'candidateResearchClosed' is historical and is NOT current research truth. Current status of h = 0 high-high is CONDITIONAL on the physical local tree match."⟩,
    ⟨"LEAF4-CONDITIONAL-COMPILER45", Status.conditionalCompiler,
     "Purely logical. Antecedents: physical row-local dictionary validity plus the four named analytic hypotheses and the owner statement. NONE is supplied."⟩,
    ⟨"HZERO-HIGHHIGH-CONDITIONAL-COMPILER45", Status.conditionalCompiler,
     "Purely logical. Antecedents: Leaves 1-5 local. NONE is supplied. Does not imply Gate 1B closure."⟩,
    ⟨"ORIGINAL-E(q)/Z_E(q)-PHYSICAL-ROWLOCAL-DICTIONARY45", Status.sourceOpen,
     "CURRENT FIRST SOURCE RESIDUAL. Exposed as the interface PhysicalRowLocalDictionaryValid; E(q), Z_E(q), kappa_4 are data fields and are NOT assigned values."⟩,
    ⟨"Q1-PHYSICAL-NORMALISATION45", Status.sourceOpen,
     "SOURCE PIN: formal zero-mode present; centred-defect analytic coefficient negligible in the research bank; physical E(1)/Z_E(1) normalisation open."⟩,
    ⟨"Q2-PHYSICAL-NORMALISATION45", Status.sourceOpen,
     "SOURCE PIN: formal alternating major packet present; physical E(2)/Z_E(2) normalisation open."⟩,
    ⟨"LEAF4", Status.conditionalCompiler,
     "ANALYTICALLY CLOSED MODULO LOCAL SOURCE IDENTIFICATION. Exact remaining Leaf-4 analytic saving: NONE."⟩,
    ⟨"LEAF1", Status.open_, "OPEN / NOT PROMOTED."⟩,
    ⟨"LEAF2", Status.open_, "OPEN / NOT PROMOTED."⟩,
    ⟨"LEAF3", Status.open_, "OPEN / NOT PROMOTED."⟩,
    ⟨"LEAF5-LOCAL-MODEL45", Status.provedAlgebraic,
     "PURE LOCAL MODEL at the symbolic coefficient level. Bare Leaf 5 is NOT the Leaf-4 owner."⟩,
    ⟨"HZERO-HIGHHIGH", Status.conditionalCompiler,
     "ANALYTICALLY CLOSED MODULO PHYSICAL LOCAL TREE MATCH. Not a Lean theorem."⟩,
    ⟨"HNE", Status.open_, "NOT RUN."⟩,
    ⟨"LOWER-D", Status.open_, "OPEN."⟩,
    ⟨"GATE1B", Status.open_, "OPEN."⟩ ]

/-! ## Honesty invariants -/

/-- **No row of this layer is `closed`.** -/
theorem no_closed_rows : ∀ e ∈ full, e.status ≠ Status.closed := by decide

/-- **The layer is honest.** -/
theorem ledger_is_honest : ∀ e ∈ full, e.honest := fun e he =>
  LedgerEntry.honest_of_not_closed (no_closed_rows e he)

/-- Gate 1B remains open at this layer. -/
theorem gate1B_open : (⟨"GATE1B", Status.open_, "OPEN."⟩ : LedgerEntry) ∈ full := by decide

/-- **The current first source residual.** -/
theorem current_first_source_residual :
    ∃ e ∈ full, e.label = "ORIGINAL-E(q)/Z_E(q)-PHYSICAL-ROWLOCAL-DICTIONARY45" ∧
      e.status = Status.sourceOpen := by decide

/-- **The old C4Shift residual is superseded here, not deleted and not false.** -/
theorem old_c4shift_superseded :
    ∃ e ∈ full, e.label = "C4SHIFT-SAWTOOTH-APRECIPROCAL-MISMATCH45" ∧
      e.status = Status.supersededAsControllingFrontier := by decide

/-- **The previous layer is preserved unchanged**: its `GATE1B` row is still
open there and its own `C4SHIFT` row is still recorded there as
`analyticOpen`. -/
theorem previous_layer_preserved :
    (⟨"GATE1B", Status.open_, "OPEN."⟩ : LedgerEntry) ∈ LedgerPuncturedProductFourier.full ∧
      ∃ e ∈ LedgerPuncturedProductFourier.full,
        e.label = "C4SHIFT-SAWTOOTH-APRECIPROCAL-MISMATCH45" ∧
          e.status = Status.analyticOpen := by
  refine ⟨by decide, ?_⟩
  exact LedgerPuncturedProductFourier.first_analytic_residual

/-- **The historical research rows are preserved**: the two
`candidateResearchClosedExternally` rows of the previous layer are still there,
unchanged, and are marked `SUPERSEDED` only by the *new* rows above. -/
theorem historical_research_rows_preserved :
    ∀ e ∈ LedgerPuncturedProductFourier.researchRows,
      (e.label = "HZeroPrimitiveDetNonzeroFull" ∨ e.label = "HZeroHighHighAnalytic") →
      e.status = LedgerPuncturedProductFourier.ResearchStatus.candidateResearchClosedExternally :=
  LedgerPuncturedProductFourier.externally_closed_rows_are_research_only

/-- **Algebra banked while the mechanism is retracted.**  Both readings coexist:
the product-Fourier and punctured-frame *algebra* rows of the previous layer are
kernel-proved there, while the two *mechanism* rows of this layer are retracted
routes. -/
theorem algebra_banked_while_mechanism_retracted :
    (∃ e ∈ LedgerPuncturedProductFourier.full,
        e.label = "PRODUCT-FOURIER-GRAM45" ∧ e.status.isKernelProved = true) ∧
      (∃ e ∈ LedgerPuncturedProductFourier.full,
        e.label = "PUNCTURED-FOURIER-FRAME45" ∧ e.status.isKernelProved = true) ∧
      (∃ e ∈ full, e.label = "PRODUCT-FOURIER-CLOSURE-MECHANISM45" ∧
        e.status = Status.falseRoute) ∧
      (∃ e ∈ full, e.label = "JOINT-FRAME-MSQRT-GAIN45" ∧
        e.status = Status.falseRoute) := by decide

/-- **The new exact rows are kernel-proved algebra.** -/
theorem new_exact_rows_kernel_proved :
    ∀ e ∈ full,
      (e.label = "BEZOUTROW-DET-INVARIANT45" ∨
        e.label = "HZERO-J4-ALPHA4-PRODUCTDIFF45-ARITHMETIC" ∨
        e.label = "DIRICHLET-ADDITIVE-CONV-FIREWALL45" ∨
        e.label = "NONCOMMUTATIVE-MAJORTREE-INTERFACE45" ∨
        e.label = "LEAF4-FORMAL-LOCAL-SPLIT45" ∨
        e.label = "LEAF4-OWNER-FIREWALL45" ∨
        e.label = "LEAF5-LOCAL-MODEL45") →
      e.status.isKernelProved = true := by decide

/-- **The latest analytic bank rows are metadata, never kernel proofs.** -/
theorem analytic_bank_rows_not_kernel_proved :
    ∀ e ∈ full,
      (e.label = "HZERO-J4-ALPHA4-PRODUCTDIFF45" ∨
        e.label = "HZERO-J4-ALPHA4-NONCOMMUTATIVE-MAJORTREE45" ∨
        e.label = "HZERO-J4-ALPHA4-BEZOUTROW-NONRESONANT45" ∨
        e.label = "HZERO-J4-ALPHA4-BEZOUTROW-CENTREDGRAM45") →
      e.status.isKernelProved = false := by decide

/-- **Leaves 1-3, HNE and Lower-D remain open obligations.** -/
theorem open_branches :
    ∀ e ∈ full,
      (e.label = "LEAF1" ∨ e.label = "LEAF2" ∨ e.label = "LEAF3" ∨
        e.label = "HNE" ∨ e.label = "LOWER-D" ∨ e.label = "GATE1B") →
      e.status.isOpenObligation = true := by decide

/-- **Leaf 4 does not close Gate 1B**: Leaf 4 is a conditional compiler row while
Gate 1B is open. -/
theorem leaf4_does_not_close_gate1B :
    (∃ e ∈ full, e.label = "LEAF4" ∧ e.status = Status.conditionalCompiler) ∧
      (∃ e ∈ full, e.label = "GATE1B" ∧ e.status = Status.open_) := by decide

/-- **The source-pinned rows are open**, including the two small-`q`
normalisations. -/
theorem source_pins_open :
    ∀ e ∈ full,
      (e.label = "ORIGINAL-E(q)/Z_E(q)-PHYSICAL-ROWLOCAL-DICTIONARY45" ∨
        e.label = "Q1-PHYSICAL-NORMALISATION45" ∨
        e.label = "Q2-PHYSICAL-NORMALISATION45") →
      e.status.isOpenObligation = true := by decide

end LedgerGate1BRowLocalDictionary
end CurrentProgramme
end TwinPrimeProject
