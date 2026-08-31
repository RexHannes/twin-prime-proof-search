import Gate1B.CurrentStatusGate1BC4ShiftCenteredAP58
import Gate1B.PuncturedFourierFrame
import Gate1B.PrimitiveDeterminantProductPhase

/-!
# Gate 1B · punctured / product-Fourier status layer (append-only)

This layer appends the `h = 0` arithmetic and finite-linear-algebra backbone
(`Gate1B.PuncturedFourierFrame`, `Gate1B.PrimitiveDeterminantProductPhase`) on
top of `LedgerC4ShiftCenteredAP58.full`.  **Historical layers are imported,
never edited.**

## What is banked and what is not

The four `SOURCE-EXACT / FORMAL BANK` rows below are **kernel-checked exact
statements** of this repository:

* `DoubleGcdPrimitiveDet` — `PrimitiveDeterminant.doubleGcd_dvd_shift`,
  `primitiveDeterminant_factor`, `primitiveDeterminant_nonzero_of_shift_nonzero`;
* `PuncturedFourierFrame` — `PuncturedFourier.puncturedFourier_gram`,
  `puncturedFourier_gram_matrix`, `puncturedFourier_posDef`,
  `puncturedFourier_fullRowRank`, `puncturedFourier_minNorm_coeff_bound`;
* `ProductFourierGram` — `PuncturedFourier.productFourier_orthogonality`,
  `productFourier_gram`, `productFourier_norm_sq`;
* `PrimitiveGcdMobiusIdentity` — `PrimitiveDeterminant.coprime_indicator_mobius`,
  `double_coprime_indicator_mobius`.

The `RESEARCH STATUS ONLY` rows are recorded through a **separate datatype**
`ResearchStatus`, which is deliberately *not* a `Status` and which maps only to
non-kernel-proved statuses.  `researchStatus_never_kernelProved` is the Lean
firewall: no research row can be confused with a proof of an analytic
inequality.

```
GATE1B : OPEN.

CURRENT FIRST ANALYTIC RESEARCH RESIDUAL :
  C4SHIFT-SAWTOOTH-APRECIPROCAL-MISMATCH45.

PARALLEL LOCAL RESIDUAL :
  TOPBAND-BROAD-MAJOR-TREE-MATCH45.
```
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace LedgerPuncturedProductFourier

open Status

set_option maxRecDepth 40000

/-! ## Research-only status taxonomy

`ResearchStatus` records the *research* state of a claim that is **not** proved
in Lean.  It is a separate type from `Status` precisely so that a research row
cannot be mistaken for, or coerced into, a kernel-checked row. -/

/-- Research-only status of an analytic claim.  No constructor asserts a Lean
proof. -/
inductive ResearchStatus where
  /-- Considered closed in the external research bank, under a frozen source
  bank.  **Not** a Lean proof and not a repository theorem. -/
  | candidateResearchClosedExternally
  /-- Genuinely open. -/
  | researchOpen
  deriving DecidableEq, Repr, Inhabited

namespace ResearchStatus

/-- The conservative `Status` a research row is allowed to occupy. -/
def toStatus : ResearchStatus → Status
  | candidateResearchClosedExternally => Status.externallyAudited
  | researchOpen => Status.analyticOpen

end ResearchStatus

/-- **Firewall.**  No research status is kernel-proved. -/
theorem researchStatus_never_kernelProved (s : ResearchStatus) :
    s.toStatus.isKernelProved = false := by
  cases s <;> rfl

/-- **Firewall.**  No research status is `closed`. -/
theorem researchStatus_never_closed (s : ResearchStatus) :
    s.toStatus ≠ Status.closed := by
  cases s <;> decide

/-- A research-only ledger row. -/
structure ResearchEntry where
  /-- Literal label used in the reports. -/
  label : String
  /-- Research state; never a proof. -/
  status : ResearchStatus
  /-- Provenance / blocker note. -/
  note : String
  deriving DecidableEq, Repr, Inhabited

/-- The research-only rows of this layer. -/
def researchRows : List ResearchEntry :=
  [ ⟨"HZeroPrimitiveDetNonzeroFull", ResearchStatus.candidateResearchClosedExternally,
     "RESEARCH STATUS ONLY. Externally closed under the frozen source bank; NOT proved in Lean."⟩,
    ⟨"HZeroHighHighAnalytic", ResearchStatus.candidateResearchClosedExternally,
     "RESEARCH STATUS ONLY. Externally closed under the frozen source bank; NOT proved in Lean."⟩,
    ⟨"HNeSawtoothAPReciprocalMismatch", ResearchStatus.researchOpen,
     "OPEN. Current first analytic research residual (C4SHIFT-SAWTOOTH-APRECIPROCAL-MISMATCH45)."⟩,
    ⟨"TopBandBroadMajorTreeMatch", ResearchStatus.researchOpen,
     "OPEN. Parallel local residual (TOPBAND-BROAD-MAJOR-TREE-MATCH45)."⟩,
    ⟨"Gate1B", ResearchStatus.researchOpen, "OPEN."⟩ ]

/-- **No research row claims a Lean proof.** -/
theorem researchRows_never_kernelProved :
    ∀ e ∈ researchRows, e.status.toStatus.isKernelProved = false :=
  fun e _ => researchStatus_never_kernelProved e.status

/-- **The two externally-closed rows are recorded as research only.** -/
theorem externally_closed_rows_are_research_only :
    ∀ e ∈ researchRows,
      (e.label = "HZeroPrimitiveDetNonzeroFull" ∨ e.label = "HZeroHighHighAnalytic") →
      e.status = ResearchStatus.candidateResearchClosedExternally := by decide

/-- **Gate 1B is recorded open in the research rows.** -/
theorem gate1B_research_open :
    (⟨"Gate1B", ResearchStatus.researchOpen, "OPEN."⟩ : ResearchEntry) ∈ researchRows := by
  decide

/-! ## The appended ledger -/

/-- The punctured / product-Fourier layer, appended on top of
`LedgerC4ShiftCenteredAP58.full`. -/
def full : List LedgerEntry :=
  [ ⟨"DOUBLEGCD-PRIMITIVE-DET45", Status.provedAlgebraic,
     "SOURCE-EXACT / FORMAL BANK: PASS. de | r, bf-ac = ell*r0, nonvanishing, semi-diagonal exclusions. Physical bounds are hypotheses."⟩,
    ⟨"PUNCTURED-FOURIER-FRAME45", Status.provedAlgebraic,
     "SOURCE-EXACT / FORMAL BANK: PASS (kernel-checked). Gram M*1 - J, positivity for #I < M, full row rank, min-norm coefficient bound."⟩,
    ⟨"PUNCTURED-FOURIER-UNITDILATE45", Status.provedAlgebraic,
     "SOURCE-EXACT / FORMAL BANK: PASS (kernel-checked). Unit dilation has the identical Gram and the same rank."⟩,
    ⟨"PRODUCT-FOURIER-GRAM45", Status.provedAlgebraic,
     "SOURCE-EXACT / FORMAL BANK: PASS (kernel-checked). T_lambda^H T_lambda = M*1 and the exact Plancherel identity. The sqrt(M) operator norm is recorded in the report only."⟩,
    ⟨"PRIMITIVE-GCD-MOBIUS45", Status.provedAlgebraic,
     "SOURCE-EXACT / FORMAL BANK: PASS. Finite divisor identities only; no analytic divisor moment."⟩,
    ⟨"DETERMINANT-PHASE-FACTORISATION45", Status.provedAlgebraic,
     "SOURCE-EXACT / FORMAL BANK: PASS. e_M(k*ell*r0) = e_M(k*b*f)*e_M(-k*a*c) from bf-ac = ell*r0."⟩,
    ⟨"PRIME-DVD-MUL-ROUTER45", Status.provedAlgebraic,
     "SOURCE-EXACT / FORMAL BANK: PASS. Supports the analytic large-divisor router; the analytic estimate is NOT formalised."⟩,
    ⟨"ORIGINALZERO-PRESERVED45", Status.provedAlgebraic,
     "FIREWALL: original determinant zero implies cyclic zero; that is the only implication proved."⟩,
    ⟨"CYCLICZERO-NOT-IDENTIFIED45", Status.provedFinite,
     "FIREWALL: explicit countermodel. Cyclic zero is NOT the original determinant zero; no false equality is encoded."⟩,
    ⟨"PUNCTUREDFRAME-USES-NONZEROONLY45", Status.provedAlgebraic,
     "FIREWALL: the punctured frame avoids the auxiliary zero frequency entirely."⟩,
    ⟨"GATE1B-NET-CONDITIONAL-COMPILER45", Status.conditionalCompiler,
     "Purely logical implication. Support / product-gain / scale hypotheses are NOT supplied here."⟩,
    ⟨"ECELL-T-OVER-SQRT-E-SUPPORT45", Status.analyticOpen,
     "NOT FORMALISED: no literal upstream Lean theorem. Exposed only as a hypothesis of the conditional compiler."⟩,
    ⟨"FIXEDDEPTH-ALPHA-GAMMA-DIVISOR-MOMENTS45", Status.analyticOpen,
     "NOT FORMALISED: no literal upstream Lean theorem."⟩,
    ⟨"NET-ANALYTIC-MSQRT-COMPILER45", Status.analyticOpen,
     "NOT FORMALISED: only the conditional algebraic compiler exists."⟩,
    ⟨"HNE-RECIPROCAL-CLOSURE45", Status.analyticOpen, "NOT FORMALISED. OPEN."⟩,
    ⟨"LOCAL-BROAD-MAJOR-TREE-MATCH45", Status.analyticOpen, "NOT FORMALISED. OPEN."⟩,
    ⟨"C4SHIFT-SAWTOOTH-APRECIPROCAL-MISMATCH45", Status.analyticOpen,
     "CURRENT FIRST ANALYTIC RESEARCH RESIDUAL. OPEN."⟩,
    ⟨"TOPBAND-BROAD-MAJOR-TREE-MATCH45", Status.sourceOpen,
     "PARALLEL LOCAL RESIDUAL. SOURCE OPEN."⟩,
    ⟨"GATE1B", Status.open_, "OPEN."⟩ ]

/-! ## Honesty invariants -/

/-- **No row of this layer is `closed`.** -/
theorem no_closed_rows : ∀ e ∈ full, e.status ≠ Status.closed := by decide

/-- **The layer is honest.** -/
theorem ledger_is_honest : ∀ e ∈ full, e.honest := fun e he =>
  LedgerEntry.honest_of_not_closed (no_closed_rows e he)

/-- Gate 1B remains open at this layer. -/
theorem gate1B_open : (⟨"GATE1B", Status.open_, "OPEN."⟩ : LedgerEntry) ∈ full := by decide

/-- **The current first analytic research residual.** -/
theorem first_analytic_residual :
    ∃ e ∈ full, e.label = "C4SHIFT-SAWTOOTH-APRECIPROCAL-MISMATCH45" ∧
      e.status = Status.analyticOpen := by decide

/-- **The parallel local residual.** -/
theorem parallel_local_residual :
    ∃ e ∈ full, e.label = "TOPBAND-BROAD-MAJOR-TREE-MATCH45" ∧
      e.status = Status.sourceOpen := by decide

/-- **The previous layer is preserved unchanged**: its own `GATE1B` row is still
`open_` there, and its first analytic residual is still recorded there. -/
theorem previous_layer_preserved :
    (⟨"GATE1B", Status.open_, "OPEN."⟩ : LedgerEntry) ∈ LedgerC4ShiftCenteredAP58.full ∧
      ∃ e ∈ LedgerC4ShiftCenteredAP58.full,
        e.label = "C4SHIFT-OFFDIAG-CENTERED-AP5/8-GRAM45" ∧
          e.status = Status.analyticOpen := by
  refine ⟨by decide, ?_⟩
  exact LedgerC4ShiftCenteredAP58.first_analytic_residual

/-- **The new exact rows are kernel-proved algebra.** -/
theorem new_exact_rows_kernel_proved :
    ∀ e ∈ full,
      (e.label = "DOUBLEGCD-PRIMITIVE-DET45" ∨ e.label = "PUNCTURED-FOURIER-FRAME45" ∨
        e.label = "PUNCTURED-FOURIER-UNITDILATE45" ∨ e.label = "PRODUCT-FOURIER-GRAM45" ∨
        e.label = "PRIMITIVE-GCD-MOBIUS45" ∨ e.label = "DETERMINANT-PHASE-FACTORISATION45" ∨
        e.label = "PRIME-DVD-MUL-ROUTER45" ∨ e.label = "CYCLICZERO-NOT-IDENTIFIED45" ∨
        e.label = "ORIGINALZERO-PRESERVED45" ∨
        e.label = "PUNCTUREDFRAME-USES-NONZEROONLY45") →
      e.status.isKernelProved = true := by decide

/-- **The Gate-1B closure row is not claimed**: every `NOT FORMALISED` row is an
open obligation, never kernel-proved. -/
theorem not_formalised_rows_open :
    ∀ e ∈ full,
      (e.label = "ECELL-T-OVER-SQRT-E-SUPPORT45" ∨
        e.label = "FIXEDDEPTH-ALPHA-GAMMA-DIVISOR-MOMENTS45" ∨
        e.label = "NET-ANALYTIC-MSQRT-COMPILER45" ∨
        e.label = "HNE-RECIPROCAL-CLOSURE45" ∨
        e.label = "LOCAL-BROAD-MAJOR-TREE-MATCH45") →
      e.status.isOpenObligation = true := by decide

/-- **The conditional compiler row is not `closed`** (the source-level firewall
of `not_closed_of_conditionalCompiler`). -/
theorem conditional_compiler_row_not_closed :
    ∀ e ∈ full, e.label = "GATE1B-NET-CONDITIONAL-COMPILER45" →
      e.status ≠ Status.closed := by decide

end LedgerPuncturedProductFourier
end CurrentProgramme
end TwinPrimeProject
