import RequestProject.CurrentProgramme.CurrentStatusGate1BRamanujanReciprocal
import Gate1B.RamRecPostReduction
import Gate1B.RatioDiagonalPhysicalisation
import Gate1B.ALineBetaU2Pushforward
import Gate1B.C4ShiftQFourierPushforward

/-!
# Gate 1B · C4Shift status layer (append-only)

This module **appends** a new status layer on top of
`LedgerRamanujanReciprocal.full`.  It imports the historical status layers and
does not modify them: every historical row remains visible and unchanged in its
own module.

## What the C4Shift delta kernel-proves

* Phase A (`Gate1B.RamRecPostReduction`): divisor–cofactor split of the modular
  inverse, the exact reciprocal phase, the phase-collision classification and
  the natural-scale ratio-fibre Cauchy inequality.
* Phase B (`Gate1B.RatioDiagonalPhysicalisation`): fibre orthogonality, the
  physical `s` congruence, the exact `R_full` character formula, the `λ`
  orthogonality, the shell congruence and the local weight reassembly
  `W_∞(N) = 1`.
* Phase C (`Gate1B.ALineBetaU2Pushforward`): the A-line Bézout parametrisation,
  the reciprocal residue `y_{u,ℓ}`, the `(q,v)` pushforward with a
  **divisor-type** fibre bound, the exact change of variables, finite Fourier
  inversion and the dual Cauchy interface.
* Phase D (`Gate1B.C4ShiftQFourierPushforward`): the load-bearing double-Fourier
  factorisation of `Γ̃`, the recovery of `Γ̃` from `Γ̂`, and the exact `Ĥ_j(θ,v)`
  pushforward.

## What it does NOT prove

The analytic estimate

`‖Ĥ_j‖_{L¹_θ ℓ²_v} ≤ naturalBound`

is the uninhabited socket
`C4ShiftQFourier.C4ShiftQFourierPushforwardInput`, and its stronger sufficient
child is `C4ShiftQFourier.C4ShiftPushforwardU2TransferInput`.  Neither is ever
constructed.

```
GATE1B : OPEN.
FIRST EXACT RESEARCH RESIDUAL : C4SHIFT-QFOURIER-PUSHFORWARD45.
```
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace LedgerC4Shift

open Status

set_option maxRecDepth 40000

/-- The C4Shift status layer, appended on top of
`LedgerRamanujanReciprocal.full`. -/
def full : List LedgerEntry :=
  [ ⟨"ADDMIN-RAMREC-DIVISOR-COFACTOR-SPLIT45", Status.provedAlgebraic,
     "FORMALLY BANKED (RamRecPostReduction.inverse_N_eq_inverse_r_mul_inverse_n_mod_M, with coprime_divisor_of_coprime_mul / coprime_cofactor_of_coprime_mul). No gcd(r,n)=1 hypothesis is used."⟩,
    ⟨"ADDMIN-RAMREC-PHASE-COLLISION45", Status.provedAlgebraic,
     "FORMALLY BANKED (RamRecPostReduction.phase_collision_classification, collision_denominators_eq, collision_residual_congruences, collision_ratio_congruence, ratioCoord). The analytic spacing estimate is NOT imported."⟩,
    ⟨"DETLINE-RAMREC-FIXEDM-RECIPROCAL-LS45", Status.provedFinite,
     "FORMALLY BANKED AT NATURAL SCALE (RamRecPostReduction.ratio_fibre_cauchy). A natural-scale combinatorial Cauchy bound only; NO negative-log saving is encoded."⟩,
    ⟨"RAMREC-LARGE-COFACTOR-BRANCH", Status.externallyAudited,
     "RESEARCH CLOSED (metadata only). No analytic bound is formalised."⟩,
    ⟨"RAMREC-RATIO-ZERO-CELL", Status.externallyAudited,
     "m_M = 0 cell: RESEARCH POWER CLOSED (metadata only). Not formalised."⟩,
    ⟨"RAMREC-HYBRID-M-R-OFFDIAGONAL", Status.externallyAudited,
     "RESEARCH POWER CLOSED (metadata only). Not formalised."⟩,
    ⟨"DETLINE-RAMREC-RATIO-PHYSICALISATION45", Status.provedAlgebraic,
     "FORMALLY BANKED (RatioPhysicalisation.fibre_orthogonality, physical_s_congruence, Rfibre_formula, sum_lambda_orthogonality, shell_congruence, local_coefficient, W_infty_eq_one, W_trunc_error_le). The physical range and no-wrap facts are the UNINHABITED interfaces RatioPhysicalRangeInput and RatioNoWrapInput."⟩,
    ⟨"DETLINE-RAMREC-NEARFULL-RATIO-PHASEGAP45", Status.supersededAsControllingFrontier,
     "SUPERSEDED / STRICTLY REDUCED; NOT FALSE."⟩,
    ⟨"DETLINE-RAMREC-RATIO-DIAGONAL-DEFECT-BETA45", Status.supersededAsControllingFrontier,
     "HISTORICAL CHILD. SUPERSEDED / STRICTLY REDUCED; NOT FALSE."⟩,
    ⟨"DETLINE-ALINE-BEZOUT45", Status.provedAlgebraic,
     "FORMALLY BANKED (ALinePushforward.aline_exists_A0, aline_A0_unique, aline_y_param, aline_q_param, y_congr_reciprocal, yCanon, exists_nu, q_param_canonical, line_shift)."⟩,
    ⟨"DETLINE-ALINE-QV-PUSHFORWARD45", Status.provedFinite,
     "FORMALLY BANKED (ALinePushforward.pushforward_dvd, pushforward_congr, ell_unique_in_window, fibre_card_le_divisors, Vsharp_pushforward, fourier_inversion, dual_cauchy_interface). The fixed (q,v) multiplicity is DIVISOR-type, not U/R-type."⟩,
    ⟨"BETAU2-RECIPROCAL-RESIDUE-RESTRICTION45", Status.supersededAsControllingFrontier,
     "STRICTLY REDUCED / NOT FALSE. The beta-U2 analytic input is the UNINHABITED interface ALinePushforward.BetaU2Input."⟩,
    ⟨"ALINE-T-DIAGONAL", Status.externallyAudited,
     "RESEARCH POWER CLOSED X^(-1/12+o(1)) (metadata only). Not formalised."⟩,
    ⟨"ALINE-SMALL-BETA-SHIFT", Status.externallyAudited,
     "RESEARCH POWER CLOSED X^(-5/36+o(1)) (metadata only). Not formalised."⟩,
    ⟨"ALINE-SQRT-U-OVER-R-INCIDENCE-TAX", Status.supersededAsControllingFrontier,
     "SUPERSEDED AS INTRINSIC OBSTRUCTION; NOT FALSE. Replaced by the divisor-type fibre bound fibre_card_le_divisors."⟩,
    ⟨"C4SHIFT-GAMMA-DOUBLE-FOURIER-FACTORISATION45", Status.provedAlgebraic,
     "FORMALLY BANKED, LOAD-BEARING (C4ShiftQFourier.GammaTilde_factorisation, with every sign kernel-checked; plus GammaTilde_eq_sum_GammaHat)."⟩,
    ⟨"C4SHIFT-HHAT-EXACT-PUSHFORWARD45", Status.provedAlgebraic,
     "FORMALLY BANKED (C4ShiftQFourier.Hhat_exact_pushforward). Exact change of variables only; no analytic estimate."⟩,
    ⟨"C4SHIFT-TOPBAND-KERNEL-IDENTIFICATION45", Status.sourceOpen,
     "SOURCE INTERFACE, UNINHABITED (C4ShiftQFourier.TopBandKernelInput): the identification K = m_top is not available in this repository."⟩,
    ⟨"DETLINE-ADDMIN-RAMANUJAN-RECIPROCAL-CROSSPAIR45", Status.supersededAsControllingFrontier,
     "SUPERSEDED AS CONTROLLING FRONTIER; NOT FALSE. Its own layer still records it as analyticOpen and is unchanged."⟩,
    ⟨"C4SHIFT-QFOURIER-PUSHFORWARD45", Status.analyticOpen,
     "CURRENT FIRST EXACT ANALYTIC RESIDUAL. ANALYTIC OPEN / UNINHABITED: C4ShiftQFourier.C4ShiftQFourierPushforwardInput is never constructed. Research natural bound Y^(3/4) log^C X; Lean proves no analytic estimate."⟩,
    ⟨"C4SHIFT-PUSHFORWARD-U2-TRANSFER45", Status.analyticOpen,
     "STRONGER THAN SOURCE-MINIMAL; OPEN. UNINHABITED: C4ShiftQFourier.C4ShiftPushforwardU2TransferInput."⟩,
    ⟨"TOPBAND-BETA-BROADMINOR-DETLINE45", Status.open_, "OPEN THROUGH C4SHIFT."⟩,
    ⟨"TOPBAND-RECURSIVE-MAJOR-TREE-PAIRING45", Status.open_, "OPEN."⟩,
    ⟨"TOPBAND-BROAD-MAJOR-TREE-MATCH45", Status.sourceOpen,
     "NOT RUN / SOURCE OPEN."⟩,
    ⟨"SHIFTED-MAM-TOPBAND45", Status.open_, "OPEN."⟩,
    ⟨"RANKONE-ENDPOINT-ALLK45", Status.open_, "OPEN."⟩,
    ⟨"PURE5", Status.open_, "OPEN. Not activated."⟩,
    ⟨"GATE1B", Status.open_, "OPEN."⟩ ]

/-! ## Honesty invariants -/

/-- **No row of this layer is `closed`.** -/
theorem no_closed_rows : ∀ e ∈ full, e.status ≠ Status.closed := by decide

/-- **The layer is honest.** -/
theorem ledger_is_honest : ∀ e ∈ full, e.honest := fun e he =>
  LedgerEntry.honest_of_not_closed (no_closed_rows e he)

/-- Gate 1B remains open at this layer. -/
theorem gate1B_open : (⟨"GATE1B", Status.open_, "OPEN."⟩ : LedgerEntry) ∈ full := by decide

/-- **The current first exact research residual** is the C4Shift `q`-Fourier
pushforward, and its status is *not* a kernel proof. -/
theorem c4shift_qfourier_is_first_residual :
    (∃ e ∈ full, e.label = "C4SHIFT-QFOURIER-PUSHFORWARD45" ∧
      e.status = Status.analyticOpen) ∧
    Status.analyticOpen.isKernelProved = false := by
  refine ⟨?_, by decide⟩
  decide

/-- **The stronger sufficient child is open too.** -/
theorem u2_transfer_open :
    ∃ e ∈ full, e.label = "C4SHIFT-PUSHFORWARD-U2-TRANSFER45" ∧
      e.status = Status.analyticOpen := by decide

/-- **Supersession is not falsification.**  Every superseded row of this layer
carries `supersededAsControllingFrontier`, which is distinct from
`falseRoute`. -/
theorem superseded_rows_are_not_false :
    ∀ e ∈ full, e.status = Status.supersededAsControllingFrontier →
      e.status ≠ Status.falseRoute := by decide

/-- **Preservation.**  The previous Ramanujan-reciprocal layer is untouched: its
own frontier row still reads `analyticOpen` there. -/
theorem previous_ramrec_layer_preserved :
    ∃ e ∈ LedgerRamanujanReciprocal.full,
      e.label = "DETLINE-ADDMIN-RAMANUJAN-RECIPROCAL-CROSSPAIR45" ∧
      e.status = Status.analyticOpen := by decide

/-- **No analytic row of this layer is kernel-proved.** -/
theorem analytic_rows_are_not_kernel_proved :
    ∀ e ∈ full, e.status = Status.analyticOpen →
      e.status.isKernelProved = false := by decide

end LedgerC4Shift
end CurrentProgramme
end TwinPrimeProject
