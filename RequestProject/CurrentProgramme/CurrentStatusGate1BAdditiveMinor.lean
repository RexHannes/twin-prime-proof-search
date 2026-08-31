import RequestProject.CurrentProgramme.CurrentStatusGate1BFiniteLift
import RequestProject.CurrentProgramme.FiniteLiftLocalTwistCompression
import RequestProject.CurrentProgramme.NearPrimitivePhysicalProjector
import RequestProject.CurrentProgramme.BroadMinorAdditiveFourier
import RequestProject.CurrentProgramme.DetLineCompanionAdditiveFourier
import RequestProject.CurrentProgramme.DetLineAdditiveMinorCrosspairSocket

/-!
# Gate 1B · additive-minor delta status layer (append-only)

**Append-only.**  This module adds one new status layer on top of
`LedgerFiniteLift.full`.  It does **not** modify
`CurrentStatusGate1BFiniteLift`, `CurrentStatusShiftedMAMOperator`,
`CurrentStatusHighKShift`, or any earlier ledger, and it does not change the
meaning of any historical status label.

## What changed at research level

The previous research frontier
`DETLINE-NEARPRIM-FINITELIFT-DENSE-SATURATION45` is recorded as
`supersededAsControllingFrontier` — **strictly reduced, NOT false**.  The new
first exact research residual is
`DETLINE-NEARPRIM-ADDITIVE-MINOR-CROSSPAIR45`, `analyticOpen`, exposed as the
uninhabited interface
`AdditiveMinorCrosspair.DetLineNearPrimAdditiveMinorCrosspairInput`.

## What is kernel-proved by this delta

* the exact local-twist expansion and its finite cell bookkeeping;
* the pure order lemma and the exact projector split
  (large projectors → physical diagonal, small projectors → routed children);
* `ρ̂ = (1−Π)δ̂`, the exact multiplier pairing identity with its `Π(1−Π)`
  factor, the plateau-zero theorem, and the non-idempotence countermodel;
* the companion DFT normal form and the divisibility completion identity.

## What is NOT proved

Every analytic conclusion (arbitrary-log savings, projector-weight asymptotics,
divisor summation, transition density, and the additive-minor crosspair itself)
remains an uninhabited interface.

```
TOPBAND : OPEN.   PURE5 : OPEN.   GATE1B : OPEN.
```
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace LedgerAdditiveMinor

open Status

set_option maxRecDepth 40000

/-! ## The new status layer -/

/-- The additive-minor delta layer, appended on top of `LedgerFiniteLift.full`. -/
def full : List LedgerEntry :=
  [ ⟨"DETLINE-FINITELIFT-LOCAL-TWIST-COMPRESSION45", Status.provedFinite,
     "EXACT EXPANSION KERNEL-PROVED (FiniteLiftLocalTwist.localTwist_cell_expansion, localTwist_indicator, moebius_coprime_indicator, localTwist_cell_card). The analytic divisor-summation bookkeeping is NOT proved: LocalTwistDivisorSummationInput, UNINHABITED / externally audited."⟩,
    ⟨"DETLINE-NEARPRIM-PRIMITIVE-TO-PHYSICAL45", Status.conditionalCompiler,
     "FINITE ALGEBRA KERNEL-PROVED (eq_of_dvd_of_abs_le, largeProjector_eq_zero_of_ne, largeProjector_eq_omega, physicalisation_split, induced_lift, omega_sub_phiStar_abs_le_divisor). Weighted analytic conclusion CONDITIONAL: nearPrimitive_to_physical_of_input, with PrimitiveProjectorIdentityInput / SmallProjectorLargeLiftClosureInput / ProjectorWeightErrorEstimateInput all UNINHABITED. Externally audited weighted PASS at research level only."⟩,
    ⟨"BROADMINOR-INTERNAL-MAJOR-ORTHOGONALITY45", Status.provedFinite,
     "PLATEAU PART KERNEL-PROVED (rhohat_eq, rho_pairing_multiplier, plateau_contribution_zero, rho_pairing_multiplier_eq_zero_of_idempotent). SMOOTH Π IDEMPOTENCE IS NOT ASSUMED: smooth_multiplier_is_not_automatically_an_orthogonal_projection is an explicit countermodel. TRANSITION PART CONDITIONAL: transition_pairing_negligible_of_input with BroadMinorTransitionEstimateInput UNINHABITED."⟩,
    ⟨"DETLINE-COMPANION-ADDITIVE-FOURIER45", Status.provedAlgebraic,
     "KERNEL-PROVED: detline_iff (uA ∣ N and s = N/(uA), integrality exposed), companionHat_normal_form, dvd_completion, completed_quotient_phase, companionHat_completed. No analytic estimate."⟩,
    ⟨"ADDITIVE-MINOR-SEPARATE-ENERGY45", Status.capacityOnly,
     "NATURAL-SCALE / NONCLOSING AT RESEARCH LEVEL. Only the trivial Cauchy bound is available (cauchy_pairing_bound) and it is attained (additiveMinorSeparateEnergy_natural_scale). NOT marked false: the route is simply insufficient at the available norm sizes. No `nonclosingAtNaturalScale` constructor exists; `capacityOnly` is the nearest honest status."⟩,
    ⟨"ADDITIVE-MINOR-TTSTAR45", Status.notCurrentlyRequired,
     "REPRESENTATION LOOP / NONCONTROLLING ROUTE. Identifying the two physical s variables returns the same determinant shell (ttStar_identification_reconstructs_determinant_shell). NO general TT* theorem is marked false; the full analytic TT* argument is not formalised."⟩,
    ⟨"DETLINE-NEARPRIM-FINITELIFT-DENSE-SATURATION45", Status.supersededAsControllingFrontier,
     "SUPERSEDED AS CONTROLLING FRONTIER / STRICTLY REDUCED; NOT FALSE. Its unresolved finite-lift contribution is now represented by the additive-minor crosspair socket. The supersession itself is EXTERNALLY AUDITED, not kernel-proved."⟩,
    ⟨"DETLINE-NEARPRIM-ADDITIVE-MINOR-CROSSPAIR45", Status.analyticOpen,
     "FIRST EXACT CURRENT RESEARCH RESIDUAL. AdditiveMinorCrosspair.DetLineNearPrimAdditiveMinorCrosspairInput; NOT INHABITED anywhere in this repository. The exact expression additiveMinorCrossPair retains finite lift e, conductor c, ell = c e, weight w_{c,e}, q_ell, additive-minor frequency m, the actual (1-Π)δ̂ multiplier form, the genuine quotient phase with its divisibility condition, the variables u,A,d,p,h, μ(d), log p, κ(h) and the physical coefficient source."⟩,
    ⟨"DETLINE-HIGHCOND-BETA-RHO-CROSSPAIR45", Status.analyticOpen,
     "PARTIAL: LARGE-LIFT CLOSED at research level; FINITE-LIFT CHILD REDUCED TO THE ADDITIVE-MINOR CROSSPAIR. Recorded analyticOpen for the surviving finite-lift child."⟩,
    ⟨"TOPBAND-BETA-BROADMINOR-DETLINE45", Status.open_, "OPEN."⟩,
    ⟨"TOPBAND-RECURSIVE-MAJOR-TREE-PAIRING45", Status.open_, "OPEN."⟩,
    ⟨"TOPBAND-BROAD-MAJOR-TREE-MATCH45", Status.sourceOpen,
     "NOT RUN / SOURCE OPEN. The local major-match provider is not activated."⟩,
    ⟨"SHIFTED-MAM-TOPBAND45", Status.open_, "OPEN."⟩,
    ⟨"RANKONE-ENDPOINT-ALLK45", Status.conditionalCompiler,
     "CONDITIONAL / OPEN. Compiler only; antecedents not supplied."⟩,
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

/-- PURE5 is not activated. -/
theorem pure5_not_activated :
    (⟨"PURE5", Status.open_, "OPEN. Not activated."⟩ : LedgerEntry) ∈ full := by decide

/-- The local major-match provider is not activated. -/
theorem local_major_match_not_activated :
    (⟨"TOPBAND-BROAD-MAJOR-TREE-MATCH45", Status.sourceOpen,
      "NOT RUN / SOURCE OPEN. The local major-match provider is not activated."⟩
        : LedgerEntry) ∈ full ∧ Status.sourceOpen.isKernelProved = false := by
  refine ⟨by decide, by decide⟩

/-- **Preservation.**  The previous finite-lift layer is untouched: its rows are
still exactly the rows of `LedgerFiniteLift.full`, including its own frontier
row. -/
theorem previous_finiteLift_layer_preserved :
    (⟨"DETLINE-NEARPRIM-FINITELIFT-DENSE-SATURATION45", Status.analyticOpen,
      "LATEST RESEARCH FRONTIER / FIRST EXACT RESEARCH RESIDUAL. Surviving range 1 ≤ e ≤ (log X)^{B_A}, ell = c*e ~ R, c ~ R (log X)^{-O_A(1)}. Not attacked here."⟩
        : LedgerEntry) ∈ LedgerFiniteLift.full := by decide

/-- **Preservation.**  The operator layer's frontier row is untouched. -/
theorem previous_operator_layer_preserved :
    (⟨"SHIFTED-MAM-FIVEFOLD-OPERATOR45", Status.analyticOpen,
      "OPEN_ANALYTIC / FIRST EXACT ANALYTIC RESIDUAL. MAMOperator.ShiftedMAMFivefoldOperatorInput; UNINHABITED; canonical local term M_h^can kept explicit."⟩
        : LedgerEntry) ∈ LedgerMAMOperator.full := by decide

/-- **The old finite-lift frontier is NOT false.**  In the new layer it carries
`supersededAsControllingFrontier`, which is distinct from `falseRoute`. -/
theorem old_finiteLift_frontier_not_false :
    ∀ e ∈ full, e.label = "DETLINE-NEARPRIM-FINITELIFT-DENSE-SATURATION45" →
      e.status = Status.supersededAsControllingFrontier ∧
      e.status ≠ Status.falseRoute := by decide

/-- **The current research frontier** is the additive-minor crosspair, and it is
`analyticOpen` — not kernel-proved. -/
theorem additiveMinor_is_current_research_frontier :
    (∃ e ∈ full, e.label = "DETLINE-NEARPRIM-ADDITIVE-MINOR-CROSSPAIR45" ∧
      e.status = Status.analyticOpen) ∧
    Status.analyticOpen.isKernelProved = false := by
  refine ⟨?_, by decide⟩
  refine ⟨full[7]!, by decide, by decide, by decide⟩

/-- **The analytic crosspair socket is not inhabited here.**  Its ledger row is
`analyticOpen`, i.e. explicitly *not* a kernel proof; no inhabitant of
`DetLineNearPrimAdditiveMinorCrosspairInput` is constructed anywhere in this
repository (see the axiom-audit module).  Note that the socket asserts a
*declared budget*: an instance with an arbitrarily large budget would carry no
saving and is therefore not the research theorem. -/
theorem analytic_crosspair_socket_uninhabited :
    ∀ e ∈ full, e.label = "DETLINE-NEARPRIM-ADDITIVE-MINOR-CROSSPAIR45" →
      e.status = Status.analyticOpen ∧ e.status.isKernelProved = false := by decide

/-- **Non-claim.**  No DETLINE research row of this layer is kernel-proved as an
analytic theorem; only the finite/algebraic rows carry kernel proofs, and those
are exactly the exact-identity rows. -/
theorem analytic_rows_are_not_kernel_proved :
    ∀ e ∈ full, e.status = Status.analyticOpen → e.status.isKernelProved = false := by
  decide

end LedgerAdditiveMinor
end CurrentProgramme
end TwinPrimeProject
