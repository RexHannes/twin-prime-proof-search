import RequestProject.CurrentProgramme.CurrentStatusGate1BAdditiveMinor
import RequestProject.CurrentProgramme.AddMinSourceCoprimalityMuLog
import RequestProject.CurrentProgramme.AddMinRamanujanReciprocity
import RequestProject.CurrentProgramme.DetLineAddMinRamanujanReciprocalSocket

/-!
# Gate 1B · Ramanujan-reciprocal delta status layer (append-only)

**Append-only.**  This module adds one new status layer on top of
`LedgerAdditiveMinor.full` (the newest Gate 1B layer actually present).  It does
**not** modify `CurrentStatusGate1BAdditiveMinor`, `CurrentStatusGate1BFiniteLift`,
`CurrentStatusShiftedMAMOperator`, `CurrentStatusHighKShift`, or any earlier
ledger, and it does not change the meaning of any historical label.

## What this delta kernel-proves

* the source coprimality seal, *conditional on* the uninhabited routing
  interface `AddMinCleanCoprimalityInput` (with an explicit countermodel showing
  the seal may not be justified by a size comparison);
* `Λ = μ ∗ log` in its exact divisor form and the one-sided source expansion;
* the Ramanujan sum, its Hölder form and the exact divisor identity
  `∑_{rRam ∣ N} c_{rRam}(B) = N · 1_{N ∣ B}`;
* modular-inverse quotient elimination (`ZMod` and integer forms);
* the Ramanujan reciprocity theorem;
* the reduction of `N⁻¹ mod q_ℓ` to `N⁻¹ mod M`, the `q_ℓ = ℓ M` phase splitting
  and the exact reciprocal phase normal form;
* the companion reciprocal normal-form compiler.

## What this delta does NOT prove

The source-coupled arbitrary-log Ramanujan-reciprocal crosspair estimate.  It is
the uninhabited interface
`AddMinRamanujanSocket.DetLineAddMinRamanujanReciprocalCrosspairInput`.

```
TOPBAND : OPEN.   PURE5 : OPEN.   GATE1B : OPEN.
```
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace LedgerRamanujanReciprocal

open Status

set_option maxRecDepth 40000

/-! ## The new status layer -/

/-- The Ramanujan-reciprocal delta layer, appended on top of
`LedgerAdditiveMinor.full`. -/
def full : List LedgerEntry :=
  [ ⟨"ADDMIN-ACTUAL-DEFECT-SOURCE45", Status.sourceOpen,
     "SOURCE ADAPTER, UNINHABITED. The repository contains no literal definitions delta_j / lambda_j / rho_j / Pi_ell; the additive-minor layer carries them only as abstract fields. AddMinSource.AddMinActualDefectSourceInput records the two source equations delta = (Λ-1) W(s/Y)/log s and rhoHat = (1-Pi) deltaHat; it is never constructed. The conditional compiler defectSource_adapter_muLog IS kernel-proved. Research/source-level PASS is metadata only."⟩,
    ⟨"ADDMIN-ONE-SIDED-MU-LOG45", Status.provedAlgebraic,
     "KERNEL-PROVED (AddMinSource.vonMangoldt_eq_moebius_log_divisorSum, oneSided_muLog_expansion, defectSource_muLog_form), reusing Mathlib's moebius_mul_log_eq_vonMangoldt. NO Type-I/II analytic estimate is formalised."⟩,
    ⟨"ADDMIN-CLEAN-COPRIMALITY-SEAL45", Status.conditionalCompiler,
     "SEALED, CONDITIONAL ON AN UNINHABITED SOURCE INTERFACE. cleanSector_coprime_N_ell / _N_M / _N_qell are kernel-proved from AddMinCleanCoprimalityInput (M prime, M ∤ uA, gcd(uA,ell)=1). The missing source lemmas are exactly M ∤ uA and gcd(uA,ell)=1. The false justification 'N < M' is refuted: size_alone_does_not_give_coprimality, source_product_can_exceed_M."⟩,
    ⟨"DETLINE-ADDMIN-ONE-SIDED-VAUGHAN45", Status.notCurrentlyRequired,
     "NONCLOSING AS STANDALONE ROUTE (research metadata only). NOT marked false; simply not the controlling route. No analytic claim about it is formalised."⟩,
    ⟨"DETLINE-COMPANION-ADDMIN-ENERGY45", Status.analyticOpen,
     "OPEN / STRONGER SUFFICIENT ROUTE. Would suffice if available; not formalised, not inhabited."⟩,
    ⟨"ADDMIN-RAMANUJAN-RECIPROCITY45", Status.provedAlgebraic,
     "KERNEL-PROVED: ramanujanC (character definition), ramanujanC_hoelder, ramanujan_divisor_sum with explicit branches _of_dvd / _of_not_dvd, ramanujan_reassembly_is_divisibility_projector, exists_int_inverse, zmod_inv_mul_cancel, inv_quotient, ezExp_inv_quotient, addMin_ramanujan_reciprocity. The indicator 1_{N∣B} is never hidden in a definition."⟩,
    ⟨"DETLINE-ADDMIN-RECIPROCAL-QUOTIENT-SEPARATION45", Status.provedAlgebraic,
     "EXACT NORMAL FORM KERNEL-PROVED: inv_reduction_qell_to_M, inv_unique_mod_M, phase_split_qell, ezExp_M_inv_reduction, phase_split_rRam, reciprocal_phase_normalForm, roughTransform, addMin_companion_ramanujan_normalForm. The compiler is a deterministic implication from printed finite hypotheses (uA > 0, the two inverse congruences, ell ≠ 0, support); it is NOT conditional on any analytic estimate."⟩,
    ⟨"DETLINE-ADDMIN-QUOTIENT-REMOVAL-FIREWALL45", Status.provedFinite,
     "QUOTIENT COUPLING REMOVED FROM THE ROUGH COEFFICIENT (old_representation_depends_on_quotient shows the old representation genuinely depended on B/N; reciprocal_summand_is_quotient_free shows the new summand takes no quotient argument). NEW COUPLING RECORDED, NOT CLAIMED ABSENT: moving divisor rRam ∣ uA + reciprocal (uA)⁻¹ phase + rough transform at the same Theta (new_coupling_is_present)."⟩,
    ⟨"DETLINE-ADDMIN-MOBIUS-PRIME-DISPERSION45", Status.notCurrentlyRequired,
     "NO POINTWISE ONE-SIDED CLOSURE AT CURRENT RESEARCH BOUNDS (research metadata only). NOT marked false and NOT formalised."⟩,
    ⟨"DETLINE-ADDMIN-DOUBLE-SOURCE-RANKGAIN45", Status.notCurrentlyRequired,
     "REPRESENTATION LOOP / NO NEW INDEPENDENT RELATION AT RESEARCH LEVEL. The only Lean content is the honest reassembly fact: summing the complete Ramanujan divisor family returns the original divisibility projector (ramanujan_reassembly_is_divisibility_projector). NO analytic TT* loop is claimed."⟩,
    ⟨"DETLINE-NEARPRIM-ADDITIVE-MINOR-CROSSPAIR45", Status.supersededAsControllingFrontier,
     "SUPERSEDED AS CONTROLLING FRONTIER / STRICTLY REDUCED; NOT FALSE. Its quotient-coupled representation is replaced by the Ramanujan-reciprocal representation. The supersession is EXTERNALLY AUDITED, not kernel-proved."⟩,
    ⟨"DETLINE-ADDMIN-RAMANUJAN-RECIPROCAL-CROSSPAIR45", Status.analyticOpen,
     "FIRST EXACT RESEARCH RESIDUAL. AddMinRamanujanSocket.DetLineAddMinRamanujanReciprocalCrosspairInput; UNINHABITED anywhere in this repository. All source slots are retained: e, c, ell = c e, q_ell = ell M, m, rhoHat(m), u, A, rRam ∣ uA, x mod rRam unit, inverse(uA) mod q_ell and mod M, Theta, mu(d), log p, kappa(h), roughTransform."⟩,
    ⟨"TOPBAND-BETA-BROADMINOR-DETLINE45", Status.open_, "OPEN."⟩,
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

/-- TOPBAND is not activated at this layer. -/
theorem topband_not_activated :
    (⟨"TOPBAND-BETA-BROADMINOR-DETLINE45", Status.open_, "OPEN."⟩ : LedgerEntry) ∈ full ∧
    (⟨"SHIFTED-MAM-TOPBAND45", Status.open_, "OPEN."⟩ : LedgerEntry) ∈ full := by
  refine ⟨by decide, by decide⟩

/-- **Preservation.**  The previous additive-minor layer is untouched: its own
frontier row still reads `analyticOpen` there. -/
theorem previous_additiveMinor_layer_preserved :
    ∃ e ∈ LedgerAdditiveMinor.full,
      e.label = "DETLINE-NEARPRIM-ADDITIVE-MINOR-CROSSPAIR45" ∧
      e.status = Status.analyticOpen := by
  refine ⟨LedgerAdditiveMinor.full[7]!, by decide, by decide, by decide⟩

/-- **The historical additive-minor frontier is NOT false.**  In this layer it
carries `supersededAsControllingFrontier`, which is distinct from `falseRoute`. -/
theorem historical_additiveMinor_frontier_not_false :
    ∀ e ∈ full, e.label = "DETLINE-NEARPRIM-ADDITIVE-MINOR-CROSSPAIR45" →
      e.status = Status.supersededAsControllingFrontier ∧
      e.status ≠ Status.falseRoute := by decide

/-- **The Ramanujan-reciprocal crosspair is the current frontier**, and it is
`analyticOpen` — not kernel-proved. -/
theorem ramanujanReciprocal_is_current_frontier :
    (∃ e ∈ full, e.label = "DETLINE-ADDMIN-RAMANUJAN-RECIPROCAL-CROSSPAIR45" ∧
      e.status = Status.analyticOpen) ∧
    Status.analyticOpen.isKernelProved = false := by
  refine ⟨⟨full[11]!, by decide, by decide, by decide⟩, by decide⟩

/-- **The analytic socket is not inhabited here.**  Its ledger row is
`analyticOpen`, i.e. explicitly not a kernel proof; no inhabitant of
`DetLineAddMinRamanujanReciprocalCrosspairInput` is constructed anywhere in this
repository (see the axiom-audit module). -/
theorem analytic_socket_uninhabited :
    ∀ e ∈ full, e.label = "DETLINE-ADDMIN-RAMANUJAN-RECIPROCAL-CROSSPAIR45" →
      e.status = Status.analyticOpen ∧ e.status.isKernelProved = false := by decide

/-- **Quotient removed, source coupling retained.**  The firewall row records
both halves: the quotient is gone from the rough coefficient, and the new
coupling (moving `rRam ∣ uA`, reciprocal `(uA)⁻¹`, shared `Θ`) is present. -/
theorem quotient_removed_but_source_coupling_remains :
    ∃ e ∈ full, e.label = "DETLINE-ADDMIN-QUOTIENT-REMOVAL-FIREWALL45" ∧
      e.status = Status.provedFinite ∧
      e.status.isKernelProved = true := by
  refine ⟨full[7]!, by decide, by decide, by decide, by decide⟩

/-- **Non-claim.**  No `analyticOpen` row of this layer is kernel-proved. -/
theorem analytic_rows_are_not_kernel_proved :
    ∀ e ∈ full, e.status = Status.analyticOpen → e.status.isKernelProved = false := by
  decide

end LedgerRamanujanReciprocal
end CurrentProgramme
end TwinPrimeProject
