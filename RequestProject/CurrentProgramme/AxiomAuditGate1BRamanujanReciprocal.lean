import RequestProject.CurrentProgramme.CurrentStatusGate1BRamanujanReciprocal

/-!
# Axiom audit — Gate 1B Ramanujan-reciprocal delta layer

`#print axioms` for every principal declaration of the delta.  Expected output
for each: only `propext`, `Classical.choice`, `Quot.sound` (or a subset).  No
`sorryAx`, no `Lean.ofReduceBool`.

Token scan of the four new modules finds no `sorry`, `admit`, `axiom`,
`opaque`, `unsafe`, `native_decide` or `@[implemented_by]` outside prose.

Every analytic/source socket remains uninhabited:
`AddMinActualDefectSourceInput`, `AddMinCleanCoprimalityInput` and
`DetLineAddMinRamanujanReciprocalCrosspairInput` are never constructed here.
-/

namespace TwinPrimeProject
namespace CurrentProgramme

open AddMinSource AddMinRamanujan AddMinRamanujanSocket LedgerRamanujanReciprocal

/-! ## 1. `Λ = μ ∗ log` and the source adapter -/

#print axioms AddMinSource.vonMangoldt_eq_moebius_log_divisorSum
#print axioms AddMinSource.oneSided_muLog_expansion
#print axioms AddMinSource.defectSource_muLog_form
#print axioms AddMinSource.defectSource_adapter_muLog
#print axioms AddMinSource.defectSource_adapter_rhoHat

/-! ## 2. Clean coprimality lemmas -/

#print axioms AddMinSource.AddMinCleanCoprimalityInput.cleanSector_coprime_N_ell
#print axioms AddMinSource.AddMinCleanCoprimalityInput.cleanSector_coprime_N_M
#print axioms AddMinSource.AddMinCleanCoprimalityInput.cleanSector_coprime_N_qell
#print axioms AddMinSource.size_alone_does_not_give_coprimality
#print axioms AddMinSource.source_product_can_exceed_M

/-! ## 3. Ramanujan sums and the divisor-sum identity -/

#print axioms AddMinRamanujan.ezExp_modulus_mul
#print axioms AddMinRamanujan.ezExp_congr
#print axioms AddMinRamanujan.ramanujanC_one
#print axioms AddMinRamanujan.ramanujanC_hoelder
#print axioms AddMinRamanujan.ramanujan_divisor_sum
#print axioms AddMinRamanujan.ramanujan_divisor_sum_of_dvd
#print axioms AddMinRamanujan.ramanujan_divisor_sum_of_not_dvd
#print axioms AddMinRamanujan.ramanujan_reassembly_is_divisibility_projector

/-! ## 4. Modular inverse / quotient elimination -/

#print axioms AddMinRamanujan.exists_int_inverse
#print axioms AddMinRamanujan.zmod_inv_mul_cancel
#print axioms AddMinRamanujan.inv_quotient
#print axioms AddMinRamanujan.ezExp_inv_quotient

/-! ## 5. Ramanujan reciprocity -/

#print axioms AddMinRamanujan.addMin_ramanujan_reciprocity
#print axioms AddMinRamanujan.quotientPhase_to_reciprocal

/-! ## 6. Inverse reduction `q_ℓ → M` and phase splitting -/

#print axioms AddMinRamanujan.inv_reduction_qell_to_M
#print axioms AddMinRamanujan.inv_unique_mod_M
#print axioms AddMinRamanujan.phase_split_qell
#print axioms AddMinRamanujan.ezExp_M_inv_reduction
#print axioms AddMinRamanujan.phase_split_rRam
#print axioms AddMinRamanujan.reciprocal_phase_normalForm

/-! ## 7. Rough transform and the companion reciprocal normal form -/

#print axioms AddMinRamanujan.roughTransform_phase_law
#print axioms AddMinRamanujan.addMin_companion_ramanujan_normalForm
#print axioms AddMinRamanujan.old_representation_depends_on_quotient
#print axioms AddMinRamanujan.reciprocal_summand_is_quotient_free
#print axioms AddMinRamanujan.new_coupling_is_present

/-! ## 8. The analytic socket (uninhabited) -/

#print axioms AddMinRamanujanSocket.crosspair_input_is_an_assumption
#print axioms AddMinRamanujanSocket.socket_budget_is_not_a_saving
#print axioms AddMinRamanujanSocket.reciprocalCompanion_keeps_source
#print axioms AddMinRamanujanSocket.config_inv_reduction

/-! ## 9. Status declarations -/

#print axioms LedgerRamanujanReciprocal.full
#print axioms LedgerRamanujanReciprocal.no_closed_rows
#print axioms LedgerRamanujanReciprocal.ledger_is_honest
#print axioms LedgerRamanujanReciprocal.gate1B_open
#print axioms LedgerRamanujanReciprocal.pure5_not_activated
#print axioms LedgerRamanujanReciprocal.topband_not_activated
#print axioms LedgerRamanujanReciprocal.previous_additiveMinor_layer_preserved
#print axioms LedgerRamanujanReciprocal.historical_additiveMinor_frontier_not_false
#print axioms LedgerRamanujanReciprocal.ramanujanReciprocal_is_current_frontier
#print axioms LedgerRamanujanReciprocal.analytic_socket_uninhabited
#print axioms LedgerRamanujanReciprocal.quotient_removed_but_source_coupling_remains
#print axioms LedgerRamanujanReciprocal.analytic_rows_are_not_kernel_proved

end CurrentProgramme
end TwinPrimeProject
