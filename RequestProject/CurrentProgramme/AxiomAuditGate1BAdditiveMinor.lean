import RequestProject.CurrentProgramme.CurrentStatusGate1BAdditiveMinor
import RequestProject.CurrentProgramme.AxiomAuditGate1BFiniteLift

/-!
# Trust audit · Gate 1B additive-minor delta layer

`#print axioms` over the **new** declarations of this delta only.  Earlier
audits (`AxiomAuditGate1BFiniteLift`, `AxiomAuditShiftedMAMOperator`,
`AxiomAuditHighKShift`, …) are imported and left untouched.

Expected results: `propext`, `Classical.choice`, `Quot.sound`, or a subset.
No `sorryAx`, no `Lean.ofReduceBool`.

The new modules

```
FiniteLiftLocalTwistCompression
NearPrimitivePhysicalProjector
BroadMinorAdditiveFourier
DetLineCompanionAdditiveFourier
DetLineAdditiveMinorCrosspairSocket
CurrentStatusGate1BAdditiveMinor
```

contain no `sorry`, `admit`, user `axiom`, `opaque`, `unsafe`, `native_decide`
or `@[implemented_by]` (the only textual occurrences of those tokens are in
documentation paragraphs such as this one).

Every analytic/source interface introduced by this delta remains
**uninhabited**:

```
FiniteLiftLocalTwist.LocalTwistDivisorSummationInput
NearPrimitiveProjector.PrimitiveProjectorIdentityInput
NearPrimitiveProjector.SmallProjectorLargeLiftClosureInput
NearPrimitiveProjector.ProjectorWeightErrorEstimateInput
NearPrimitiveProjector.NearPrimitiveToPhysicalAnalyticInput
BroadMinorFourier.BroadMinorTransitionEstimateInput
AdditiveMinorCrosspair.DetLineNearPrimAdditiveMinorCrosspairInput
```
-/

namespace TwinPrimeProject
namespace CurrentProgramme

/-! ## Local-twist exact expansion -/

#print axioms FiniteLiftLocalTwist.additive_indicator
#print axioms FiniteLiftLocalTwist.localTwist_indicator
#print axioms FiniteLiftLocalTwist.moebius_coprime_indicator
#print axioms FiniteLiftLocalTwist.localTwist_cell_expansion
#print axioms FiniteLiftLocalTwist.localTwist_cell_card
#print axioms FiniteLiftLocalTwist.localTwist_cell_normalisation
#print axioms FiniteLiftLocalTwist.sum_ezExp
#print axioms FiniteLiftLocalTwist.sum_range_ezExp

/-! ## Large-projector diagonal and the primitive projector split -/

#print axioms NearPrimitiveProjector.eq_of_dvd_of_abs_le
#print axioms NearPrimitiveProjector.largeProjector_eq_zero_of_ne
#print axioms NearPrimitiveProjector.largeProjector_eq_omega
#print axioms NearPrimitiveProjector.projKernel_split
#print axioms NearPrimitiveProjector.physicalisation_split
#print axioms NearPrimitiveProjector.physicalisation_split_of_identity
#print axioms NearPrimitiveProjector.phiStar_eq_omega_add
#print axioms NearPrimitiveProjector.omega_sub_phiStar_abs_le_divisor
#print axioms NearPrimitiveProjector.induced_lift
#print axioms NearPrimitiveProjector.small_projector_routed_closed
#print axioms NearPrimitiveProjector.nearPrimitive_to_physical_of_input

/-! ## `ρ̂` multiplier identity, non-idempotence, plateau zero -/

#print axioms BroadMinorFourier.dftPlus_inner
#print axioms BroadMinorFourier.rhohat_eq
#print axioms BroadMinorFourier.rho_pairing
#print axioms BroadMinorFourier.rho_pairing_multiplier
#print axioms BroadMinorFourier.rho_pairing_multiplier_eq_zero_of_idempotent
#print axioms BroadMinorFourier.smooth_multiplier_is_not_automatically_an_orthogonal_projection
#print axioms BroadMinorFourier.plateau_contribution_zero
#print axioms BroadMinorFourier.regions_disjoint
#print axioms BroadMinorFourier.regions_cover
#print axioms BroadMinorFourier.transition_pairing_negligible_of_input

/-! ## Companion DFT normal form and divisibility completion -/

#print axioms DetLineCompanion.detline_iff
#print axioms DetLineCompanion.companionHat_normal_form
#print axioms DetLineCompanion.dvd_completion
#print axioms DetLineCompanion.completed_quotient_phase
#print axioms DetLineCompanion.companionHat_completed

/-! ## Additive-minor expression and socket -/

#print axioms AdditiveMinorCrosspair.additiveMinorCrossPair
#print axioms AdditiveMinorCrosspair.compHat_is_quotient_phase
#print axioms AdditiveMinorCrosspair.rhoHat_eq_deltaHat_on_minor
#print axioms AdditiveMinorCrosspair.crosspair_input_is_an_assumption
#print axioms AdditiveMinorCrosspair.cauchy_pairing_bound
#print axioms AdditiveMinorCrosspair.additiveMinorSeparateEnergy_natural_scale
#print axioms AdditiveMinorCrosspair.ttStar_identification_reconstructs_determinant_shell

/-! ## Current status declarations -/

#print axioms LedgerAdditiveMinor.full
#print axioms LedgerAdditiveMinor.no_closed_rows
#print axioms LedgerAdditiveMinor.ledger_is_honest
#print axioms LedgerAdditiveMinor.gate1B_open
#print axioms LedgerAdditiveMinor.pure5_not_activated
#print axioms LedgerAdditiveMinor.local_major_match_not_activated
#print axioms LedgerAdditiveMinor.previous_finiteLift_layer_preserved
#print axioms LedgerAdditiveMinor.previous_operator_layer_preserved
#print axioms LedgerAdditiveMinor.old_finiteLift_frontier_not_false
#print axioms LedgerAdditiveMinor.additiveMinor_is_current_research_frontier
#print axioms LedgerAdditiveMinor.analytic_crosspair_socket_uninhabited
#print axioms LedgerAdditiveMinor.analytic_rows_are_not_kernel_proved

end CurrentProgramme
end TwinPrimeProject
