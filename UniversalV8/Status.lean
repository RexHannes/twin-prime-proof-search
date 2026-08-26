/-
# UniversalV8 — status and axiom audit

Imports every new theorem module and runs `#print axioms` on every principal theorem.
Only `propext`, `Classical.choice`, `Quot.sound` may appear.

No `sorry`, no `admit`, no user `axiom`, no `opaque`, no `native_decide`,
no `@[implemented_by]` occurs in the UniversalV8 bank.
-/
import UniversalV8.DiscreteAbel
import UniversalV8.BoundedVariation
import UniversalV8.Synthesis
import UniversalV8.BlockGram
import UniversalV8.DiagonalBaseline
import UniversalV8.Budget
import UniversalV8.DefectCapacity
import UniversalV8.Countermodels
import UniversalV8.Interfaces
import Gate1A.SafeAlgebra.BPExponentRepair
import Gate1B.SafeAlgebra.NPLBudget
import Gate1B.SafeAlgebra.NPLDiagonalReduction
import Gate1B.SafeAlgebra.RouteVariation

namespace UniversalV8.Status

/-! ## Module A — discrete Abel -/
#print axioms UniversalV8.local_sum_by_parts
#print axioms UniversalV8.local_sum_by_parts_succ
#print axioms UniversalV8.norm_sum_le_partialSumBound_mul_variation

/-! ## Module B / C — discrete BV and routing jumps -/
#print axioms UniversalV8.variation_const
#print axioms UniversalV8.variation_smul
#print axioms UniversalV8.variation_add
#print axioms UniversalV8.variation_sub
#print axioms UniversalV8.variation_mul
#print axioms UniversalV8.variation_concat
#print axioms UniversalV8.variation_mono
#print axioms UniversalV8.variation_piecewise_const
#print axioms UniversalV8.weighted_sum_le_partialSum_mul_dBV
#print axioms UniversalV8.variation_le_two_mul_bound_mul_jumpCount
#print axioms UniversalV8.dBV_le_of_jumpCount
#print axioms Gate1B.SafeAlgebra.routed_weighted_sum_bound

/-! ## Modules D / E / F — synthesis, transport, Schur -/
#print axioms UniversalV8.blockGramIdentity
#print axioms UniversalV8.synthesis_norm_sq
#print axioms UniversalV8.synthesis_norm_le_sum
#print axioms UniversalV8.normalizedSynthesisBound
#print axioms UniversalV8.inner_apply_le_of_apply_norm_le
#print axioms UniversalV8.actualVectorTransport
#print axioms UniversalV8.unweightedSchur
#print axioms UniversalV8.weightedSchur
#print axioms UniversalV8.weightedSchur_needs_symmetry

/-! ## Module G — budgeted synthesis -/
#print axioms UniversalV8.budgetedSynthesis
#print axioms UniversalV8.budgetedSynthesis_closes
#print axioms UniversalV8.budgetedSynthesis_ratio

/-! ## Module H — diagonal baseline -/
#print axioms UniversalV8.gram_expand
#print axioms UniversalV8.gram_eq_diag_add_offdiag
#print axioms UniversalV8.diagOffDiag_budget
#print axioms UniversalV8.diagOffDiag_budget_remaining
#print axioms UniversalV8.quadraticForm_eq_diag_add_offDiag

/-! ## Module I — countermodels -/
#print axioms UniversalV8.identical_packets_have_family_congestion
#print axioms UniversalV8.identical_packets_gap
#print axioms UniversalV8.signs_do_not_force_cancellation
#print axioms UniversalV8.signed_family_can_attain_maximum
#print axioms UniversalV8.dBV_needs_partialSum_bound

/-! ## Module J — defect capacity -/
#print axioms UniversalV8.defectCapacity
#print axioms UniversalV8.pow_card_le_of_pairwiseCoprime_product_dvd
#print axioms UniversalV8.defectCapacity_pow
#print axioms UniversalV8.defectCapacity_log

/-! ## Gate 1A rational exponent ledger -/
#print axioms Gate1A.SafeAlgebra.bp_vertex1_energy
#print axioms Gate1A.SafeAlgebra.bp_vertex1_surplus
#print axioms Gate1A.SafeAlgebra.bp_vertex2_energy
#print axioms Gate1A.SafeAlgebra.bp_vertex2_surplus
#print axioms Gate1A.SafeAlgebra.bp_vertex3_energy
#print axioms Gate1A.SafeAlgebra.bp_vertex3_surplus
#print axioms Gate1A.SafeAlgebra.bp_worst_energy_surplus
#print axioms Gate1A.SafeAlgebra.bp_worstEnergyMargin
#print axioms Gate1A.SafeAlgebra.bp_amplitudeTaxMargin

/-! ## Gate 1B rational exponent / budget ledger -/
#print axioms Gate1B.SafeAlgebra.nearPrimitiveNoWrapExponent
#print axioms Gate1B.SafeAlgebra.diagonal_exponent_identity
#print axioms Gate1B.SafeAlgebra.npl_diagonal_saving_floor
#print axioms Gate1B.SafeAlgebra.npl_diagonal_saving_endpoint
#print axioms Gate1B.SafeAlgebra.X_div_Q_eq_R
#print axioms Gate1B.SafeAlgebra.npl_allowedCongestion
#print axioms Gate1B.SafeAlgebra.sameConductorDiagonal_le
#print axioms Gate1B.SafeAlgebra.sum_le_of_injOn
#print axioms Gate1B.SafeAlgebra.nearPrimitive_diag_energy_bound
#print axioms Gate1B.SafeAlgebra.gate1B_congestionBudget
#print axioms Gate1B.SafeAlgebra.gate1B_congestionBudget_closes

end UniversalV8.Status
