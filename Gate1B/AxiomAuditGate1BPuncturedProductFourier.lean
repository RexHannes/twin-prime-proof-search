import Gate1B.PuncturedFourierFrame
import Gate1B.PrimitiveDeterminantProductPhase
import Gate1B.CurrentStatusGate1BPuncturedProductFourier

/-!
# Gate 1B · axiom audit for the punctured / product-Fourier safe bank

`#print axioms` for every principal declaration added by this delta.  The
expected output for each is a subset of `{propext, Classical.choice,
Quot.sound}`; no new custom axiom is introduced anywhere, and every declaration
is fully proved (zero `sorryAx` in the audit output).
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace AxiomAuditPuncturedProductFourier

open TwinPrimeProject.CurrentProgramme.PuncturedFourier
open TwinPrimeProject.CurrentProgramme.PrimitiveDeterminant
open TwinPrimeProject.CurrentProgramme.LedgerPuncturedProductFourier

/-! ## 1. Punctured Fourier frame -/

#print axioms eM
#print axioms eM_zero
#print axioms eM_add
#print axioms eM_conj
#print axioms full_char_sum
#print axioms nzFreq
#print axioms mem_nzFreq
#print axioms punctured_char_sum
#print axioms puncturedFourier_gram
#print axioms anal
#print axioms synth_anal
#print axioms frame_energy_identity
#print axioms ofReal_sum_normSq
#print axioms frame_energy_real
#print axioms normSq_sum_le_card_mul
#print axioms puncturedFourier_posDef
#print axioms puncturedFourier_posDef_of_two_card_lt
#print axioms puncturedFourier_posDef_strict
#print axioms puncturedFourier_minNorm_coeff_bound
#print axioms puncturedFourier_minNorm_div
#print axioms puncturedFourier_surjective
#print axioms puncturedMatrix
#print axioms onesMatrix
#print axioms puncturedFourier_gram_matrix
#print axioms puncturedFourier_fullRowRank

/-! ## 2. Dilated frame -/

#print axioms dilatedMatrix
#print axioms puncturedFourier_unitDilate_gram
#print axioms puncturedFourier_unitDilate_gram_matrix
#print axioms puncturedFourier_unitDilate_gram_eq
#print axioms puncturedFourier_unitDilate_surjective
#print axioms puncturedFourier_unitDilate_rank

/-! ## 3. Product-Fourier operator -/

#print axioms prodFourier
#print axioms productFourier_orthogonality
#print axioms productFourier_gram
#print axioms productFourier_norm_sq

/-! ## 4. Primitive determinant arithmetic -/

#print axioms doubleGcd_dvd_shift
#print axioms doubleGcd_dvd_shift_gcd
#print axioms primitiveDeterminant_factor
#print axioms primitiveDeterminant_nonzero_of_shift_nonzero
#print axioms sameX_semidiagonal_impossible
#print axioms sameZ_semidiagonal_impossible

/-! ## 5. Product phase factorisation -/

#print axioms determinant_phase_factorization
#print axioms determinant_phase_factorization_int

/-! ## 6. Primitive gcd Möbius identities -/

#print axioms divisors_filter_dvd
#print axioms sum_moebius_divisors
#print axioms coprime_indicator_mobius
#print axioms double_coprime_indicator_mobius

/-! ## 7. Degenerate `M`-divisor router -/

#print axioms prime_dvd_mul_router
#print axioms le_of_dvd_pos
#print axioms prime_dvd_mul_router_ge

/-! ## 8. Original-zero / cyclic-zero firewall -/

#print axioms OriginalDetZero
#print axioms CyclicDetZero
#print axioms originalZero_preserved
#print axioms cyclicZero_not_identified
#print axioms cyclicZero_ne_originalZero
#print axioms puncturedFrame_uses_nonzeroOnly
#print axioms puncturedSynthesis_indep_of_zero_freq

/-! ## 9. Conditional compiler -/

#print axioms conditional_net_compiler

/-! ## 10. Status layer -/

#print axioms researchStatus_never_kernelProved
#print axioms researchStatus_never_closed
#print axioms researchRows_never_kernelProved
#print axioms externally_closed_rows_are_research_only
#print axioms gate1B_research_open
#print axioms no_closed_rows
#print axioms ledger_is_honest
#print axioms gate1B_open
#print axioms first_analytic_residual
#print axioms parallel_local_residual
#print axioms previous_layer_preserved
#print axioms new_exact_rows_kernel_proved
#print axioms not_formalised_rows_open
#print axioms conditional_compiler_row_not_closed

end AxiomAuditPuncturedProductFourier
end CurrentProgramme
end TwinPrimeProject
