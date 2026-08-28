/-
# Gate 1B v8.4 — status and axiom audit

Imports every v8.4 module and prints the axioms of each principal declaration.
The v8.1 / v8.2 / v8.3 banks are untouched; v8.4 is append-only.

Scope of v8.4 (finite / algebraic, or explicitly hypothesis-carrying):

* the RF1D conductor state-count repair and threshold capacity bookkeeping;
* lane-E emptiness (exponent part + finite divisibility part);
* the clean prime split `c = p c₀` and the lane-C `β` factorisation;
* the induced Gauss factor and the exact `μ(e)` cancellation;
* the prime-conductor CRT character/Gauss factorisation;
* the prime-character collapse and its normalised form;
* the hybrid `h`-Poisson finite residue transform and the conditional compiler;
* truncated dual-frequency uniqueness (the repair of the "single frequency"
  overstatement);
* the H7 dual congruence, dual determinant shell and full-divisor self-duality;
* large-prime divisor capacity and the dyadic harmonic fibre;
* the H7 dual-determinant capacity bookkeeping (CAPACITY_ONLY);
* the no-log promotion firewall and the v8.4 countermodels.

NOT claimed anywhere: the RF1D analytic theorem, any H7 / H8 / H9 / same-`q` /
D₁₂ analytic estimate, arbitrary-log savings, Siegel–Walfisz, Pólya–Vinogradov,
the multiplicative large sieve, `R_E` bounds, Gate 1B closure, Full Type II,
twin primes.
-/
import Gate1B.SafeAlgebra.RF1DConductorStateCount
import Gate1B.SafeAlgebra.RF1DHighConductorCapacity
import Gate1B.SafeAlgebra.LaneEEmpty
import Gate1B.SafeAlgebra.BetaCEPrimeSplit
import Gate1B.SafeAlgebra.InducedGaussFactor
import Gate1B.SafeAlgebra.InducedMuCancellation
import Gate1B.SafeAlgebra.PrimeConductorCRT
import Gate1B.SafeAlgebra.PrimeCharacterCollapse
import Gate1B.SafeAlgebra.PrimeCharacterCollapseNormalized
import Gate1B.SafeAlgebra.HybridHPoissonResidue
import Gate1B.SafeAlgebra.DualResidueUniqueness
import Gate1B.SafeAlgebra.H7DualCongruence
import Gate1B.SafeAlgebra.PrimitiveCharacterProjector
import Gate1B.SafeAlgebra.PrimitiveProjectorMu
import Gate1B.SafeAlgebra.MuSpentByProjector
import Gate1B.SafeAlgebra.H7DualDeterminant
import Gate1B.SafeAlgebra.H7SelfDuality
import Gate1B.SafeAlgebra.H7DualDetCapacity
import Gate1B.SafeAlgebra.CountermodelsV84
import Gate1B.SafeExtensions.HybridHPoisson
import Gate1B.SafeExtensions.H7LogClosureFirewall
import Gate1B.SafeExtensions.H7DualDetInterface
import Gate1B.SafeExtensions.V84ResourceLedger
import Gate1B.SafeExtensions.V84PrimeConductorInterfaces
import Universal.SafeAlgebra.LargePrimeDivisorCount
import Universal.SafeAlgebra.DyadicHarmonic

namespace Gate1B.SafeExtensions.V84

/-! ## RF1D -/

#print axioms Gate1B.SafeAlgebra.conductorStateCount_capacity
#print axioms Gate1B.SafeAlgebra.conductorStateCount_factors
#print axioms Gate1B.SafeAlgebra.betaCharacterStateExponent
#print axioms Gate1B.SafeAlgebra.conductorStateCount_ne_cofactorCount
#print axioms Gate1B.SafeAlgebra.rf1d_transition_exponent
#print axioms Gate1B.SafeAlgebra.rf1d_belowTransition_margin
#print axioms Gate1B.SafeAlgebra.rf1d_aboveTransition_nonneg
#print axioms Gate1B.SafeAlgebra.rf1d_capacity_transfer

/-! ## Lane E -/

#print axioms Gate1B.SafeAlgebra.VExponent_gt_two
#print axioms Gate1B.SafeAlgebra.V_gt_Ysq
#print axioms Gate1B.SafeAlgebra.laneE_prime_not_dvd_e
#print axioms Gate1B.SafeAlgebra.laneE_empty
#print axioms Gate1B.SafeAlgebra.laneE_empty_setOf

/-! ## Lane C: prime split and β -/

#print axioms Gate1B.SafeAlgebra.prime_dvd_conductor
#print axioms Gate1B.SafeAlgebra.complement_eq
#print axioms Gate1B.SafeAlgebra.moebius_complement
#print axioms Gate1B.SafeAlgebra.betaCE_laneC_factor

/-! ## Induced Gauss factor and μ(e) cancellation -/

#print axioms Gate1B.SafeAlgebra.gaussShift_unit
#print axioms Gate1B.SafeAlgebra.gaussSum_eq_abstract
#print axioms Gate1B.SafeAlgebra.induced_gauss_squarefree
#print axioms Gate1B.SafeAlgebra.beta_mul_inducedGauss_cancel_muE
#print axioms Gate1B.SafeAlgebra.betaSource_mul_inducedGauss_cancel_muE

/-! ## Prime CRT characters -/

#print axioms Gate1B.SafeAlgebra.primeConductor_char_equiv
#print axioms Gate1B.SafeAlgebra.crt_gauss_factor
#print axioms Gate1B.SafeAlgebra.primeConductor_gauss_factor

/-! ## Prime-character collapse -/

#print axioms Gate1B.SafeAlgebra.allChars_gauss_collapse
#print axioms Gate1B.SafeAlgebra.principal_gauss_eq_neg_one
#print axioms Gate1B.SafeAlgebra.nonprincipal_gauss_collapse
#print axioms Gate1B.SafeAlgebra.nonprincipal_gauss_collapse_normalized
#print axioms Gate1B.SafeAlgebra.normalized_collapse_correction_isolated

/-! ## Hybrid h-Poisson -/

#print axioms Gate1B.SafeAlgebra.residue_condition
#print axioms Gate1B.SafeAlgebra.hybridResidueTransform
#print axioms Gate1B.SafeAlgebra.hybridResidue_congruence
#print axioms Gate1B.SafeExtensions.hybrid_hPoisson_conditional

/-! ## Dual window uniqueness -/

#print axioms Gate1B.SafeAlgebra.residueClass_inter_interval_card_le_one
#print axioms Gate1B.SafeAlgebra.residueClass_inter_interval_subsingleton
#print axioms Gate1B.SafeAlgebra.truncatedDual_frequency_unique

/-! ## Primitive projector -/

#print axioms Gate1B.SafeAlgebra.primitiveChar_sum_squarefree
#print axioms Gate1B.SafeAlgebra.mu_mul_quotient_mu
#print axioms Gate1B.SafeAlgebra.mu_weighted_primitiveProjector
#print axioms Gate1B.SafeAlgebra.generic_common_divisor_eq_one
#print axioms Gate1B.SafeAlgebra.generic_filter_eq_singleton
#print axioms Gate1B.SafeAlgebra.primitiveProjector_generic_eq_inv

/-! ## Dual determinant and self-duality -/

#print axioms Gate1B.SafeAlgebra.h7_dual_prime_congruence
#print axioms Gate1B.SafeAlgebra.h7_dual_prime_congruence_zmod
#print axioms Gate1B.SafeAlgebra.pd_dvd_dualDet
#print axioms Gate1B.SafeAlgebra.h7_dualDet_shell
#print axioms Gate1B.SafeAlgebra.h7_dualDet_shell_of_congruences
#print axioms Gate1B.SafeAlgebra.h7_fullDivisor_dualShell
#print axioms Gate1B.SafeAlgebra.h7_selfDual_shellShape
#print axioms Gate1B.SafeAlgebra.h7_fullDivisor_reconstructs_H7shape

/-! ## Capacity -/

#print axioms Universal.SafeAlgebra.largePrime_pow_card_le
#print axioms Universal.SafeAlgebra.largePrime_card_lt
#print axioms Universal.SafeAlgebra.largePrime_capacity_bound
#print axioms Universal.SafeAlgebra.dyadic_harmonic_le_two
#print axioms Universal.SafeAlgebra.dyadic_totient_fibre_le
#print axioms Gate1B.SafeAlgebra.h7Deficit_at_13_18
#print axioms Gate1B.SafeAlgebra.h7Deficit_at_8_9
#print axioms Gate1B.SafeAlgebra.h7_dualDet_naturalScaleExponent
#print axioms Gate1B.SafeAlgebra.h7_fixedPower_deficit_recovered
#print axioms Gate1B.SafeAlgebra.h7_recovered_exponent_not_negative

/-! ## Firewalls and countermodels -/

#print axioms Gate1B.SafeExtensions.no_log_saving_from_natural_scale
#print axioms Gate1B.SafeAlgebra.countermodelA_summable
#print axioms Gate1B.SafeAlgebra.countermodelA_support_infinite
#print axioms Gate1B.SafeAlgebra.countermodelB_natural_scale_insufficient
#print axioms Gate1B.SafeAlgebra.countermodelB_exponent_zero
#print axioms Gate1B.SafeAlgebra.countermodelC_mu_cancels
#print axioms Gate1B.SafeAlgebra.countermodelC_concrete
#print axioms Gate1B.SafeAlgebra.countermodelD_shell_not_size
#print axioms Gate1B.SafeAlgebra.countermodelD_weights_unbounded

end Gate1B.SafeExtensions.V84
