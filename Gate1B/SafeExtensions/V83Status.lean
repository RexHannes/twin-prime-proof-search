/-
# Gate 1B v8.3 — status and axiom audit

Imports every v8.3 module and prints the axioms of each principal declaration.
Nothing here restates, weakens or replaces the v8.1 / v8.2 banks, which are
untouched.

Scope of v8.3 (all of it finite / algebraic or explicitly hypothesis-carrying):

* general high-order regroup exponent geometry and the generic shell regroup;
* H6 / H7 / H8 / H9 exact shells and congruences;
* finite-fibre pushforward energy and the H6 / H7 source-energy compiler;
* a generic finite multiplicative character system with inversion and Parseval;
* the reciprocal additive-phase character expansion (fixed shift `2`);
* the H7 / H8 packet factorisations and the H9 nonprincipal character packet;
* the exact same-`q` character expansion and double character Gram, plus the
  countermodel showing it is not a function of residue energy;
* the finite bulk/spike interpolation inequalities and the D₁₂ capacity
  bookkeeping (CAPACITY_ONLY);
* the Tier-3 zero-mode residual algebra and its no-go countermodel;
* the high-order routing table and the v8.3 firewall countermodels.

NOT claimed anywhere: any H7 / H8 / H9 / same-`q` / D₁₂ analytic estimate,
Siegel–Walfisz, Pólya–Vinogradov, the multiplicative large sieve, Pascadi
Theorem 7.1, `R_E` source bounds, Gate 1B closure, Full Type II, twin primes.
-/
import Gate1B.SafeAlgebra.HighOrderRegroupGeometry
import Gate1B.SafeAlgebra.HighOrderShellRegroup
import Gate1B.SafeAlgebra.H6Regroup
import Gate1B.SafeAlgebra.H7Regroup
import Gate1B.SafeAlgebra.H7Reciprocal1D
import Gate1B.SafeAlgebra.H8Reciprocal1D
import Gate1B.SafeAlgebra.H9PureDefect
import Gate1B.SafeAlgebra.FiniteMultiplicativeCharacters
import Gate1B.SafeAlgebra.ReciprocalCharacterExpansion
import Gate1B.SafeAlgebra.H78CharacterPacket
import Gate1B.SafeAlgebra.H9CharacterPacket
import Gate1B.SafeAlgebra.SameQCharacterGram
import Gate1B.SafeAlgebra.SameQCountermodel
import Gate1B.SafeAlgebra.D12BulkSpikeCapacity
import Gate1B.SafeAlgebra.CountermodelsV83
import Gate1B.SafeExtensions.HighOrderSourceEnergy
import Gate1B.SafeExtensions.SameQNineFactorInterface
import Gate1B.SafeExtensions.HighOrderRoutingStatus
import Gate1B.SafeExtensions.V83ZeroModeResidual
import Gate1B.SafeExtensions.V83HighOrderInterfaces
import Universal.SafeAlgebra.ProductEnergyFiniteFiber
import Universal.SafeAlgebra.BulkSpikeInterpolation

namespace Gate1B.SafeExtensions.V83

/-! ## Axiom audit of the v8.3 additions -/

section HighOrderGeometry

#print axioms Gate1B.SafeAlgebra.hasTwoModels_of_order_le_seven
#print axioms Gate1B.SafeAlgebra.regroupBExponent_eq_seven
#print axioms Gate1B.SafeAlgebra.regroup_order_five
#print axioms Gate1B.SafeAlgebra.regroup_order_six
#print axioms Gate1B.SafeAlgebra.regroup_order_seven
#print axioms Gate1B.SafeAlgebra.orderEight_oneModel
#print axioms Gate1B.SafeAlgebra.orderNine_noModel
#print axioms Gate1B.SafeAlgebra.defects_add_models

end HighOrderGeometry

section Shells

#print axioms Gate1B.SafeAlgebra.shell_regroup_twoModels
#print axioms Gate1B.SafeAlgebra.shell_regroup_coeff_eq
#print axioms Gate1B.SafeAlgebra.shell_regroup_order5
#print axioms Gate1B.SafeAlgebra.shell_regroup_order6
#print axioms Gate1B.SafeAlgebra.h6_shell_regroup
#print axioms Gate1B.SafeAlgebra.h6_congruence
#print axioms Gate1B.SafeAlgebra.h6_congruence_modEq
#print axioms Gate1B.SafeAlgebra.h6_ell_unique
#print axioms Gate1B.SafeAlgebra.h6_ell_value
#print axioms Gate1B.SafeAlgebra.h7_qk5_shell
#print axioms Gate1B.SafeAlgebra.h7_qk5_congruence
#print axioms Gate1B.SafeAlgebra.h7_rf1d_shell
#print axioms Gate1B.SafeAlgebra.h7_rf1d_congruence
#print axioms Gate1B.SafeAlgebra.h7_rf1d_ell_unique
#print axioms Gate1B.SafeAlgebra.h8_rf1d_shell
#print axioms Gate1B.SafeAlgebra.h8_rf1d_congruence
#print axioms Gate1B.SafeAlgebra.h9_shell
#print axioms Gate1B.SafeAlgebra.h9_shell_congruence
#print axioms Gate1B.SafeAlgebra.h9_qell_coprime
#print axioms Gate1B.SafeAlgebra.h9_qell_coprime_shell

end Shells

section Energy

#print axioms Universal.SafeAlgebra.l2_pushforward_le_fiber_card_mul
#print axioms Universal.SafeAlgebra.l2_pushforward_le_uniform_fiber
#print axioms Universal.SafeAlgebra.l2_pushforward_product_le
#print axioms Gate1B.SafeExtensions.pair_tensor_energy
#print axioms Gate1B.SafeExtensions.h6Energy_of_fiberBound
#print axioms Gate1B.SafeExtensions.h7Energy_exact

end Energy

section Characters

#print axioms Gate1B.SafeAlgebra.MulCharSystem.chi_one
#print axioms Gate1B.SafeAlgebra.MulCharSystem.chi_inv
#print axioms Gate1B.SafeAlgebra.MulCharSystem.character_fourier_inversion
#print axioms Gate1B.SafeAlgebra.MulCharSystem.character_fourier_inversion'
#print axioms Gate1B.SafeAlgebra.MulCharSystem.character_parseval
#print axioms Gate1B.SafeAlgebra.gauss_twist
#print axioms Gate1B.SafeAlgebra.reciprocal_addChar_fourier
#print axioms Gate1B.SafeAlgebra.reciprocal_phase_character_expand
#print axioms Gate1B.SafeAlgebra.reciprocal_phase_expand_shift_two
#print axioms Gate1B.SafeAlgebra.h7_characterPacket_factor
#print axioms Gate1B.SafeAlgebra.h8_characterPacket_factor
#print axioms Gate1B.SafeAlgebra.MulCharSystem.unit_residue_indicator_character_expand
#print axioms Gate1B.SafeAlgebra.MulCharSystem.h9_nonprincipal_character_packet
#print axioms Gate1B.SafeAlgebra.MulCharSystem.h9_packet_of_factorisation

end Characters

section SameQ

#print axioms Gate1B.SafeAlgebra.kloostermanCharSum_eq
#print axioms Gate1B.SafeAlgebra.sameQ_character_expand
#print axioms Gate1B.SafeAlgebra.sameQ_gram_expand
#print axioms Gate1B.SafeAlgebra.sameQ_gram_eq_gramForm
#print axioms Gate1B.SafeAlgebra.sameQ_not_function_of_residueEnergy
#print axioms Gate1B.SafeAlgebra.sameQ_ne_residueEnergy_counterexample
#print axioms Gate1B.SafeExtensions.SameQNineFactorData.sameQ_of_nuclear_factorisation

end SameQ

section BulkSpike

#print axioms Universal.SafeAlgebra.bulk_bound
#print axioms Universal.SafeAlgebra.spike_l1_bound
#print axioms Universal.SafeAlgebra.spike_weighted_bound
#print axioms Universal.SafeAlgebra.spike_card_l1_bound
#print axioms Universal.SafeAlgebra.spike_l2_card_bound
#print axioms Universal.SafeAlgebra.bulkSpike_bound
#print axioms Gate1B.SafeAlgebra.d12_rms_exponent
#print axioms Gate1B.SafeAlgebra.d12_sup_over_rms_exponent
#print axioms Gate1B.SafeAlgebra.d12_bulkSpike_loss_exponent
#print axioms Gate1B.SafeAlgebra.bulkSpike_balance_exponent

end BulkSpike

section ZeroModeAndStatus

#print axioms Gate1B.SafeExtensions.historical_eq_canonical_sub_residual
#print axioms Gate1B.SafeExtensions.expectedTerm_not_freely_choosable
#print axioms Gate1B.SafeExtensions.RE_eq_zero_of_eq
#print axioms Gate1B.SafeExtensions.highOrderStatus_geometry_banked
#print axioms Gate1B.SafeExtensions.highOrderStatus_analytic_open

end ZeroModeAndStatus

section Countermodels

#print axioms Gate1B.SafeAlgebra.countermodel_A_regroup_not_unique
#print axioms Gate1B.SafeAlgebra.countermodel_B_sameQ_gram
#print axioms Gate1B.SafeAlgebra.countermodel_C_bulkSpike_worse_than_l2
#print axioms Gate1B.SafeAlgebra.countermodel_D_zeroMode_residual

end Countermodels

end Gate1B.SafeExtensions.V83
