/-
# Gate 1B v12 — moving-multiplier exact bank: status and axiom audit

Imports every v12 moving-multiplier module and prints the axioms of every
principal declaration.  V10, V11 and all earlier banks are untouched; v12 is
append-only.

Scope of the v12 moving-multiplier bank:

* the exact Kloosterman multiplicative-character diagonalisation and the
  moving-multiplier bilinear expansion;
* the exact moving-`a` second moment (unit and all-residue forms);
* the no-wrap product-energy fibre bound;
* the ℓ² family-lift counterguard (duality attained);
* the additive Θ-Fourier transform of the moving Kloosterman family
  (COORDINATE TRANSFORM ONLY) with finite Plancherel;
* the conditional CRT source Fourier factorisation;
* the conditional multiplicative source-character factorisation and Parseval;
* the four-cycle trace / determinant / discriminant and the fixed-`a`
  regression;
* the four-multiplier and character-alignment counterguards;
* the QK source-character covariance data with UNINHABITED bound;
* the weighted multiplicative energy with UNINHABITED bound;
* the physical four-multiplier source with UNINHABITED moment bound;
* the prior-ledger compatibility record (data only);
* the conditional compilers and the V10 four-leaf bridge.

NOT claimed anywhere: any asymptotic estimate, a `p^{o(1)}` bound on the
product residue energy, a moving-multiplier power saving, QK56 or SHIFT-MULT4
analytic closure, Gate 1B closure, Ford–Maynard, or twin primes.
-/
import Gate1B.SafeAlgebra.MovingMultiplierPrime
import Gate1B.SafeAlgebra.MovingMultiplierSecondMoment
import Gate1B.SafeAlgebra.NoWrapProductEnergy
import Gate1B.SafeAlgebra.MovingMultiplierCounterguard
import Gate1B.SafeAlgebra.KloostermanMultiplierFourier
import Gate1B.SafeAlgebra.ThetaSourceFourierFactor
import Gate1B.SafeAlgebra.ThetaSourceMulCharacter
import Gate1B.SafeAlgebra.MovingMultiplierFourCycle
import Gate1B.SafeAlgebra.FourMultiplierCounterguards
import Gate1B.SafeAlgebra.CharacterAlignmentCounterguard
import Gate1B.SafeExtensions.QKSourceCharacterCovariance
import Gate1B.SafeExtensions.WeightedMultiplicativeEnergyInterface
import Gate1B.SafeExtensions.ShiftMultiplierSource
import Gate1B.SafeExtensions.MovingMultiplierLedgerStatus
import Gate1B.SafeExtensions.MovingMultiplierConditionalCompilers

namespace Gate1B.SafeExtensions.V12Audit

-- prime character expansion / moving-multiplier bilinear expansion
#print axioms Gate1B.SafeAlgebra.kloosterman_character_expand
#print axioms Gate1B.SafeAlgebra.movingMultiplier_bilinear_expand
#print axioms Gate1B.SafeAlgebra.movingMultiplier_bilinear_expand'

-- exact moving-`a` second moment
#print axioms Gate1B.SafeAlgebra.movingMultiplier_second_moment_units
#print axioms Gate1B.SafeAlgebra.movingMultiplier_second_moment_all
#print axioms Gate1B.SafeAlgebra.sum_hat_sq_eq_card_mul_energy

-- no-wrap product energy
#print axioms Gate1B.SafeAlgebra.congruence_eq_of_noWrap
#print axioms Gate1B.SafeAlgebra.productResidueEnergy_le_fibre_mul

-- ℓ² family-lift counterguard
#print axioms Gate1B.SafeAlgebra.movingFamily_l2_duality
#print axioms Gate1B.SafeAlgebra.fixedMultiplierSaving_not_familyLift_by_l2_alone

-- additive Θ-Fourier (coordinate transform only)
#print axioms Gate1B.SafeAlgebra.AdditiveCharacterSystem.add_plancherel
#print axioms Gate1B.SafeAlgebra.AdditiveCharacterSystem.kloosterman_theta_fourier_unit
#print axioms Gate1B.SafeAlgebra.AdditiveCharacterSystem.kloosterman_theta_fourier_nonunit
#print axioms Gate1B.SafeAlgebra.AdditiveCharacterSystem.kloosterman_theta_square_mass
#print axioms Gate1B.SafeAlgebra.AdditiveCharacterSystem.thetaFourier_is_coordinate_change

-- CRT source Fourier factorisation (conditional)
#print axioms Gate1B.SafeAlgebra.crt_source_fourier_factor
#print axioms Gate1B.SafeAlgebra.crt_source_fourier_factor_modulus

-- multiplicative source-character factorisation and Parseval
#print axioms Gate1B.SafeAlgebra.MulCharSystem.rankOne_source_character_factor
#print axioms Gate1B.SafeAlgebra.MulCharSystem.rankOne_source_character_factor_modulus
#print axioms Gate1B.SafeAlgebra.MulCharSystem.character_parseval_totient

-- four-cycle algebra
#print axioms Gate1B.SafeAlgebra.fourCycle_trace
#print axioms Gate1B.SafeAlgebra.fourCycle_det
#print axioms Gate1B.SafeAlgebra.fixedPoint_quadratic_disc
#print axioms Gate1B.SafeAlgebra.fourCycle_disc_eq
#print axioms Gate1B.SafeAlgebra.fourCycle_trace_fixed_multiplier
#print axioms Gate1B.SafeAlgebra.fourCycle_disc_fixed_multiplier
#print axioms Gate1B.SafeAlgebra.fourCycle_trace_depends_on_multipliers

-- counterguards
#print axioms Gate1B.SafeAlgebra.fourCopies_ne_fourIndependentParameters
#print axioms Gate1B.SafeAlgebra.rankOneRestriction_changes_moment
#print axioms Gate1B.SafeAlgebra.MulCharSystem.commonCharacterAlignment_saturates_genericMoment
#print axioms Gate1B.SafeAlgebra.MulCharSystem.alignedMode_carries_all_parseval_mass

-- interfaces (uninhabited) and their non-vacuity guards
#print axioms Gate1B.SafeExtensions.qkSourceCharacterCovarianceBound_not_vacuous
#print axioms Gate1B.SafeExtensions.weightedMultiplicativeEnergyInput_not_vacuous
#print axioms Gate1B.SafeExtensions.shiftMult4CharacterBound_not_vacuous
#print axioms Gate1B.SafeExtensions.QKSourceCharacterCovarianceData.qkCovariance_sector_split
#print axioms Gate1B.SafeExtensions.QKSourceCharacterCovarianceData.qkCovariance_norm_le
#print axioms Gate1B.SafeExtensions.productResidueEnergy_eq_of_second_moment

-- ledger record
#print axioms Gate1B.SafeExtensions.no_prior_claim_handles_movingMultiplier
#print axioms Gate1B.SafeExtensions.no_prior_claim_handles_crossCharacter

-- conditional compilers and the V10 bridge
#print axioms Gate1B.SafeExtensions.qkCovarianceBound_to_shiftedQuotientParent
#print axioms Gate1B.SafeExtensions.qkCovarianceBound_to_qk56FullCovariance
#print axioms Gate1B.SafeExtensions.shiftMult4Bound_to_shiftedQuotientParent
#print axioms Gate1B.SafeExtensions.v12_to_v10AnalyticLeaves
#print axioms Gate1B.SafeExtensions.v12LeafBundle_not_automatic

end Gate1B.SafeExtensions.V12Audit
