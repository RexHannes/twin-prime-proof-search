/-
# NANC Gate 1A v9.1 — status ledger and axiom audit

    ROOT_MULTIPLIER_ALGEBRA:           proved (finite, ZMod, explicit units)
    ROOT_MULTIPLIER_MOD_CLEAN_FACTOR:  proved (u independent of q1)
    HARD_DELTA_UNIT_ROUTER:            proved (finite arithmetic)
    WEIGHTED_ROOT_ANALYSIS_ENERGY:     proved (finite Cauchy, fibre mass)
    WEIGHTED_ROOT_FIBRE_RESIDUEMASS:   proved (alpha summed on both sides)
    NONUNIT_FIREWALL:                  countermodel proved
    DEFECT_OP_CHARACTER_EIGEN:         proved (finite Fourier diagonalisation)
    DEFECT_OP_ENERGY_LE_FOURIERSUP:    proved
    NO_RAW_FEJER_L1:                   countermodel proved
    ROOTDEFECT_BILINEAR_BOUND:         proved (finite Cauchy)
    ROOTDEFECT-SOURCE-FACTOR1A:        INTERFACE OPEN / NO INHABITANT
    PROJECTIVE_CROSSED_CONVOLUTION:    proved (+ fibre-card corollary)
    ZERO-PROJ-SOURCE-SPLICE1A:         INTERFACE OPEN / NO INHABITANT
    GATE1A_DIRECT_CLEAN_P3:            OPEN
    FULL_TYPE_II:                      NOT DECLARED
    TWIN_PRIMES:                       NOT DECLARED

The `#print axioms` calls below are the axiom audit: only `propext`,
`Classical.choice` and `Quot.sound` may appear.
-/
import RequestProject.NANC.Gate1A.SafeExtensions.RootMultiplier
import RequestProject.NANC.Gate1A.SafeExtensions.WeightedRootDefect
import RequestProject.NANC.Gate1A.SafeExtensions.DefectMultiplier
import RequestProject.NANC.Gate1A.SafeExtensions.RootDefectFactor
import RequestProject.NANC.Gate1A.SafeExtensions.ProjectiveSourceInterfaces

namespace TwinPrimeProject.NANC.Gate1A.V91

#print axioms rootMultiplier_rewrite
#print axioms rootMultiplier_mod_cleanFactor
#print axioms rootMultiplierU_indep_q1
#print axioms hardDelta_isUnit_mod_cleanPrime
#print axioms rootMultiplierU_isUnit_mod_cleanPrime
#print axioms weightedRootAnalysis_energy
#print axioms weightedRootAnalysis_of_fibreBound
#print axioms weightedRootFibre_of_residueMass
#print axioms nonunitMultiplier_collapses_rootFibre
#print axioms defectOp_character_eigen
#print axioms defectOp_energy_le_fourierSup
#print axioms defectOp_of_multiplierBound
#print axioms defectOp_l1_mass_not_canonical
#print axioms rootDefect_bilinear_bound
#print axioms RootDefectSourceFactorization.bound
#print axioms projectiveCrossedConvolution
#print axioms projectiveCrossedConvolution_of_fibreCard
#print axioms ZeroProjectiveSourceFactorization.bound

end TwinPrimeProject.NANC.Gate1A.V91
