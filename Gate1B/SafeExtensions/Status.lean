/-
# Gate 1B safe extensions — status and axiom audit

## PROVED FINITE / ALGEBRAIC (this bank)

* `physicalOuterCauchy`, `gate1B_physicalSecondMomentBudget` — the exact outer
  Cauchy step and the ordered-field second-moment budget implication;
* `rawCentered_eq_mixed_add_unaryD_add_unaryP` — the HFMV finite face lift, with
  the firewall counterexample `mixedFace_ne_raw_without_unary_hypotheses`;
* `ramanujanSum_over_divisors`, `ramanujanProperDivisors_eq_centeredDivisibility`
  — the exact (proper-)divisor Ramanujan identities;
* `pclMixedFace_exact` / `betaMixedFace_to_PCL_exact` — the exact PCL mixed-face
  reindexing, with `squarefree_divisor_coprime_quotient` and
  `moebius_split_squarefree_divisor`;
* `subsetProductSquareSum_eq_eulerProduct`, `pclCoreSquareMass_factorization`,
  `pclCoreSquareMass_finiteBound` — the finite PCL Euler square-mass core;
* `primeCenteredSquareMass_split`, `primeCenteredSquareMass_le` — the
  prime-centered square-mass decomposition and finite bounds;
* `eq_one_or_prime_of_all_primeFactors_gt_sqrt`, `largeUnmatchedFactor_unique`,
  `fufLargeRouter_finite` — the large-unmatched finite structural router;
* `akPhysicalSplice_of_suppliedBound`, `akPhysicalSpliceBudget`,
  `akPhysicalSplice_closes_of_margin` — the abstract physical-splice budget,
  with the AK estimate strictly as a hypothesis;
* `ak_largeCell_spectralTax_le`, `ak_energyOutputExponent`,
  `ak_physicalTargetExponent`, `ak_energyMargin_exact`,
  `ak_amplitudeMargin_exact` — exact ℚ exponent certificates (1/144, 1/288);
* `zeroCoefficient_energy_zero`, `noAutomaticC2LowerMass`,
  `c2Floor_not_formal_from_upperBound` — the retracted-`C₂`-floor guard.

## NOT PROVED ANALYTICALLY (comments-only interfaces; see `AKGMInterfaces.lean`)

GM Theorem 1.1; AK-GM-X012 interface; typed integrated AK self-kernel; the
`X^{o(1)}` PCL mass; the actual `X^{-1/144}` analytic estimate; BV4 / BV5;
Mertens / Vinogradov–Korobov; `E(q)`, `Z_E(q)`, `kappa4`; source face
completeness; Gate 1B closure.  **Gate 1B remains OPEN.**
-/
import Gate1B.SafeExtensions.SourceWeightCollapse
import Gate1B.SafeExtensions.PrimitiveConductorRouter
import Gate1B.SafeExtensions.NearPrimitiveDiagonal
import Gate1B.SafeExtensions.Budget
import Gate1B.SafeExtensions.Interfaces
import Gate1B.SafeExtensions.PhysicalSecondMoment
import Gate1B.SafeExtensions.MixedFaceScope
import Gate1B.SafeExtensions.PCLMixedFace
import Gate1B.SafeExtensions.PCLSquareMass
import Gate1B.SafeExtensions.PrimeCenteredSquareMass
import Gate1B.SafeExtensions.LargeUnmatchedRouter
import Gate1B.SafeExtensions.AKPhysicalBudget
import Gate1B.SafeExtensions.C2FloorGuard
import Gate1B.SafeExtensions.AKGMInterfaces
import Gate1B.SafeAlgebra.AKPhysicalExponentRepair
import Universal.SafeAlgebra.Homogeneity

namespace Gate1B.SafeExtensions.Status

-- previously banked
#print axioms Gate1B.SafeExtensions.squarefree_moebius_remove_prime
#print axioms Gate1B.SafeExtensions.fixedQ_weightedSignCollapse
#print axioms Gate1B.SafeExtensions.squarefree_hypothesis_load_bearing
#print axioms Gate1B.SafeExtensions.primitiveConductorTrichotomy
#print axioms Gate1B.SafeExtensions.primitiveConductor_cases_disjoint
#print axioms Gate1B.SafeExtensions.nearPrimitive_diag_energy_bound_restricted
#print axioms Gate1B.SafeExtensions.nearPrimitive_needs_injectivity
#print axioms Gate1B.SafeExtensions.gate1B_sufficient_congestion

-- universal homogeneity module
#print axioms Universal.SafeAlgebra.quadraticEnergy_smul
#print axioms Universal.SafeAlgebra.sesquilinear_same_smul
#print axioms Universal.SafeAlgebra.finiteSesquilinearForm_smul
#print axioms Universal.SafeAlgebra.zeroEnergy_counterexample
#print axioms Universal.SafeAlgebra.noPositiveUniformEnergyFloor
#print axioms Universal.SafeAlgebra.upperBound_does_not_give_lowerBound

-- physical outer Cauchy
#print axioms Gate1B.SafeExtensions.physicalOuterCauchy
#print axioms Gate1B.SafeExtensions.gate1B_outerCauchy
#print axioms Gate1B.SafeExtensions.physicalSecondMoment_imp_amplitude
#print axioms Gate1B.SafeExtensions.gate1B_physicalSecondMomentBudget

-- HFMV mixed-face scope guard
#print axioms Gate1B.SafeExtensions.weightedCenteredFaceDecomposition
#print axioms Gate1B.SafeExtensions.rawCentered_eq_mixed_add_unaryD_add_unaryP
#print axioms Gate1B.SafeExtensions.mixedFace_ne_raw_without_unary_hypotheses

-- exact Ramanujan / PCL mixed face
#print axioms Gate1B.SafeExtensions.ramanujanSum_over_divisors
#print axioms Gate1B.SafeExtensions.ramanujanSum_one
#print axioms Gate1B.SafeExtensions.ramanujanProperDivisors_eq_centeredDivisibility
#print axioms Gate1B.SafeExtensions.rho_eq_ramanujan_average
#print axioms Gate1B.SafeExtensions.squarefree_divisor_coprime_quotient
#print axioms Gate1B.SafeExtensions.moebius_split_squarefree_divisor
#print axioms Gate1B.SafeExtensions.pclPairs_support
#print axioms Gate1B.SafeExtensions.sum_antidiagonal_filter_gt_one
#print axioms Gate1B.SafeExtensions.sum_pclPairs
#print axioms Gate1B.SafeExtensions.pclMixedFace_exact
#print axioms Gate1B.SafeExtensions.betaMixedFace_to_PCL_exact

-- finite PCL square mass
#print axioms Gate1B.SafeExtensions.subsetProductSquareSum_eq_eulerProduct
#print axioms Gate1B.SafeExtensions.pclCoreSquareMass_factorization
#print axioms Gate1B.SafeExtensions.pclCoreSquareMass_finiteBound

-- prime-centered square mass
#print axioms Gate1B.SafeExtensions.primeCenteredSquareMass_split
#print axioms Gate1B.SafeExtensions.primeCenteredSquareMass_le

-- large unmatched router
#print axioms Gate1B.SafeExtensions.eq_one_or_prime_of_all_primeFactors_gt_sqrt
#print axioms Gate1B.SafeExtensions.largeUnmatchedFactor_unique
#print axioms Gate1B.SafeExtensions.fufLargeRouter_finite

-- physical splice budget
#print axioms Gate1B.SafeExtensions.akPhysicalSplice_of_suppliedBound
#print axioms Gate1B.SafeExtensions.akPhysicalSpliceBudget
#print axioms Gate1B.SafeExtensions.akPhysicalSplice_closes_of_margin

-- rational exponent ledger
#print axioms Gate1B.SafeAlgebra.ak_UV_exponent_sum
#print axioms Gate1B.SafeAlgebra.ak_largeCell_spectralTax_le
#print axioms Gate1B.SafeAlgebra.ak_energyOutputExponent
#print axioms Gate1B.SafeAlgebra.ak_physicalTargetExponent
#print axioms Gate1B.SafeAlgebra.ak_energyMargin_exact
#print axioms Gate1B.SafeAlgebra.ak_amplitudeMargin_exact
#print axioms Gate1B.SafeAlgebra.ak_exponentLedger

-- C₂ floor retraction guard
#print axioms Gate1B.SafeExtensions.zeroCoefficient_energy_zero
#print axioms Gate1B.SafeExtensions.noAutomaticC2LowerMass
#print axioms Gate1B.SafeExtensions.c2Floor_not_formal_from_upperBound

end Gate1B.SafeExtensions.Status
