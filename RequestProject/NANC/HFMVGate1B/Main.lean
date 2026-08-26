import RequestProject.NANC.HFMVGate1B.HFMVComplementaryDivisor
import RequestProject.NANC.HFMVGate1B.HFMVDeterminant
import RequestProject.NANC.HFMVGate1B.HFMVDiagonal
import RequestProject.NANC.HFMVGate1B.HFMVExponentLedger
import RequestProject.NANC.HFMVGate1B.B1DeterminantEnergy
import RequestProject.NANC.HFMVGate1B.HFMVAnalyticInterfaces

/-!
# HFMV Gate 1B: aggregation and axiom audit

This module aggregates the source-native HFMV determinant bank and runs
`#print axioms` on every main finite theorem.

Proved finite (this bank):
* complementary-divisor equivalence and uniqueness of `l`;
* the determinant identity and its converse;
* the diagonal identity and the exact finite tuple-diagonal decomposition;
* the rational exponent ledger;
* the B1 determinant multiplicity-one lemma and the finite energy inequality.

Not proved anywhere: GSDV, Gate 1B, full Type II, twin primes.
-/

namespace TwinPrimeProject
namespace HFMVGate1B

section Audit

#print axioms dvd_iff_exists_ell
#print axioms dvd_iff_exists_incidence
#print axioms ell_unique
#print axioms existsUnique_ell
#print axioms ell_pos
#print axioms ell_range

#print axioms det_identity
#print axioms det_identity_centered
#print axioms det_converse_abstract
#print axioms det_converse

#print axioms diagonal_prod_eq
#print axioms diagonal_prod_eq'
#print axioms diagonal_v_eq
#print axioms diagonalPairs_eq_prodPairs
#print axioms diagonalPairs_card
#print axioms diagonalPairs_card_le
#print axioms diagonalPairs_card_eq_sq_of_constant_v

#print axioms expU_add_expV
#print axioms expUV_sub_expQ
#print axioms two_expQ_sub_two_expV
#print axioms rpow_UV_div_Q
#print axioms rpow_Qsq_div_Vsq

#print axioms b1_multiplicity_one
#print axioms b1_key_injOn
#print axioms b1Alpha_single
#print axioms b1_energy

#print axioms hfmv_bound_of_interfaces

end Audit

end HFMVGate1B
end TwinPrimeProject
