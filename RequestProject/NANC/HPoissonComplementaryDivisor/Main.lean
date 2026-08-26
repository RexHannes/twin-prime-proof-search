import RequestProject.NANC.HPoissonComplementaryDivisor.CRTPhase
import RequestProject.NANC.HPoissonComplementaryDivisor.PoissonCongruenceCore
import RequestProject.NANC.HPoissonComplementaryDivisor.ComplementaryDivisor
import RequestProject.NANC.HPoissonComplementaryDivisor.ExponentGeometry
import RequestProject.NANC.HPoissonComplementaryDivisor.CenteringCore
import RequestProject.NANC.HPoissonComplementaryDivisor.ConditionalExponentLedger

/-!
# HPoissonComplementaryDivisor: aggregate module and axiom audit

This bank contains only finite arithmetic, congruence algebra, divisor
switching, centering identities and rational exponent bookkeeping for the
switched `r = 9`, `4|5` h-Poisson bridge.

No analytic number theory statement is proved or assumed.  The analytic
inputs appear exclusively as the never-inhabited predicates of
`ConditionalExponentLedger`.

The `#print axioms` commands below are audit commands, not declarations.
-/

namespace TwinPrimeProject
namespace HPoissonCD

-- Module 1
#print axioms crt_exists
#print axioms crt_unique
#print axioms crt_existsUnique_mod
#print axioms crt_isCoprime_mul
#print axioms inv_unique
#print axioms inv_congr_inv
#print axioms crt_inverse_decomposition
#print axioms crt_phase_identity

-- Module 2
#print axioms residue_iff_mul
#print axioms crt_split_two
#print axioms residue_iff_split
#print axioms shift_injective
#print axioms shift_surjective

-- Module 3
#print axioms dvd_iff_exists_ell
#print axioms ell_unique
#print axioms existsUnique_ell
#print axioms subst_factor
#print axioms residue_iff_two_ell

-- Module 4
#print axioms expU_add_expV
#print axioms two_expQ_sub_expU
#print axioms two_expQ_add_expH0_add_two_expV
#print axioms expH0_add_expU_add_two_expV
#print axioms composite_exponent_gap
#print axioms expQ_sub_expV
#print axioms expU_add_expV_sub_expQ
#print axioms ellExponent_mem_Icc
#print axioms global_ell_exponent_false

-- Module 5
#print axioms indicator_eq_rho_add
#print axioms rho_mul_coprime
#print axioms centering_ops_pairwise_distinct

-- Module 6
#print axioms TA_target_exponent_arith
#print axioms S4_sq_bound_of_TA_bound_conditional
#print axioms no_unconditional_TA_target

end HPoissonCD
end TwinPrimeProject
