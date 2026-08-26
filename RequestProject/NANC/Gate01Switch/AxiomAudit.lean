import RequestProject.NANC.Gate01Switch.Main
import RequestProject.NANC.Gate01CombinedLedger
/-!
# Gate01Switch: trust audit

`#print axioms` on representative theorems of the switched bank.  Each reports
only `propext`, `Classical.choice`, `Quot.sound` (the ledger theorems report no
axioms at all).  No custom axiom is introduced anywhere in the bank.
-/

open TwinPrimeProject.Gate01Switch
#print axioms dvd_add_two_iff_mod_eq
#print axioms sum_residueMinusTwo_eq_sum_multiplier
#print axioms switchedOperator_eq_multiplier
#print axioms switchedOperator_eq_SW2
#print axioms lambda3_primePow
#print axioms lambda3_squarefree
#print axioms switchedOperator_three_way
#print axioms repeated_prime_factorization
#print axioms divisorsAntidiagonal_shift_eq_q5Fibre
#print axioms genericSwitched_q5_expansion
#print axioms q5_and_sparse_strata_imply_switched_fixedCell
#print axioms switched_cells_and_coverage_imply_gate1B
#print axioms switchedFiniteBank_proved
#print axioms switchedAnalyticItems_not_proved
#print axioms no_factorization_of_coarse_semiprime
#print axioms vaughanSwitchIdentity
#print axioms hardSwitchedExponentRegion_nonempty
#print axioms TwinPrimeProject.Gate01Combined.finiteBanks_proved
