/-
# Gate1B / R11 : axiom audit

`#print axioms` for every principal theorem of the R11 canonical bank.  The build log of
this module is the audit record.  No custom axiom is declared anywhere in `Gate1B.R11`.
-/
import Gate1B.R11.Bank

namespace Gate1B.R11

-- CARD5
#print axioms choose_ten_five
#print axioms card_card5Selectors
#print axioms moebius_selectedDivisor
#print axioms selectedDivisor_squarefree
#print axioms card5_equal_n_collapse
#print axioms card5_equal_n_collapse_of_blind

-- 5|4|2 and factorial normalization
#print axioms card_Alloc442
#print axioms mem_Alloc442
#print axioms factor542_normalization_mul
#print axioms factor542_normalization
#print axioms factorial_ten_split
#print axioms factorial_normalization_no_extra_multiplicity
#print axioms card5_outer_coefficient_ledger
#print axioms ratio_252_3150

-- canonical source: labels, collisions, rational metadata
#print axioms R11Labels.atoms_injective
#print axioms moebius_prod_primes
#print axioms squarefree_prod_primes
#print axioms crossGroupPairs_count
#print axioms omegaSquarefree_eq_free_sub_collision
#print axioms sum_omegaSquarefree_eq
#print axioms canonical_source_from_free_of_collision_bound
#print axioms centers_sum_to_one
#print axioms p0_plus_four_large
#print axioms six_large
#print axioms split_227_273
#print axioms gap_23_250

-- comparison typing
#print axioms comparison_weight_typing
#print axioms comparison_weight_typing_sum
#print axioms bFull_ne_bLoc

-- Möbius–log split
#print axioms vonMangoldt_eq_sum_moebius_mul_log
#print axioms vonMangoldt_split
#print axioms vonMangoldtTrunc_two_eq_zero_of_odd

-- long-Möbius reindexing
#print axioms divisor_involution_bijOn
#print axioms longMobiusLog_reindex
#print axioms weighted_longMobius_reindex

-- matched determinant and Bézout
#print axioms determinant_eq_neg_two
#print axioms determinant_pairwise_cross_coprime
#print axioms determinant_solution_parametrization
#print axioms determinant_solution_parametrization_unique

-- bank and firewall
#print axioms r11_low_closed_implies_longMobius_residual
#print axioms r11_low_closed_implies_longMobius_residual_with_collision
#print axioms internal_bank_does_not_entail_coverage
#print axioms canonical_internal_bank_complete

end Gate1B.R11
