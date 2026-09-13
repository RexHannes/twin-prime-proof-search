/-
# Gate1B / R11 / Frontier / CanonicalRootSync / TerminalRamanujan : axiom audit  (T14)

`#print axioms` for every theorem of the terminal-Ramanujan layer.  Each one must report only
a subset of `propext`, `Classical.choice`, `Quot.sound`.  No custom axiom, no `sorry`, no
`native_decide`, no `unsafe`, no `opaque`, no `@[implemented_by]` occurs in this directory.
-/
import Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.TruncatedMobius
import Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.RamanujanFinite
import Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.RamanujanCoeff
import Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.CofactorAllocation
import Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.PrimeAllocation
import Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.CoefficientFormula
import Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.TerminalSplit
import Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ComplementaryQuotient
import Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.RowOperator
import Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.TerminalOwner
import Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.CanonicalBridge
import Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.Firewall
import Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.TerminalCut

-- TruncatedMobius
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.Cutoffs.mem_I1
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.Cutoffs.mem_I2
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.Cutoffs.mem_box
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.Cutoffs.box_pos
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.Cutoffs.box_prod_le
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.lam_zero
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.lam_eq_zero_of_Qmax_lt
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.lam_eq_zero_of_even
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.lam_eq_sum_filter
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.lam_ne_muConv
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.lam_three_wide
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.assembled_bound_does_not_imply_packetwise
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.assembled_zero_with_large_packets

-- RamanujanFinite
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.divisors_gcd_eq_filter
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ram_eq_ramAlt
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.sum_ram_divisors
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ram_one

-- RamanujanCoeff
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.lam_cast
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.aCoeff_eq_aDiv
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.filter_dvd_eq_divisors
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.Fsum_eq_ramanujan_expansion
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.aCoeff_eq_zero_of_even
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.aCoeff_eq_zero_of_cube_dvd

-- CofactorAllocation
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.D1_mul_D2
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.moebius_D1_mul_D2
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.moebius_eq_zero_of_not_coprime_cofactor
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.moebius_interval_extraction

-- PrimeAllocation
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.indDvd_apply
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.isMultiplicative_indDvd
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ind_mul_of_coprime
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.squarefree_dvd_of_primes_dvd
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.isMultiplicative_allocKernel
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.mult_eval_squarefree
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.allocKernel_prime
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.prod_ind_eq
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.allocKernel_eq_triple
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.alloc_indicator
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.q_dvd_iff
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.alloc_indicator_with_b

-- CoefficientFormula
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.odd_of_dvd_odd
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.term_alloc_expansion
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.aCoeff_cofactor_allocation

-- TerminalSplit
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.Fsum_eq_low_add_top
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.Ftop_zero_cutoff
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.Ftop_full_cutoff
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.Flow_eq_sub

-- ComplementaryQuotient
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.aCoeff_complementary_quotient
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.aCoeff_sum_over_quotients
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.Ftop_complementary_quotient
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.filter_dvd_top
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.Ftop_large_divisor
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.terminal_small_complement
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.terminal_small_complement_rat
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.Ftop_terminal_support

-- RowOperator
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.rowOp_add
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.rowOp_arg_pos
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.rowOp_terminal_split
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.moment_split
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.raw_moment_budget
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.moment_eq_top_of_low_zero
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.moment_algebra_does_not_bound

-- TerminalOwner
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.scalarBudget_const_mul
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.epM2_of_terminal_parts
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.epM2_needs_terminal_owner

-- CanonicalBridge
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.j2_of_epM2
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.j2_of_terminal_route
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.dbRaw_budget_of_terminal_route
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.epM2Realisation_load_bearing
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.j2_owner_still_open
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.terminal_owner_still_open

-- Firewall
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.chamber_624_in_window
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.chamber_624_lt_five_eighths
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.chamber_621_in_window
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.terminal_factorable_small_complement
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.factorable_structure_does_not_imply_topBound

-- TerminalCut
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.canonical_cut_retained
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.canonical_cut_length_retained
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.tcutSet_r11
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.tcutSet_j2ViaTerminal
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.terminal_nodes_offroute
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.unique_new_bridge
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.terminal_owner_below_j2
