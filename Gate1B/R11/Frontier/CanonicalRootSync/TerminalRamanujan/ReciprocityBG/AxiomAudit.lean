/-
# Gate1B / R11 / Frontier / CanonicalRootSync / TerminalRamanujan / ReciprocityBG : axiom audit
(B12)

`#print axioms` for every theorem of this layer.  Each one must report only a subset of
`propext`, `Classical.choice`, `Quot.sound`.  No custom axiom, no `sorry`, no `admit`, no
`native_decide`, no `unsafe`, no `opaque`, no `@[implemented_by]` occurs in this directory.
-/
import Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.Realisation
import Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.CRTPhase
import Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.Reciprocity
import Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.MobiusProvenance
import Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.ComplementCost
import Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.DualFrequency
import Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.LowFrequencyOwner
import Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.HighFrequencyOwner
import Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.PowerBudget
import Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.Bridge
import Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.Firewall

-- Realisation
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.canonical_sum_over_chart
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.epM2Realisation_of_subBridges
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.ofCanonical_sourceWeight
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.ofCanonical_normalisation
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.epM2Realisation_ofCanonical
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.toyData_chart
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.epM2RowIdentification_load_bearing

-- CRTPhase
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.J_modEq_u
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.J_modEq_v
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.J_modEq_C
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.dvd_of_unit_mul
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.J_modEq_u_inv
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.mul_dvd_of_three
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.shiftedJ_unique
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.CongMod1.refl
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.CongMod1.symm
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.phase_factorisation
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.ee_congr
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.ee_add
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.phase_factorisation_exp
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.C_factor_not_removable

-- Reciprocity
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.reciprocity_mod_one
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.eComp_mul_Lcomp
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.eComp_dvd
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.coprime_Lcomp
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.Mone_mul_Mtwo
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.source_relation_reduces_denominator
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.source_relation_retains_e
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.reduction_needs_source_relation

-- MobiusProvenance
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.coprime_div_of_squarefree
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.moebius_mul_div
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.dvd_eq_gcd_mul_gcd
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.sum_divisors_coprime_split
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.lam_eq_divisors
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.lam_mobius_provenance
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.prime_dvd_of_sq_dvd_mul
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.sq_part_dvd
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.div_sq_mul
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.lam_mobius_provenance_sq
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.allocSum_respects_cutoffs

-- ComplementCost
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.allocCount_eq_mul
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.d2_eq_card_divisors
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.allocCount_eq_d2
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.harmR_nonneg
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.harmR_le_one_add_log
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.sum_d2_div_le_harmR_sq
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.complementAssemblyBudget_of_split

-- DualFrequency
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.dual_row_split
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.highDualRow_eq_zero
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.momentOf_split
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.dualMoment_split
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.dual_block_not_monotone
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.dual_block_moment_not_monotone

-- LowFrequencyOwner
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.bg_row_split
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.lowDualBudget_of_bg
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.lowDualBourgainGaraevBound_open
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.bg_bands_assemble

-- HighFrequencyOwner
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.epM2TopBound_of_high
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.atomwise_does_not_control_sum
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.atomWitness_high_row
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.atomWitness_atoms
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.atomWitness_not_joint
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.atoms_do_not_imply_joint
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.highDualJointAverageBound_open

-- PowerBudget
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.bgLowExponent_lt_reserve
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.bg_net_reserve
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.k4_exponent_gap
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.k4_weights
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.wedge_point_feasible
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.power_budget_does_not_close_owner

-- Bridge
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.epM2Bound_of_dual_owners
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.j2_of_dual_owners
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.j2_of_subBridges_and_dual_owners
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.bridge_does_not_close_j2
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.bridge_open_nodes

-- Firewall
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.dictionary_unconditional
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.external_inputs_open
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.averaging_firewall
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.realisation_firewall
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.phase_firewalls
#print axioms Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.layer_claims_nothing_unconditional
