/-
# Gate1B / R11 : axiom audit for the TWIN GATE1B R11 formal banking run

`#print axioms` for every principal theorem of the run.  Each depends only on a subset of
`{propext, Classical.choice, Quot.sound}`; there is no custom axiom, no `sorry`, no
`native_decide`, and no `@[implemented_by]` anywhere in the new layer.
-/
import Gate1B.R11.StatusBank

namespace Gate1B.R11

-- Vaughan chart layer
#print axioms Gate1B.R11.vaughan_identity
#print axioms Gate1B.R11.vTwo_vaughan_eq_mobius_log_split
#print axioms Gate1B.R11.vTwo_lane_ledger
#print axioms Gate1B.R11.fourLaneValue_eq_longMobiusValue

-- Polytope / 6-11 geometry
#print axioms Gate1B.R11.ExponentVector.block_sum
#print axioms Gate1B.R11.ExponentVector.Mblock_le
#print axioms Gate1B.R11.ExponentVector.one_sub_Mblock_ge
#print axioms Gate1B.R11.ExponentVector.Lblock_ge
#print axioms Gate1B.R11.ExponentVector.pinned_ledger
#print axioms Gate1B.R11.smallMVector_counterexample
#print axioms Gate1B.R11.smallNVector_counterexample
#print axioms Gate1B.R11.pascadi_conditions_of_polytope

-- Long-Möbius reindexing and determinant algebra (earlier layer, re-audited)
#print axioms Gate1B.R11.longMobiusLog_reindex
#print axioms Gate1B.R11.determinant_eq_neg_two
#print axioms Gate1B.R11.determinant_pairwise_cross_coprime
#print axioms Gate1B.R11.determinant_minusTwo_solution_parametrization

-- Cutoff conservation and the hybrid min lemma
#print axioms Gate1B.R11.exponent_conservation
#print axioms Gate1B.R11.rpow_conservation
#print axioms Gate1B.R11.hybrid_min_le

-- Reciprocity
#print axioms Gate1B.R11.reciprocity_mod_one
#print axioms Gate1B.R11.reciprocity_exp

-- SL2 Bruhat
#print axioms Gate1B.R11.det_rescaled_eq_one
#print axioms Gate1B.R11.bruhat_factorisation
#print axioms Gate1B.R11.bruhat_factorisation_zmod

-- Hilbert-HMRD
#print axioms Gate1B.HilbertHMRD.fourier_inversion
#print axioms Gate1B.HilbertHMRD.fcoef_parseval
#print axioms Gate1B.HilbertHMRD.fcoef_l1_le_sqrt_totient
#print axioms Gate1B.HilbertHMRD.hilbertL2Bound_of_scalarL2Bound
#print axioms Gate1B.HilbertHMRD.operatorNorm_tensor_identity_hilbert
#print axioms Gate1B.HilbertHMRD.packet_small_branch
#print axioms Gate1B.HilbertHMRD.packet_energy_branch
#print axioms Gate1B.HilbertHMRD.packet_energy_branch_interval
#print axioms Gate1B.HilbertHMRD.packet_hmrd

-- Status bank and firewall
#print axioms Gate1B.R11.bank_vaughan_identity
#print axioms Gate1B.R11.bank_chart_equivalence
#print axioms Gate1B.R11.bank_polytope_611
#print axioms Gate1B.R11.bank_hilbert_hmrd
#print axioms Gate1B.R11.hmrd_applies_of_physicalCaller

end Gate1B.R11
