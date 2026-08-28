import RequestProject.NANC.Gate1B.V11Counterguards
import RequestProject.NANC.Gate1B.V11FMProvenance
import RequestProject.NANC.Gate1B.V11PairModParentCompiler
import RequestProject.NANC.Gate1B.V11GeneratedTypeIIReassembly
import RequestProject.NANC.Gate1B.V11V10Compatibility

/-!
# V11 · Gate 1B — status and axiom audit

Every principal v11 declaration is passed through `#print axioms`.  Expected
output for each: exactly `[propext, Classical.choice, Quot.sound]` (or "does not
depend on any axioms").

No `sorry`, no `admit`, no user `axiom`, no `native_decide`, no
`@[implemented_by]` occurs in any v11 module.

## Status ledger

| item | status |
| --- | --- |
| FM SieveGen project predicate | DEFINED |
| FM Perron generated grammar | DEFINED + PROVED FINITE COST THEOREMS |
| Real Ford grammar certificate | UNINHABITED / REPO DATA ABSENT |
| FMPerron generated Type-II predicate | DEFINED |
| SieveGen ⟶ Generated | PROVED |
| Generated ⟶ SieveGen | NOT CLAIMED |
| S2 pure Mellin | INTERFACE (uninhabited) + PROVED FINITE COMPILER |
| S2 `P⁻`/`P⁺` | OPEN ANALYTIC INTERFACE |
| PairMod source value | DEFINED |
| Fixed-vs-moving multiplier firewall | PROVED |
| Source multiplier rank-one algebra | PROVED (reuses banked D₁₂ identities) |
| Shifted capacity 1/32 | CAPACITY_ONLY |
| QK capacity 1/108 | CAPACITY_ONLY |
| Worst margin | 1/108 |
| PairMod analytic input | UNINHABITED |
| PairMod ⟶ shifted parent | CONDITIONAL COMPILER |
| PairMod ⟶ QK5/6 parent | CONDITIONAL COMPILER |
| PairMod ⟶ V10 four leaves | PROVED (no type mismatch) |
| Generated Type-II reassembly | CONDITIONAL COMPILER |
| Gate 1B | OPEN / UNCHANGED |
-/

namespace TwinPrimeProject
namespace Gate1BV11

/-! ## Grammar atoms -/
#print axioms norm_cpow_I_mul_le_one
#print axioms rampR_mem_unitInterval
#print axioms norm_semAtom_le_one
#print axioms norm_semPrimeExtremaAtom_le_one
#print axioms semAtom_mobius_two
#print axioms semAtom_not_constant

/-! ## Generated expressions and cost -/
#print axioms cost_nonneg
#print axioms norm_product_le
#print axioms norm_finiteSum_le_l1Cost
#print axioms convolution_divisorBound
#print axioms norm_semExpr_le_cost
#print axioms finite_template_reassembly
#print axioms finite_template_reassembly_of_cost
#print axioms fmPerronGeneratedUnit_atom
#print axioms fmPerronGeneratedUnit_mobius
#print axioms FMPerronGenerated.mul
#print axioms FMPerronGenerated.add
#print axioms FMPerronGenerated.smul
#print axioms FMPerronGenerated.conv
#print axioms FMPerronGenerated.finiteLinearCombination
#print axioms FMPerronGeneratedUnit.mul
#print axioms FMPerronGrammarCertificate.generated

/-! ## The project-local Type-II predicates -/
#print axioms fmPerronGeneratedTypeII_of_sieveGen
#print axioms sieveGenValue_toy
#print axioms fmPerronGeneratedTypeII_toy_fails
#print axioms fmSieveGenTypeII_toy_fails

/-! ## The grammar compiler -/
#print axioms FMProofGeneratedPacket.factorFun_generated
#print axioms generatedPacketFamily_bound
#print axioms shifted_log_budget
#print axioms generatedPacketFamily_logBudget
#print axioms compiler_hypotheses_are_load_bearing

/-! ## S2 generated twists -/
#print axioms defectTransform_add_weight
#print axioms defectTransform_smul_defect
#print axioms norm_defectTransform_le
#print axioms defectTransform_backendDualNorm
#print axioms s2Generated_gives_pureMellin
#print axioms s2Generated_gives_primeExtrema
#print axioms pureMellin_transform_does_not_control_extremaTransform

/-! ## The `P±` firewall -/
#print axioms separatingModel_mellinValue_zero
#print axioms separatingModel_extremaValue
#print axioms mellinControl_does_not_imply_primeExtremaControl
#print axioms extremaTwist_constant_on_prime_fibre
#print axioms Pminus_four
#print axioms Pplus_four
#print axioms Pminus_eight
#print axioms Pplus_eight
#print axioms mellinTwist_separates_four_eight
#print axioms mellinTwist_four_ne_zero
#print axioms primeExtremaTwist_is_not_a_mellinTwist

/-! ## Pair-modulus source multiplier -/
#print axioms PairModSourceData.pairModFamilyValue_eq
#print axioms PairModSourceData.norm_pairModFamilyValue_le
#print axioms PairModSourceData.kernel_scale

/-! ## The moving-multiplier firewall -/
#print axioms alignedFamily_pairing
#print axioms alignedFamily_fixed_bound
#print axioms alignedFamily_norm_A
#print axioms alignedFamily_l2_energy
#print axioms alignedFamily_value_norm
#print axioms fixedMultiplierBounds_do_not_control_movingFamily
#print axioms antiAlignedFamily_pairing
#print axioms antiAlignedFamily_norm_A
#print axioms l2Energy_does_not_determine_familyValue

/-! ## Rank-one source structure -/
#print axioms SourceRankOne.l1_factor
#print axioms SourceRankOne.l2_factor
#print axioms rankOne_does_not_give_movingFamily_saving

/-! ## Capacity arithmetic -/
#print axioms worstMargin_eq
#print axioms qk_is_the_binding_constraint
#print axioms tax_below_worst_leaves_margin
#print axioms tax_below_worst_leaves_shifted_margin
#print axioms oneEighteenth_gt_oneOneOhEight
#print axioms sqrtY_familyTax_kills_qk_margin
#print axioms sqrtY_familyTax_no_margin
#print axioms sqrtY_familyTax_deficit
#print axioms admissible_tax_window_nonempty

/-! ## The pair-modulus analytic interface and its compilers -/
#print axioms FMPerronPairModSourceMultiplierInput.coeffSlot_generated
#print axioms FMPerronPairModSourceMultiplierInput.norm_parentValue_le
#print axioms pairMod_to_shiftedQuotientParent
#print axioms pairMod_to_qk56FullCovariance
#print axioms shiftedQuotientParentBound_not_automatic
#print axioms qk56FullCovarianceBound_not_automatic

/-! ## The V10 analytic-leaf bridge -/
#print axioms v10AnalyticLeaves_of_parentBounds
#print axioms pairModPackage_to_v10AnalyticLeaves
#print axioms leafBundle_not_automatic

/-! ## Generated Type-II reassembly -/
#print axioms fmPerronGeneratedTypeII_of_reassembly
#print axioms reassembly_transform_stays_generated
#print axioms no_reassembly_for_toyData
#print axioms reassembly_targets_v11_predicate

/-! ## V10 compatibility -/
#print axioms gate1B_closed_of_v11_leaves_and_v10_pins
#print axioms leaves_alone_do_not_close_gate1B

/-! ## Counterguards A–F -/
#print axioms rampR_of_le
#print axioms rampR_of_ge
#print axioms rampR_lt_one
#print axioms counterguard_A_generatedAtoms_are_not_all_unitBounded
#print axioms counterguard_B_mellin_ne_primeExtrema
#print axioms counterguard_B_semantic
#print axioms counterguard_C_fixed_ne_moving
#print axioms counterguard_D_l2Energy_ne_coherence
#print axioms counterguard_D_rankOne_no_saving
#print axioms counterguard_E_compiler_is_not_a_theorem
#print axioms counterguard_F_leaves_ne_closure

end Gate1BV11
end TwinPrimeProject
