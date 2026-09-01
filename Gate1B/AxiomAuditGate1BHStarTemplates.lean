import Gate1B.CurrentStatusGate1BHStarTemplates

/-!
# Gate 1B · axiom audit for the HSTAR source-template safe bank

`#print axioms` for every public theorem of the modules

* `Gate1B.VaughanLambda3P3Bridge`
* `Gate1B.HStarK0J0VaughanCentering`
* `Gate1B.HStarK0J0SourceGrammar`
* `Gate1B.HStarK0J0DeterminantShell`
* `Gate1B.HStarTemplateFamily`
* `Gate1B.HStarFiniteNuclearCompiler`
* `Gate1B.Gate1BFamilyScopeFirewall`
* `Gate1B.HStarTemplateUniformityInterface`
* `Gate1B.CurrentStatusGate1BHStarTemplates`

Only the standard foundations `propext`, `Classical.choice` and `Quot.sound`
may appear.  There is no `sorry`, no `sorryAx`, no custom `axiom`, no
`native_decide`, no `implemented_by` and no `opaque` shortcut anywhere in this
bank.
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace HStarTemplates

-- VaughanLambda3P3Bridge
#print axioms afC_truncation_decomposition
#print axioms highHighCoefficient_apply
#print axioms lambda3AF_eq_highHighCoefficient
#print axioms lambda3_conv_zeta_eq_highHighP3
#print axioms exists_af_conv_zeta_ne_self
#print axioms highHighCoefficient_one_one_one
#print axioms highHighCoefficient_one_one_two
#print axioms highHighCoefficient_one_one_four
#print axioms highHighCoefficient_one_one_eight
#print axioms highHighP3_one_one_eight
#print axioms lambda3_ne_highHighP3
#print axioms no_bridge_modulus_to_hard
#print axioms mem_switchedMultiplierSet
#print axioms switched_sum_eq_pairSum
#print axioms switched_pairing_reindex
#print axioms switched_pairing_eq_highHighP3
-- HStarK0J0VaughanCentering
#print axioms afR_truncation_decomposition
#print axioms vaughanP3R_eq_coefficient_conv_zeta
#print axioms exactVaughanIdentityR
#print axioms centering_identity
#print axioms vonMangoldt_centering
#print axioms vonMangoldt_centering_apply
#print axioms shifted_pairing_centering
#print axioms localRough_not_identified_with_global
#print axioms centering_transport_of_bridge
-- HStarK0J0SourceGrammar
#print axioms hStarSourceKind_u_ne_v
#print axioms HStarK0J0Source.k_is_zero
#print axioms HStarK0J0Source.J_is_empty
#print axioms HStarK0J0Source.gEmpty_is_one
#print axioms HStarK0J0Source.uKind_ne_vKind
#print axioms uBase_eq_zero_of_not_squarefree
#print axioms vBase_ne_zero
#print axioms uBase_ne_vBase
#print axioms no_common_source_family
#print axioms uBlock_primes_nodup
#print axioms vBlock_support_not_strictly_ordered
-- HStarK0J0DeterminantShell
#print axioms determinant_shell
#print axioms shell_of_determinant
#print axioms determinant_shell_raw
#print axioms determinant_shell_nat
#print axioms sum_divisorPair_reindex
#print axioms modulus_coefficient_reindex
-- HStarTemplateFamily
#print axioms HStarK0J0Template.determinantOK_of_shell
#print axioms sampleTemplate_ne_sampleTemplate'
#print axioms exists_family_not_singleton
#print axioms member_does_not_determine_family
-- HStarFiniteNuclearCompiler
#print axioms nuclear_compiler
#print axioms family_recombination_bound
#print axioms parent_bound_of_certificate
#print axioms certificate_recombination
#print axioms rawSourceEnergy_mono
#print axioms rawSourceEnergy_unitTwist
#print axioms finite_cauchy_energy
#print axioms rawMultiplicativeEnergy_mono
#print axioms card_divisorsAntidiagonal_le
#print axioms rawEnergy_ne_gate1A_covarianceEnergy
#print axioms rawEnergy_eq_covariance_of_trivial_weight
-- Gate1BFamilyScopeFirewall
#print axioms hStarTemplateGate1BBound_iff
#print axioms cancellingPackets_recombination
#print axioms scalar_closed_but_not_family_uniform
#print axioms scalar_does_not_imply_family_uniform
#print axioms scalar_of_family_uniform
#print axioms family_uniform_of_forall
#print axioms forgetWD_not_injective
#print axioms no_physical_weight_from_template
-- HStarTemplateUniformityInterface
#print axioms familyUniform_of_certificate
#print axioms scalar_closure_insufficient_for_uniformity
#print axioms produced_bound_of_census_and_uniformity
#print axioms parent_bound_of_certificates
#print axioms reassembly_needs_family_certificate

end HStarTemplates

namespace LedgerGate1BHStarTemplates

-- The status layer itself.
#print axioms no_closed_rows
#print axioms ledger_is_honest
#print axioms current_research_frontier
#print axioms global_gate1B_open
#print axioms twin_prime_open
#print axioms interfaces_open
#print axioms new_exact_rows_kernel_proved
#print axioms previous_layer_preserved

end LedgerGate1BHStarTemplates
end CurrentProgramme
end TwinPrimeProject
