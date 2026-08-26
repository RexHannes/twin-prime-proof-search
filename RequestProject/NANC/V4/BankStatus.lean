/-
NANC V4 — bank status table and axiom audit.

Every entry of the bank is given an explicit status.  The `#print axioms` block
at the end audits the Lean-banked theorems.
-/
import Mathlib
import RequestProject.NANC.V4.Counterguards
import RequestProject.NANC.V4.ComparisonModel
import RequestProject.NANC.V4.N2RepairInterface

namespace NANC.V4

/-- A bank entry: a name together with its status. -/
structure BankEntry where
  name : String
  status : BankStatus

/-- Entries that are genuinely proved in Lean. -/
def leanBankedEntries : List BankEntry :=
  [ ⟨"BankStatus no-promotion guards", BankStatus.leanBanked⟩,
    ⟨"one_sixth_gt_fm_threshold", BankStatus.leanBanked⟩,
    ⟨"one_sixth_threshold_margin", BankStatus.leanBanked⟩,
    ⟨"shrunk_nu_gt_threshold_of_eps_small", BankStatus.leanBanked⟩,
    ⟨"shrunk_theta_add_nu", BankStatus.leanBanked⟩,
    ⟨"twinLocalFactor elementary identities", BankStatus.leanBanked⟩,
    ⟨"shiftedPrime_inputs_imply_FMTypeI (Gate-0 compiler)", BankStatus.conditionalTheorem⟩,
    ⟨"scale_comparison_prime_mass", BankStatus.leanBanked⟩,
    ⟨"positive_weightedTwinMass_exists_twin", BankStatus.provedFinite⟩,
    ⟨"sourceSpecificTypeII_not_definitionally_FMTypeII", BankStatus.provedFinite⟩,
    ⟨"gate1A_gate1B_not_FMTypeII", BankStatus.provedFinite⟩,
    ⟨"ordinary_positive_ne_bounded_positive", BankStatus.provedFinite⟩,
    ⟨"fm_central_width_one_sixth_conditional", BankStatus.conditionalTheorem⟩,
    ⟨"FMShiftedPrimeEndgamePackage projections", BankStatus.conditionalTheorem⟩ ]

/-- Entries that are defined but deliberately uninhabited. -/
def externalEntries : List BankEntry :=
  [ ⟨"FMTypeIAtScale", BankStatus.uninhabitedInterface⟩,
    ⟨"FMTypeIIAtScale", BankStatus.uninhabitedInterface⟩,
    ⟨"MaximalWeightedBVShiftedPrime", BankStatus.externalAnalyticInput⟩,
    ⟨"ComparisonProgressionMean", BankStatus.externalAnalyticInput⟩,
    ⟨"FMComparisonB1", BankStatus.externalAnalyticInput⟩,
    ⟨"FMComparisonB2", BankStatus.externalAnalyticInput⟩,
    ⟨"FMGrowthCondition", BankStatus.externalAnalyticInput⟩,
    ⟨"FMPositiveCentralWidth (Ford–Maynard Thm 2.7)", BankStatus.externalAnalyticInput⟩,
    ⟨"FMBoundedPositiveNearCentral", BankStatus.externalAnalyticInput⟩,
    ⟨"FullFMTypeIIReassembly", BankStatus.uninhabitedInterface⟩,
    ⟨"FMShiftedPrimeN2Upper", BankStatus.uninhabitedInterface⟩,
    ⟨"FMShiftedPrimeEndgameSplice", BankStatus.uninhabitedInterface⟩,
    ⟨"TwoLinearFormsUpperSieveOutput", BankStatus.uninhabitedInterface⟩,
    ⟨"EventuallyPositiveTwinMass / twin-prime infinitude", BankStatus.uninhabitedInterface⟩ ]

/-- Research claims that are explicitly NOT banked. -/
def notBankedClaims : List String :=
  [ "Gate 1A frontier closure",
    "Gate 1B frontier closure",
    "proposed source-specific N₂ repair",
    "claim that the Gate-0 analytic input is discharged",
    "claim that Gate 2 is unconditionally closed" ]

/-- **Global guard.**  No entry of the external list is proof-bearing. -/
theorem externalEntries_not_proofBearing :
    ∀ e ∈ externalEntries, BankStatus.IsProofBearing e.status = false := by
  decide

/-- **Global guard.**  No entry of the Lean-banked list is interface-only. -/
theorem leanBankedEntries_not_interfaceOnly :
    ∀ e ∈ leanBankedEntries, BankStatus.IsInterfaceOnly e.status = false := by
  decide

section Audit

#print axioms BankStatus.sourceMissing_ne_failedRoute
#print axioms BankStatus.uninhabited_ne_proved
#print axioms BankStatus.conditional_ne_unconditional
#print axioms BankStatus.not_proofBearing_and_interfaceOnly
#print axioms one_sixth_gt_fm_threshold
#print axioms one_sixth_threshold_margin
#print axioms shrunk_nu_gt_threshold_of_eps_small
#print axioms shrunk_theta_add_nu
#print axioms typeIIInterval_eq
#print axioms twinLocalFactor_nonneg
#print axioms twinLocalFactor_one
#print axioms twinLocalFactor_mul_new_prime
#print axioms shiftedPrime_inputs_imply_FMTypeI
#print axioms scale_comparison_prime_mass
#print axioms scale_comparison_prime_mass_lt
#print axioms positive_weightedTwinMass_exists_twin
#print axioms positive_genericTwinMass_exists_twin
#print axioms eventuallyPositiveTwinMass_imp_infinite
#print axioms sourceSpecificTypeII_not_definitionally_FMTypeII
#print axioms gate1AB_certificate_imp_full_reassembly
#print axioms gate1A_gate1B_not_FMTypeII
#print axioms ordinary_positive_ne_bounded_positive
#print axioms fm_central_width_one_sixth_conditional
#print axioms fm_shrunk_width_conditional
#print axioms typeI_alone_not_gate2
#print axioms width_arithmetic_alone_not_positivity
#print axioms interface_never_banked
#print axioms no_promotion
#print axioms FMShiftedPrimeEndgamePackage.positiveTwinMass
#print axioms package_gives_twin_pair
#print axioms no_package_from_nothing
#print axioms splice_imp_n2Upper
#print axioms n2_alone_does_not_close_gate2

end Audit

end NANC.V4
