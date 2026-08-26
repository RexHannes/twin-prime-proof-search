import RequestProject.FixedCertificateAlgebra
import RequestProject.AnalyticInterfaces

/-!
# Conservative K0/K1 structural and analytic status ledger

Source geometry and analytic estimates are represented only by explicit
proof-carrying inputs or status metadata. No global inhabitant is provided.
-/

namespace TwinPrimeProject

/-- A proposition proved only after the exact Ford source definitions are
supplied. This record does not prove its stored proposition. -/
structure FordSourceGeometryInput where
  proposition : Prop
  proof : proposition
  sourceDefinitions : List String

/-- Transparent accessor, not a source theorem. -/
theorem useFordSourceGeometry (h : FordSourceGeometryInput) : h.proposition := h.proof

inductive K0K1Status where
  | leanProved
  | externallyAudited
  | provedModuloSource
  | conditionalInterface
  | openInput
  | hypothesisMismatch
  | failedRoute
  | auditedFailedRoute
  | unverifiedProofSketch
  | currentImmediateFrontier
  | candidateFrontierOnly
  deriving DecidableEq, Repr

structure K0K1Entry where
  label : String
  status : K0K1Status
  note : Option String
  deriving Repr

def k0k1Ledger : List K0K1Entry :=
  [ ⟨"FIXED_CERTIFICATE_NO_ROUGH_MOBIUS_SIGN", .leanProved, none⟩
  , ⟨"FIXED_CERTIFICATE_EXACT_FINITE_EXPANSION", .leanProved, none⟩
  , ⟨"ONE_MOBIUS_NORMAL_FORM", .leanProved, none⟩
  , ⟨"MOBIUS_FINITE_DIFFERENCE_IDENTITY", .leanProved, none⟩
  , ⟨"FINITE_DIFFERENCE_STRIP_ENDPOINT", .leanProved, none⟩
  , ⟨"ALTERNATING_BINOMIAL_PREFIX", .leanProved, none⟩
  , ⟨"K0_EQUAL_FACTOR_SIGN_TABLE", .leanProved, none⟩
  , ⟨"K0_EQUAL_FACTOR_R9_VALUE_70", .leanProved, none⟩
  , ⟨"K0_EQUAL_FACTOR_OPEN_CELL_STABILITY", .conditionalInterface, none⟩
  , ⟨"K0_EQUAL_FACTOR_CELL_OUTSIDE_N", .provedModuloSource, none⟩
  , ⟨"K0_GENUINE_DENSE_LEAKAGE_SUPPORT", .provedModuloSource, none⟩
  , ⟨"ROUGH_PRIME_COUNT_AT_MOST_SIX", .leanProved, none⟩
  , ⟨"CERTIFICATE_SUPPORTED_SUBSET_SIZE_AT_MOST_THREE", .leanProved, none⟩
  , ⟨"K1_ALL_PRINCIPAL_VARIABLES_POWER_LENGTH", .leanProved, none⟩
  , ⟨"SQUAREFULL_KERNEL_ALGEBRAIC_REPAIR", .leanProved, none⟩
  , ⟨"SQUAREFULL_FIBRE_UNIFORM_ANALYTIC_SUMMATION", .openInput, none⟩
  , ⟨"DIRECT_K0_TO_K1_BUCHSTAB_REDUCTION", .failedRoute,
      some "largest K0 prime lies below n^sigma < n^nu0, outside the K1 singleton window"⟩
  , ⟨"DIRECT_K1_TO_K0_TRUNCATION_REDUCTION", .failedRoute,
      some "truncation uniformity does not imply uniformity for the twisted shifted-prime weight"⟩
  , ⟨"K0_K1_DIRECT_REDUCTIONS_FAILED", .auditedFailedRoute, none⟩
  , ⟨"ARBITRARY_COEFFICIENT_CENTERED_FORD_TYPE_II", .openInput,
      some "sufficient but possibly overbroad for the fixed-certificate application"⟩
  , ⟨"EXACT_VAUGHAN_OR_HEATH_BROWN_PACKET_LEDGER", .currentImmediateFrontier, none⟩
  , ⟨"FIXED_COEFFICIENT_VAUGHAN_RESIDUE", .unverifiedProofSketch, none⟩
  , ⟨"ANATOMICAL_BOMBIERI_VINOGRADOV", .hypothesisMismatch, none⟩
  , ⟨"B_SIDE_ANATOMICAL_MAIN_TERM", .openInput, none⟩
  , ⟨"BFI_K1_WEIGHT_CLASS_MATCH", .hypothesisMismatch, none⟩
  , ⟨"DFI_DETERMINANT_MATCH", .hypothesisMismatch, none⟩
  , ⟨"RAW_DISPERSION_MIXED_TERM_CLOSURE", .openInput, none⟩
  , ⟨"FIXED_CERTIFICATE_L2", .candidateFrontierOnly, none⟩
  ]

end TwinPrimeProject
