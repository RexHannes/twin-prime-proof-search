import Mathlib

/-!
# Status taxonomy for the Shifted Möbius Type-II / F3 ledger

This module defines the machine-readable proof-status datatype used throughout the
banking project, together with a small registry mapping theorem labels to their
current status.  Nothing here is an axiom or a mathematical claim: it is purely a
bookkeeping layer that makes the ledger checkable by the Lean kernel.
-/

namespace ShiftedMobiusBank

/-- The status taxonomy required by the master banking task.

* `leanProved` — the complete stated theorem is machine-checked in Lean with no
  `sorry`/`admit`/`axiom`/`implemented_by`.
* `leanProvedCore` — an algebraic/modular core is machine-checked.
* `externallyAudited` — an externally checked result not fully formalized in Lean.
* `literatureVerified` — an exact statement with verified source location.
* `conditionalInterface` — a consequence from an explicit hypothesis, not an axiom.
* `provisionalReduction` — an audited reduction not yet a complete theorem.
* `sourcePending` — exact external wording or source location has not been supplied.
* `openInput` — an exact theorem still needed.
* `refuted` — a statement disproved or a route blocked.
* `superseded` — an earlier status replaced by a later audit. -/
inductive ProofStatus where
  | leanProved
  | leanProvedCore
  | externallyAudited
  | literatureVerified
  | conditionalInterface
  | provisionalReduction
  | openInput
  | refuted
  | superseded
  | sourcePending
  deriving DecidableEq, Repr

/-- A single ledger entry: a label, its current status, and its previous status
(if the entry was superseded). -/
structure LedgerEntry where
  label : String
  status : ProofStatus
  supersedes : Option String := none
  deriving Repr

/-- Machine-readable registry of the current ledger.  This is the Lean mirror of
the executive status table in `LEDGER.md`. -/
def ledger : List LedgerEntry :=
  [ ⟨"CW_MU_CONDUCTOR_WINDOW_BANKED", .externallyAudited, none⟩
  , ⟨"F3_R2_BD_REDUCTION", .externallyAudited, none⟩
  , ⟨"F3_R2_MAIN_TERM_KILLED", .externallyAudited, none⟩
  , ⟨"LOW_MID_CONDUCTORS_CONTROLLED", .externallyAudited, none⟩
  , ⟨"ABSOLUTE_BD_REFUTED", .refuted, none⟩
  , ⟨"ACTUAL_KF_DIAGONAL_PROVED", .externallyAudited,
      some "ACTUAL_KF_DIAGONAL_PROVISIONAL (conditional)"⟩
  , ⟨"ABSTRACT_POISSON_DIAGONAL_FALSE", .refuted, none⟩
  , ⟨"KF_OFFDIAG_CROSSCOPRIME_PROVED", .externallyAudited, none⟩
  , ⟨"DOUBLE_CROSS_PRIMEPOWER_EXTRACTION", .leanProvedCore,
      some "DOUBLE_CROSS_GCD_PROVISIONAL (conditional)"⟩
  , ⟨"RESIDUAL_COLLAPSE_PROVED", .leanProvedCore, none⟩
  , ⟨"COMPLETE_DOUBLE_CROSS_PHASE_FACTORIZED", .externallyAudited, none⟩
  , ⟨"ONE_MODULUS_FOURIER_SEPARATION", .externallyAudited, none⟩
  , ⟨"FOURIER_LOSS_DM_SQRT", .externallyAudited, none⟩
  , ⟨"FALSE_MPAIR_ONE_OVER_G_REFUTED", .refuted, none⟩
  , ⟨"ACTUAL_KF_TINY_WEDGE_CORRECTED", .externallyAudited,
      some "ACTUAL_KF_TINY_WEDGE_PROVISIONAL (conditional)"⟩
  , ⟨"RATIO_SPLIT_WRIGHT_WEDGE_PROVED", .externallyAudited, none⟩
  , ⟨"ACTUAL_KF_WEDGE_122_162", .externallyAudited, none⟩
  , ⟨"F3_R2_PARTIALLY_KILLED_WIDENED", .externallyAudited, none⟩
  , ⟨"MESOSCOPIC_MOBIUS_LEMMA_ADMISSIBLE_Q", .externallyAudited, none⟩
  , ⟨"UNRESTRICTED_Q_MESOSCOPIC_FALSE", .refuted, none⟩
  -- New in this update: fixed-depth routing + high-conductor/full-piece split.
  , ⟨"F3_FIXED_DEPTH_ROUTABLE_SECTOR_PROVED", .externallyAudited,
      some "F3_FIXED_DEPTH_ROUTING (was OPEN_INPUT)"⟩
  , ⟨"HIGH_CONDUCTOR_COMPONENT_POWER_SAVING", .externallyAudited, none⟩
  , ⟨"FULL_ROUTED_PIECE_LOG_SAVING", .externallyAudited, none⟩
  , ⟨"F3_R2_HIGH_CONDUCTOR_POWER_SAVING", .externallyAudited, none⟩
  , ⟨"FULL_ROUTED_PIECE_POWER_SAVING_REFUTED_AS_STATED", .refuted, none⟩
  , ⟨"GLOBAL_ORIENTATION_WRIGHT_WIDENING_FAILED", .refuted, none⟩
  -- Fixed-depth routing threshold and reindexing are machine-checked here.
  , ⟨"ROUTING_THRESHOLD_W_STAR", .leanProved, none⟩
  , ⟨"FIXED_DEPTH_ROUTING_REINDEX", .leanProved, none⟩
  , ⟨"FIXED_DEPTH_CONVOLUTION_MAJORANT", .leanProved, none⟩
  -- F1 migration.
  , ⟨"LONG_MOBIUS_F1_MIGRATION_ROUTABLE_PROVED", .externallyAudited,
      some "LONG_MOBIUS_F1_MIGRATION_THEOREM (was OPEN_INPUT)"⟩
  , ⟨"MESOSCOPIC_LEMMA_ALONE_DOES_NOT_SOLVE_F1", .refuted, none⟩
  , ⟨"FULL_F1_MIGRATION_OPEN", .openInput, none⟩
  , ⟨"F1_ULTRASHORT_AGGREGATE_MAIN_TERM", .openInput, none⟩
  , ⟨"F1_ULTRASHORT_OFFDIAGONAL", .openInput, none⟩
  , ⟨"F1_ULTRASHORT_CORE_REDUCTION", .provisionalReduction, none⟩
  -- Exact next open wall.
  , ⟨"TWO_OUTER_VARIABLE_F3_KERNEL", .openInput, none⟩
  , ⟨"F3_SINGLE_OUTER_UNROUTABLE_CORE", .openInput, none⟩
  , ⟨"HYBRID_MQ_KLOOSTERMAN_LARGE_SIEVE", .openInput, none⟩
  , ⟨"BALANCED_TII_CORE", .openInput, none⟩
  , ⟨"PARITY_OPEN", .openInput, none⟩
  -- Machine-checked algebra/parameters (this project):
  , ⟨"wedge_containment_206_implies_122", .leanProved, none⟩
  , ⟨"oldWedge_sigma_feasible_iff", .leanProved, none⟩
  , ⟨"splitting_parameter_122_162", .leanProved, none⟩
  , ⟨"wright_term_exponent_inequalities", .leanProved, none⟩
  , ⟨"sector_partition_exhaustive_disjoint", .leanProved, none⟩
  , ⟨"double_cross_residual_coprime", .leanProved, none⟩
  , ⟨"crt_residual_collapse_core", .leanProved, none⟩
  , ⟨"mesoscopic_finite_product_bound", .leanProved, none⟩
  , ⟨"routing_threshold_equiv", .leanProved, none⟩
  , ⟨"newWedge_iff_wStar", .leanProved, none⟩
  , ⟨"maj_fixed_depth", .leanProved, none⟩
  , ⟨"routing_reindex", .leanProved, none⟩
  , ⟨"routedCoeff_divBounded", .leanProved, none⟩
  , ⟨"ultrashort_product_bound", .leanProved, none⟩
  , ⟨"f3_fixed_depth_routable_full_piece", .leanProved, none⟩
  , ⟨"long_mobius_f1_migration_routable", .leanProved, none⟩
  , ⟨"status_distinctions_consistent", .leanProved, none⟩
  -- Ford/F1/F2 conservative banking update.
  , ⟨"FORD_MAYNARD_POSITIVITY_INTERFACE", .sourcePending, none⟩
  , ⟨"FORD_PROJECT_TRANSFERENCE_CONDITIONS", .conditionalInterface, none⟩
  , ⟨"OUTER_BLOCK_AVERAGE_LEMMA", .leanProved, none⟩
  , ⟨"FINITE_OUTER_LEVEL_ARITHMETIC", .leanProvedCore, none⟩
  , ⟨"F1_GLOBAL_CENTERING_IDENTITY", .leanProvedCore, none⟩
  , ⟨"F1_COMPARISON_SEQUENCE_AXIOMS", .openInput, none⟩
  , ⟨"FINITE_MULTIPLICATIVE_CHARACTER_EXPANSION", .externallyAudited, none⟩
  , ⟨"FINITE_MULTIPLICATIVE_CHARACTER_EXPANSION_CORE", .leanProvedCore, none⟩
  , ⟨"F2_DOUBLE_MELLIN_PRIME_UNIT", .sourcePending, none⟩
  , ⟨"NAIVE_RECIPROCAL_TENSOR_EXPONENT", .leanProvedCore, none⟩
  , ⟨"RECIPROCAL_TENSOR_GAP_THREE_HALVES", .leanProved, none⟩
  , ⟨"F2_PP_MAIN", .sourcePending, none⟩
  , ⟨"F2_PN_SINGLE_SPECTRAL", .sourcePending, none⟩
  , ⟨"F2_NP_SINGLE_SPECTRAL", .sourcePending, none⟩
  , ⟨"F2_NN_RECIPROCAL_TENSOR", .openInput, none⟩
  , ⟨"RECIPROCAL_CHARACTER_TENSOR_LARGE_SIEVE", .openInput, none⟩
  , ⟨"F2_COMPOSITE_GCD_REASSEMBLY", .openInput, none⟩
  , ⟨"FULL_F2", .openInput, none⟩
  , ⟨"FULL_F3", .openInput, none⟩
  , ⟨"FULL_F1", .openInput, none⟩
  , ⟨"UNIFORM_PROJECT_TYPE_II", .openInput, none⟩
  , ⟨"RCT_SMOOTH_ALPHA", .sourcePending, none⟩
  , ⟨"RCT_SMOOTH_C_H", .sourcePending, none⟩
  , ⟨"RCT_PRIME_MODULUS", .sourcePending, none⟩
  , ⟨"RCT_SEMIPRIME_MODULUS", .sourcePending, none⟩
  , ⟨"RCT_QUADRATIC_CHARACTERS", .sourcePending, none⟩
  , ⟨"RCT_AVERAGED_SHIFT", .sourcePending, none⟩
  , ⟨"RCT_WELL_FACTORABLE_LAMBDA", .sourcePending, none⟩
  , ⟨"F3_ONE_OUTER_ROUTABLE", .externallyAudited, none⟩
  , ⟨"F3_TWO_OUTER", .openInput, none⟩
  , ⟨"F3_THREE_OUTER", .sourcePending, none⟩
  , ⟨"F3_FOUR_OUTER", .sourcePending, none⟩
  ]

/-- Count of entries with a given status (useful sanity check for the ledger). -/
def countStatus (s : ProofStatus) : Nat :=
  (ledger.filter (fun e => e.status = s)).length

end ShiftedMobiusBank
