import RequestProject.Status
import Mathlib

/-!
# Frontier status table (§18, §30)

A machine-readable ledger of every banked label with its status, plus the
current strongest banked *unconditional* high-conductor condition.
-/

namespace Banking.Frontier

open Banking

/-- The banked ledger: label ↦ status.  Mirrors `LEDGER.md` §A. -/
def ledger : List (String × BankStatus) :=
  [ -- Primitive algebraic core (this update)
    ("TWO_OUTER_LATTICE_IDENTITY", .leanProved),
    ("PRIMITIVE_INNER_LATTICE_COUNT", .leanProved),
    ("PRIMITIVE_FORM_C_RESIDUE", .leanProvedCore),
    ("PRIMITIVE_FORM_C_R2_RECONSTRUCTION", .leanProvedCore),
    ("PRIMITIVE_LATTICE_SOLVABILITY", .leanProved),
    ("PRIMITIVE_B1_PROGRESSION", .leanProved),
    ("PRIMITIVE_B2_RECONSTRUCTION", .leanProved),
    ("PRIMITIVE_RECIPROCITY_SPLIT", .leanProved),
    ("PRIMITIVE_ARCHIMEDEAN_PHASE_SMALL", .conditionalInterface),
    ("PRIMITIVE_PHASE_DETERMINANTS", .provisionalReduction),
    ("PRIMITIVE_ZERO_MODE_MAIN_TERM_DEFINED", .provisionalReduction),
    ("PRIMITIVE_B1_POISSON_COMPLETION", .externallyAudited),
    ("PRIMITIVE_NONZERO_PHASE", .externallyAudited),
    ("PRIMITIVE_FREQUENCY_RANGE", .externallyAudited),
    -- Deficit / exponent arithmetic
    ("P1_GENERIC_DEFICIT", .leanProved),
    ("BALANCED_P1_DEFICIT", .leanProvedCore),
    ("BALANCED_P2_DEFICIT", .leanProvedCore),
    ("BALANCED_P3_DEFICIT", .leanProvedCore),
    ("BALANCED_P4_SATURATION", .leanProvedCore),
    ("BALANCED_ADDITIVE_DIVISOR_SURPLUS", .leanProvedCore),
    ("ADDITIVE_DIVISOR_SURPLUS_EXACT_CONDITION", .leanProvedCore),
    ("ADDITIVE_DIVISOR_SURPLUS_SIMPLE_SUFFICIENT_CONDITION", .leanProvedCore),
    ("ABL_SCALE_MATCH_PENDING_FORMULA_AUDIT", .provisionalReduction),
    -- Controlled P1 strata (reported)
    ("P1_EXACT_DIAGONAL_REPORTED", .provisionalReduction),
    ("P1_DEGENERATE_REPORTED", .provisionalReduction),
    ("P1_NEAR_DEGENERATE_REPORTED", .provisionalReduction),
    ("P1_DIVISIBILITY_PINNED_REPORTED", .provisionalReduction),
    ("PRIMITIVE_FORM_C_LOCALIZATION", .provisionalReduction),
    ("CORRELATED_NUMERATOR_KF_FORM_XI", .provisionalReduction),
    -- Open inputs
    ("P1_CORRELATED_NUMERATOR_LOG", .openInput),
    ("P1_CORRELATED_NUMERATOR_POWER", .openInput),
    ("BILINEAR_LEVEL_SPECTRAL_LARGE_SIEVE", .openInput),
    ("PRIMITIVE_FOURTH_MOMENT_SAVING", .openInput),
    ("RANK_ONE_WEIGHTED_ABL_QUINTILINEAR", .openInput),
    ("ABL_SIGNED_MODULUS_WEIGHT_MATCH", .openInput),
    ("F1_AGGREGATE_MU_CONVOLUTION_MAIN_TERM", .openInput),
    ("TYPE_III_MINOR_ARC_OPERATOR", .openInput),
    ("FIXED_SHIFT_CONTAGION", .openInput),
    -- Literature
    ("FORD_MAYNARD_PRIME_PRODUCING_SIEVE_FRAMEWORK", .literatureVerified),
    ("FORD_MAYNARD_NU_0_1663_SOURCE_AUDIT", .numericalSourcePending),
    ("ABL_THEOREM_2_3_QUINTILINEAR_INPUT", .literatureVerified),
    ("SAWIN_SHUSTERMAN_FUNCTION_FIELD", .literatureVerifiedContext),
    -- Conditional interfaces
    ("CONDITIONAL_PARITY_BREAK_CHAIN", .conditionalInterface),
    -- Fable verdicts
    ("PRIMITIVE_FORM_C_REDUCED_TO_NEW_INPUT", .provisionalReduction),
    ("FORM_C_OPEN", .openInput),
    ("RESTORATION_OPEN", .openInput),
    ("F3_TWO_OUTER_PARTIAL", .provisionalReduction),
    ("FULL_F1_OPEN", .openInput),
    ("F2_OPEN", .openInput),
    ("NEW_EXACT_WALL", .provisionalReduction),
    -- Refuted / superseded
    ("ABSOLUTE_BD_REFUTED", .refuted),
    ("ABSTRACT_POISSON_DIAGONAL_FALSE", .refuted),
    ("FALSE_MPAIR_ONE_OVER_G_REFUTED", .refuted),
    ("UNRESTRICTED_Q_MESOSCOPIC_FALSE", .refuted),
    ("FULL_ROUTED_PIECE_POWER_SAVING_REFUTED_AS_STATED", .refuted),
    ("TWO_OUTER_SINGLE_OUTER_AUTOEXTENSION_REFUTED", .refuted),
    ("FORM_C_PROVED_REFUTED_AS_STATUS", .refuted),
    ("BALANCED_R3_PROVED_REFUTED_AS_STATUS", .refuted),
    ("PARITY_BROKEN_REFUTED_AS_STATUS", .refuted),
    -- ===== Audited prime short-window update (this run) =====
    -- §2 complete-period orthogonality (fully Lean-proved)
    ("KLOOSTERMAN_COMPLETE_ORTHOGONALITY", .leanProved),
    ("Q_SHEAR_COMPLETE_PERIOD_ENERGY", .leanProved),
    -- §3 nonzero Fourier-mode identity (fully Lean-proved)
    ("PRIME_SHORT_WINDOW_FOURIER_IDENTITY", .leanProved),
    -- §4 normalized trace conversion (fully Lean-proved)
    ("NORMALIZED_KLOOSTERMAN_TRACE_CONVERSION", .leanProved),
    -- §5 short-window Fourier normalization (fully Lean-proved) + conditional
    ("SHORT_WINDOW_FOURIER_NORMALIZATION", .leanProved),
    ("ARBITRARY_LAMBDA_FROM_FOURIER", .conditionalInterface),
    -- §6 spectral criticality (linear-algebra core Lean-proved)
    ("SHORT_WINDOW_SINGULAR_VALUE_LOWER_BOUND", .leanProved),
    ("ARBITRARY_LAMBDA_SW_SPECTRALLY_CRITICAL_INTERIOR", .externallyAudited),
    ("ARBITRARY_LAMBDA_SW_ENDPOINT", .provisional),
    -- §7 bilinear inverse-monomial (optimization Lean-proved; input literature)
    ("FKMS_INVERSE_MONOMIAL_BILINEAR", .literatureVerified),
    ("PRIME_INVERSE_KLOOSTERMAN_SAVING_1_224", .leanProvedCore),
    -- §8 trilinear factorized (comparison Lean-proved; application conditional)
    ("FKMS_INVERSE_MONOMIAL_TRILINEAR", .literatureVerified),
    ("PRIME_FACTORIZED_TRACE_SAVING_1_16", .conditionalInterface),
    -- §9 factorability polytope (fully Lean-proved)
    ("FACTORABILITY_SUBSET_SUM_POLYTOPE", .leanProved),
    ("AUTOMATIC_ONE_SIXTH_FACTORIZATION", .refuted),
    -- §10 Möbius-vector / joint-(q,h) interfaces (open analytic inputs)
    ("MOBIUS_VECTOR_SHORT_WINDOW", .openInput),
    ("AUTOCORRELATION_PRESERVING_JOINT_QH", .openInput),
    ("MOBIUS_KILLS_TOP_SINGULAR_VECTOR", .openInput),
    -- §11 Ford–Maynard positivity window (literature)
    ("FORD_MAYNARD_POSITIVITY_WINDOW", .literatureVerified),
    -- §12 superseded / rejected routes
    ("GENERIC_WEIGHTED_ABL", .supersededRoute),
    ("ONE_SIDED_WEIGHTED_ABL", .supersededRoute),
    ("PER_Q_ABL", .refutedRoute),
    ("ALL_MODULI_INTERVAL_AFTER_INVERSION", .refuted),
    ("KNOWN_QUADRILINEAR_HMVBARWBAR", .sourceNotFound) ]

/-- Lookup a label's status. -/
def statusOf (lbl : String) : Option BankStatus :=
  (ledger.find? (fun p => p.1 = lbl)).map Prod.snd

/-- The current strongest banked *unconditional* high-conductor condition
(retained from the single-outer ledger):
`122μ + 162θ < 1 ⟹ 𝒦 ≪ (X²/N)·X^{−η}`.  Here we record only the exponent
region. -/
def highConductorRegion (μ θ : ℝ) : Prop := 122 * μ + 162 * θ < 1

/-- The region is nonempty (sanity witness). -/
theorem highConductorRegion_nonempty : ∃ μ θ : ℝ, highConductorRegion μ θ :=
  ⟨0, 0, by unfold highConductorRegion; norm_num⟩

/-! ## §10 Open analytic interfaces (Möbius-vector / joint-(q,h))

These record the exact *shapes* of the requested open analytic inputs.  Each is
an `OPEN_INPUT` interface: the analytic assertion is a `Prop`-valued field, never
an axiom, so nothing is asserted to hold. -/

/-- **MOBIUS_VECTOR_SHORT_WINDOW** (`OPEN_INPUT`).  Short-window control of the
Möbius-twisted Kloosterman vector `∑_{yz∼Q} μ(y) ρ_z S(u/(yz), m; p)`, weaker
than arbitrary-λ short-window control.  Recorded as an abstract statement. -/
structure MobiusVectorShortWindow where
  /-- The analytic short-window bound `≪_A H p Y Z (log p)^{-A}`. -/
  statement : Prop

/-- **AUTOCORRELATION_PRESERVING_JOINT_QH** (`OPEN_INPUT`).  Joint `(q,h)`
trace large sieve whose `h`-weights must originate from a rank-one
autocorrelation `h = r₂ − r₁`, `α_{r₁} conj α_{r₂}`; the `h = 0` term is handled
separately.  The autocorrelation structure must be retained (not replaced by
arbitrary coefficients). -/
structure AutocorrelationPreservingJointQH where
  /-- The shift `h = r₂ − r₁`. -/
  shiftFromAutocorrelation : Prop
  /-- The `h = 0` diagonal is excluded / handled separately. -/
  diagonalExcluded : Prop
  /-- The analytic joint-(q,h) large-sieve bound. -/
  statement : Prop

end Banking.Frontier
