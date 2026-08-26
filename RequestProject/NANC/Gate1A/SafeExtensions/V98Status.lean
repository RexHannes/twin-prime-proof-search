/-
# NANC Gate 1A v9.8 — status ledger and axiom audit

    AUTHORITATIVE DIRECT SOURCE:   PINNED  (`Gate1ADirectCanonicalSource`,
                                   `ctilde_def`), provenance
                                   `sourceInspectedNotProved`
    PHYSICAL W_D:                  COMMON  (`gate1A_direct_physicalWeight_common`,
                                   `covariance_eq_weight_pairing`,
                                   `exists_rowDependent_weight_not_common`)
    CANONICAL ALL-m ROW FAMILY:    CONSTRUCTED (`Gate1ADirectAllMRow`,
                                   `exists_allMRow_not_cleanP3`)
    GATE1A DIRECT ENERGY:          CONSTRUCTED
                                   (`Gate1ADirectPacket.normalizedEnergy`,
                                   `gate1ADirectAllMPhysicalEnergy`)
    TARGET BRIDGE:                 PROVED (`directTarget_bridge`,
                                   `physical_of_normalized_bound`)
    BPP ENERGY PIN:                INTERFACE CONSTRUCTED, UNINHABITED
                                   (`Gate1ADirectBPPEnergyPin`,
                                   `energyPin_not_automatic`,
                                   `energyPin_not_implied_by_conclusion`)
    BPP FINITE COMPILER:           PROVED (reuse of v9.4
                                   `familyEnergy_of_participation`, plus
                                   `primeParticipation_familyEnergy`)
    BPP EXTERNAL ANALYTIC INPUT:   EXTERNALLY VERIFIED, NOT FORMALISED
                                   (`Gate1ABPPPrimeParticipationInput`,
                                   provenance `externallyPublished` /
                                   `sourceSpecificAnalyticPass`)
    FAMILY ENERGY / ONE ROOT:      `familyEnergyExp_eq` = −1/2,
                                   `oneRoot_exponent` = −1/4
    MARGINS:                       V1 = 1/72, V2 = 1/24, V3 = 1/32
                                   (frozen v9.4 ledger, re-exported)
    U^{-2} RECOMBINATION:          PROVED (identity + margins 1/18, 1/18, 1/24)
    CLEAN-P3:                      COROLLARY (`cleanP3_of_allM_bound`)
    EDGEDEPENDENT-D2:              GATE 0 ADAPTER OBLIGATION
                                   (`edgeDependentD2_is_gate0_adapter_obligation`);
                                   the datum itself is untouched
    ROOTDEFECT FACTORISATION:      SECONDARY ROUTE, OPEN
                                   (`rootDefect_is_secondary_route`)
    GATE0 → GATE1A COMPILER:       OPEN, and provably not definitional
                                   (`Gate0.gate0Exhaustiveness_not_definitional`)
    GATE1A DIRECT LEAN STATUS:     EXTERNAL-UNINHABITED
    GATE1A DIRECT RESEARCH STATUS: recorded as a *source* status, never as a
                                   Lean theorem
    GATE1B / GATE0 / GATE2:        UNCHANGED by this run
    FULL FM TYPE II:               NOT INFERRED
    TWIN PRIMES:                   NOT PROVED

The closure-status model of Section 24 is `ClosureLayer`; `v98Ledger` records
the layer, outcome and provenance of every v9.8 item and
`layers_not_collapsed`, `no_lean_inhabitant_claimed` and
`research_status_is_not_lean_evidence` prevent the single-verdict reading.
-/
import RequestProject.NANC.Gate1A.SafeExtensions.V98CanonicalDirectSource
import RequestProject.NANC.Gate1A.SafeExtensions.V98CanonicalAllMRows
import RequestProject.NANC.Gate1A.SafeExtensions.V98DirectEnergyPin
import RequestProject.NANC.Gate1A.SafeExtensions.V98BPPProvenance
import RequestProject.NANC.Gate1A.SafeExtensions.V98DirectClosure
import RequestProject.NANC.Gate1A.SafeExtensions.V98Gate0ScopeSplit

namespace TwinPrimeProject.NANC.Gate1A.V98

/-! ## 1. The closure-status model (Section 24) -/

/-- The five distinguishable layers of a v9.8 item. -/
inductive ClosureLayer
  /-- A: a finite theorem proved in Lean. -/
  | finiteLeanTheorem
  /-- B: a source definition pinned in Lean. -/
  | sourceDefinitionPinned
  /-- C: a published or source-specific analytic input, verified outside Lean. -/
  | externalAnalyticInput
  /-- D: a research-level closure claim. -/
  | researchClosure
  /-- E: a Lean inhabitant that does not exist. -/
  | leanInhabitantAbsent
  deriving DecidableEq, Repr

/-- Outcome of a v9.8 item. -/
inductive V98Outcome
  | constructed
  | constructedConditionally
  | interfaceOnly
  | notConstructed
  deriving DecidableEq, Repr

/-- One ledger line. -/
structure V98Entry where
  label : String
  layer : ClosureLayer
  outcome : V98Outcome
  provenance : Provenance
  note : String
  deriving Repr

/-- **The v9.8 ledger.** -/
def v98Ledger : List V98Entry :=
  [ { label := "CANONICAL_DIRECT_SOURCE_PINNED"
    , layer := .sourceDefinitionPinned, outcome := .constructed
    , provenance := .sourceInspectedNotProved
    , note := "Ctilde transcribed literally; only algebraic identities proved" }
  , { label := "PHYSICAL_WD_COMMON"
    , layer := .finiteLeanTheorem, outcome := .constructed
    , provenance := .leanProved
    , note := "one weight field; row dependence is derived, not source-chosen" }
  , { label := "CANONICAL_ALLM_ROW_FAMILY"
    , layer := .finiteLeanTheorem, outcome := .constructed
    , provenance := .leanProved
    , note := "ESharpRow reused; strictly larger than the clean-P3 family" }
  , { label := "CANONICAL_DIRECT_ENERGY_AND_TARGETS"
    , layer := .finiteLeanTheorem, outcome := .constructed
    , provenance := .leanProved
    , note := "normalized and physical energies plus the H-normalisation bridge" }
  , { label := "BPP_ENERGY_PIN"
    , layer := .leanInhabitantAbsent, outcome := .interfaceOnly
    , provenance := .interfaceOpen
    , note := "single-equation interface; guards show it is neither free nor self-derived" }
  , { label := "BPP_FINITE_COMPILER"
    , layer := .finiteLeanTheorem, outcome := .constructed
    , provenance := .leanProved
    , note := "E_off <= D*S/P^2*T_abs, reused from the v9.4 bank" }
  , { label := "BPP_EXTERNAL_ANALYTIC_INPUT"
    , layer := .externalAnalyticInput, outcome := .interfaceOnly
    , provenance := .externallyPublished
    , note := "plateau participation: Bernstein + primes in intervals shorter than R^{3/4}" }
  , { label := "SMOOTH_SEPARATION_TEMPLATES"
    , layer := .externalAnalyticInput, outcome := .interfaceOnly
    , provenance := .sourceSpecificAnalyticPass
    , note := "finite Fourier-Mellin templates with X^o nuclear cost; compiler proved" }
  , { label := "EXPONENT_LEDGER_AND_MARGINS"
    , layer := .finiteLeanTheorem, outcome := .constructed
    , provenance := .leanProved
    , note := "R^{-1/2} family energy, one root R^{-1/4}, margins 1/72, 1/24, 1/32" }
  , { label := "RECOMBINATION_ERROR_U2"
    , layer := .finiteLeanTheorem, outcome := .constructed
    , provenance := .leanProved
    , note := "controlling U^{-2} identity, spare margins 1/18, 1/18, 1/24" }
  , { label := "CLEANP3_COROLLARY"
    , layer := .finiteLeanTheorem, outcome := .constructed
    , provenance := .leanProved
    , note := "positive compression of clean rows into the all-m family" }
  , { label := "GATE1A_DIRECT_CLOSURE_COMPILER"
    , layer := .finiteLeanTheorem, outcome := .constructedConditionally
    , provenance := .leanProved
    , note := "deterministic; inhabited exactly by its premises" }
  , { label := "EDGEDEPENDENT_D2_SCOPE"
    , layer := .finiteLeanTheorem, outcome := .constructed
    , provenance := .leanProved
    , note := "Gate 0 adapter obligation, not an input of the canonical theorem" }
  , { label := "ROOTDEFECT_SECONDARY"
    , layer := .finiteLeanTheorem, outcome := .constructed
    , provenance := .leanProved
    , note := "secondary route; not a field of the Direct closure certificate" }
  , { label := "GATE0_TO_GATE1A_EXHAUSTIVENESS"
    , layer := .leanInhabitantAbsent, outcome := .notConstructed
    , provenance := .interfaceOpen
    , note := "OPEN; provably not definitionally true" }
  ]

/-! ## 2. Firewalls on the ledger -/

/-- The ledger genuinely contains several layers: no single verdict summarises
it. -/
theorem layers_not_collapsed :
    (v98Ledger.any fun e => e.layer = ClosureLayer.finiteLeanTheorem) ∧
    (v98Ledger.any fun e => e.layer = ClosureLayer.sourceDefinitionPinned) ∧
    (v98Ledger.any fun e => e.layer = ClosureLayer.externalAnalyticInput) ∧
    (v98Ledger.any fun e => e.layer = ClosureLayer.leanInhabitantAbsent) := by
  decide

/-- **No Lean inhabitant is claimed for any external analytic input.** -/
theorem no_lean_inhabitant_claimed :
    ∀ e ∈ v98Ledger, e.layer = ClosureLayer.externalAnalyticInput →
      e.outcome = V98Outcome.interfaceOnly := by decide

/-- **Research status is not Lean evidence.**  Every ledger entry whose
provenance is not `leanProved` fails the Lean-evidence test. -/
theorem research_status_is_not_lean_evidence :
    ∀ e ∈ v98Ledger, e.provenance ≠ Provenance.leanProved →
      e.provenance.isLeanEvidence = false := by decide

/-- The run is partial: open items remain. -/
theorem v98_not_complete :
    v98Ledger.any fun e => e.outcome = V98Outcome.notConstructed := by decide

/-- No item is recorded as an unconditional Lean closure. -/
theorem no_unconditional_closure :
    ∀ e ∈ v98Ledger, e.label = "GATE1A_DIRECT_CLOSURE_COMPILER" →
      e.outcome = V98Outcome.constructedConditionally := by decide

/-! ## 3. Axiom audit -/

#print axioms eR_add
#print axioms norm_eR
#print axioms omegaCanonical_weight_factor
#print axioms omegaCanonical_congr_of_common_weight
#print axioms Gate1ADirectCanonicalSource.ctilde_def
#print axioms Gate1ADirectCanonicalSource.ctilde_excludes_diagonal
#print axioms Gate1ADirectCanonicalSource.norm_phase
#print axioms Gate1ADirectCanonicalSource.gate1A_direct_physicalWeight_common
#print axioms Gate1ADirectCanonicalSource.coeffAt_congr_of_common_weight
#print axioms SmoothSeparationCertificate.canonicalWeight_finiteTemplate
#print axioms SmoothSeparationCertificate.templateCount_eq
#print axioms SmoothSeparationCertificate.coeff_nuclear_bound
#print axioms arbitraryEdgeDependent_needs_edge_many_templates
#print axioms allMRow_witness
#print axioms exists_allMRow_not_cleanP3
#print axioms cleanP3_embeds_allM_faithful
#print axioms cleanP3_energy_le_allM_energy
#print axioms cleanP3_of_allM_bound
#print axioms Fibre.direct_determinant_identity
#print axioms PhysicalDirectSource.covariance_def
#print axioms PhysicalDirectSource.covariance_determinant
#print axioms PhysicalDirectSource.covariance_eq_weight_pairing
#print axioms PhysicalDirectSource.common_weight_shared_by_rows
#print axioms exists_rowDependent_weight_not_common
#print axioms Gate1ADirectPacket.normalizedEnergy_def
#print axioms Gate1ADirectPacket.normalizedEnergy_nonneg
#print axioms gate1ADirectAllMPhysicalEnergy_nonneg
#print axioms directTarget_bridge
#print axioms physical_of_normalized_bound
#print axioms Gate1ADirectBPPEnergyPin.energy_le
#print axioms normalizedEnergy_le_target_of_pin
#print axioms unitSource_ctilde
#print axioms unitPacket_energy
#print axioms energyPin_not_automatic
#print axioms energyPin_not_implied_by_conclusion
#print axioms energyPin_nonempty_iff
#print axioms provenance_not_lean_evidence
#print axioms Gate1ABPPPrimeParticipationInput.primeParticipation_familyEnergy
#print axioms Gate1ABPPPrimeParticipationInput.participationInput_not_self_inhabiting
#print axioms familyEnergyExp_eq
#print axioms oneRoot_exponent
#print axioms oneRoot_real
#print axioms directMargin_V1
#print axioms directMargin_V2
#print axioms directMargin_V3
#print axioms directMargins_pos
#print axioms directErrorMargins_U2
#print axioms directGateComparison_of_margin
#print axioms Gate1ADirectClosureCertificate.toPhysicalTarget
#print axioms Gate1ADirectClosureCertificate.toCanonicalStatement
#print axioms closureCertificate_nonempty_iff
#print axioms closure_not_implied_by_physical_target
#print axioms emptyPacket_energy
#print axioms emptyPhysical_energy
#print axioms directRecombinationError_U2
#print axioms edgeDependentD2_is_gate0_adapter_obligation
#print axioms rootDefect_is_secondary_route
#print axioms gate0_obligations
#print axioms gate0_disjoint_from_gate1ADirect
#print axioms edgeDependentD2Data_still_available
#print axioms Gate0.gate0Exhaustiveness_not_definitional
#print axioms Gate0.gate0Exhaustiveness_nonempty_iff
#print axioms gate1ADirect_closure_independent_of_gate0
#print axioms gate1ADirect_does_not_imply_gate0
#print axioms layers_not_collapsed
#print axioms no_lean_inhabitant_claimed
#print axioms research_status_is_not_lean_evidence
#print axioms v98_not_complete
#print axioms no_unconditional_closure

end TwinPrimeProject.NANC.Gate1A.V98
