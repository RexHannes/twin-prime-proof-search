/-
# NANC Gate 1A v9.6 — status ledger, layer firewall and axiom audit

    ACTUAL W_{D,e}:               ARBITRARY EDGE DEPENDENT
                                  (`actualWeightVerdict`, source path
                                  `EdgeDependentD2Data.coeff`)
    EDGEDEPENDENT-D2:             NOT `E♯` ADMISSIBLE
                                  (`deltaEdgeData_no_small_template`,
                                  `finiteTemplateCertificate_delta_card`)
    FINITE TEMPLATE CERTIFICATE:  CONSTRUCTED for common weights only
                                  (`commonFiniteTemplate`)
    SOURCE-EXACT DICTIONARY:      CONSTRUCTED and PINNED for the actual
                                  common-D2 source (`commonD2Dictionary`,
                                  `commonD2_source_partition`);
                                  NOT constructed for the full census
    PACKET MULTIPLICITY:          EXACTLY 1 for the actual common-D2 dictionary
                                  (`commonD2Multiplicity_exact`);
                                  SOURCE MISSING for the interface-only packets
    GENERIC BPP ANALYTIC INHAB.:  ABSENT — only the vacuous inhabitant exists
                                  (`genericBPPBound_vacuously_inhabited`,
                                  `genericBPP_says_nothing_about_other_energy`)
    ROOTDEFECT SOURCE FACTOR.:    CANONICAL INHABITANT CONSTRUCTED; pinning open
    ZERO-PROJ SOURCE FACTOR.:     CANONICAL INHABITANT CONSTRUCTED; pinning open
    CLEAN-P3 CLOSURE CERT.:       INHABITABLE ONLY FROM A SUPPLIED `E♯` BOUND
                                  (`cleanP3Certificate_of_bound`); the physical
                                  target version is conditional
    ALL-m CLOSURE CERT.:          CONSTRUCTED ONLY for the actual common-D2
                                  source and only with the triangle-inequality
                                  target (`commonD2Closure`,
                                  `commonD2Closure_finalTarget_is_trivial`)
    ALL-m SOURCE EXHAUSTIVENESS:  NOT CONSTRUCTED — twelve census packets have
                                  no defined operator at all
                                  (`interfaceOnlyPackets_length`)
    GATE1B:                       UNCHANGED
    FULL TYPE II:                 NOT INFERRED
    TWIN PRIMES:                  NOT INFERRED

--------------------------------------------------------------------------
## The layer firewall (Section 23 of the v9.6 instructions)

Four different things are never merged in this bank:

* **A** finite compiler proved;
* **B** analytic theorem available only as an interface;
* **C** actual source dictionary constructed;
* **D** final closure certificate constructed.

`v96Ledger` records the layer of every v9.6 item, and
`layers_not_collapsed` proves that the four layers really occur separately in
the ledger, so no single "PASS" can be read off it.

--------------------------------------------------------------------------
## Ford–Maynard / Full Type II firewall (unchanged)

Nothing in v9.6 declares Full Type II or twin primes.  The Gate 1A all-`m`
source is *not* exhausted: the census still contains packets whose source is an
externally supplied proposition.
-/
import RequestProject.NANC.Gate1A.SafeExtensions.V96ActualWeight
import RequestProject.NANC.Gate1A.SafeExtensions.V96SourceDictionary
import RequestProject.NANC.Gate1A.SafeExtensions.V96SourceLocators
import RequestProject.NANC.Gate1A.SafeExtensions.V96Certificates

namespace TwinPrimeProject.NANC.Gate1A.V96

/-! ## 1. The four status layers -/

/-- The four layers that must never be collapsed into one verdict. -/
inductive V96Layer
  /-- A: a finite compiler theorem, proved in Lean. -/
  | finiteCompilerProved
  /-- B: an analytic statement present only as an interface field. -/
  | analyticInterfaceOnly
  /-- C: an actual source object constructed from repository definitions. -/
  | actualSourceConstructed
  /-- D: a final closure certificate constructed. -/
  | closureCertificateConstructed
  deriving DecidableEq, Repr

/-- Outcome of a v9.6 item. -/
inductive V96Outcome
  | constructed
  | constructedConditionally
  | notConstructed
  | refuted
  deriving DecidableEq, Repr

/-- One line of the v9.6 ledger. -/
structure V96Entry where
  label : String
  layer : V96Layer
  outcome : V96Outcome
  note : String
  deriving Repr

/-- The v9.6 ledger. -/
def v96Ledger : List V96Entry :=
  [ { label := "ACTUAL_WEIGHT_ARBITRARY_EDGE_DEPENDENT"
    , layer := .actualSourceConstructed, outcome := .constructed
    , note := "EdgeDependentD2Data.coeff is an unconstrained function of the edge" }
  , { label := "EDGEDEPENDENT_D2_NOT_ESharp_ADMISSIBLE"
    , layer := .finiteCompilerProved, outcome := .refuted
    , note := "delta edge weights force at least #Edge common templates" }
  , { label := "FINITE_TEMPLATE_CERTIFICATE_COMMON_ONLY"
    , layer := .finiteCompilerProved, outcome := .constructed
    , note := "one template, unit nuclear cost, for a common weight" }
  , { label := "SOURCE_EXACT_DICTIONARY_COMMOND2_PINNED"
    , layer := .actualSourceConstructed, outcome := .constructed
    , note := "actualSource = CommonD2Data.edgeSum, coverage identity proved" }
  , { label := "SOURCE_EXACT_DICTIONARY_FULL_CENSUS"
    , layer := .actualSourceConstructed, outcome := .notConstructed
    , note := "12 of 19 packets have no defined operator in the source" }
  , { label := "PACKET_MULTIPLICITY_COMMOND2_EXACT_ONE"
    , layer := .finiteCompilerProved, outcome := .constructed
    , note := "one analytic occurrence per (pair, harmonic)" }
  , { label := "PACKET_MULTIPLICITY_SOURCE_MISSING"
    , layer := .analyticInterfaceOnly, outcome := .notConstructed
    , note := "interface-only packets expose no decomposition measure" }
  , { label := "GENERIC_BPP_ANALYTIC_INHABITANT"
    , layer := .analyticInterfaceOnly, outcome := .notConstructed
    , note := "only the vacuous inhabitant with zero energy functional exists" }
  , { label := "ROOTDEFECT_SOURCE_FACTORIZATION_CANONICAL"
    , layer := .finiteCompilerProved, outcome := .constructed
    , note := "canonical inhabitant; pinning to the actual hard parent open" }
  , { label := "ZERO_PROJECTIVE_SOURCE_FACTORIZATION_CANONICAL"
    , layer := .finiteCompilerProved, outcome := .constructed
    , note := "canonical inhabitant with trivial fibre multiplicity" }
  , { label := "GATE1A_CLEANP3_CLOSURE_CERTIFICATE"
    , layer := .closureCertificateConstructed, outcome := .constructedConditionally
    , note := "needs a supplied E-sharp bound; target must be supplied physically" }
  , { label := "GATE1A_ALLM_CLOSURE_CERTIFICATE_COMMOND2"
    , layer := .closureCertificateConstructed, outcome := .constructedConditionally
    , note := "actual common-D2 source, triangle-inequality target only" }
  , { label := "GATE1A_ALLM_SOURCE_EXHAUSTIVENESS"
    , layer := .actualSourceConstructed, outcome := .notConstructed
    , note := "unclassified packets remain; first one is edgeDependentD2" }
  ]

/-! ## 2. Layer firewall -/

/-- The ledger really contains all four layers: no single verdict summarises
it. -/
theorem layers_not_collapsed :
    (v96Ledger.any fun e => e.layer = V96Layer.finiteCompilerProved) ∧
    (v96Ledger.any fun e => e.layer = V96Layer.analyticInterfaceOnly) ∧
    (v96Ledger.any fun e => e.layer = V96Layer.actualSourceConstructed) ∧
    (v96Ledger.any fun e => e.layer = V96Layer.closureCertificateConstructed) := by
  decide

/-- The ledger contains unfinished items: v9.6 is a partial run. -/
theorem v96_not_complete :
    v96Ledger.any fun e => e.outcome = V96Outcome.notConstructed := by decide

/-- No item is recorded as unconditionally constructed at the closure layer. -/
theorem no_unconditional_closure :
    ∀ e ∈ v96Ledger, e.layer = V96Layer.closureCertificateConstructed →
      e.outcome = V96Outcome.constructedConditionally := by decide

/-- The all-`m` census is still blocked: interface-only packets remain. -/
theorem allM_still_blocked : interfaceOnlyPackets ≠ [] := by decide

/-! ## 3. Axiom audit -/

#print axioms actualWeightVerdict_ne_common
#print axioms edgeData_coeff
#print axioms template_count_ge_of_linearIndependent
#print axioms deltaEdgeData_linearIndependent
#print axioms deltaEdgeData_no_small_template
#print axioms finiteTemplateCertificate_delta_card
#print axioms commonFiniteTemplate_cost
#print axioms sourceDictionary_inhabited_for_every_source
#print axioms genericBPPBound_vacuously_inhabited
#print axioms genericBPP_says_nothing_about_other_energy
#print axioms esharpAdapter_nonempty_iff
#print axioms commonD2Dictionary_pins
#print axioms commonD2Dictionary_contribution
#print axioms commonD2_source_partition
#print axioms commonD2Multiplicity_exact
#print axioms commonD2Closure_bound
#print axioms commonD2Closure_finalTarget_is_trivial
#print axioms commonD2_is_the_only_dictionary_ready_packet
#print axioms edgeDependentD2_is_dataOnly
#print axioms interfaceOnlyPackets_length
#print axioms majority_of_packets_are_interfaces
#print axioms sourceDecl_ne_empty
#print axioms first_non_dictionary_ready
#print axioms rootDefectSourceFactorization_inhabited
#print axioms rootDefect_hardParent_unique
#print axioms zeroProjectiveSourceFactorization_inhabited
#print axioms zeroProjective_sourceCoeff_unique
#print axioms canonicalZeroProjective_fibreCard
#print axioms cleanP3Certificate_self_referential
#print axioms cleanP3Certificate_physical_target
#print axioms layers_not_collapsed
#print axioms v96_not_complete
#print axioms no_unconditional_closure
#print axioms allM_still_blocked

end TwinPrimeProject.NANC.Gate1A.V96
