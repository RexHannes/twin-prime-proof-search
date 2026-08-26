/-
# NANC Gate 1A v9.5 — status ledger, scope firewalls, axiom audit

    BPP GENERIC UNIT ENGINE:      P3-FREE / BANKED AS CERTIFICATE INTERFACE
                                  (`GenericBPPBound`, `ESharpGenericIsP3Free`)
    CLEAN-P3:                     CLOSED iff `Gate1ACleanP3ClosureCertificateV95`
                                  is constructed — it is NOT constructed here
    ALL-m GENERIC MODEL:          CLOSED (finite compiler `allM_packet_exhaustive`)
    ACTUAL ALL-m SOURCE:          OPEN — `AllMExhaustiveness` NOT constructed
    SOURCE-EXACT PACKET DICT.:    INCOMPLETE — first missing field
                                  `coversActualSource` for the edge-dependent
                                  `W_{D,e}` D2 packet
    MULTIPLICITY:                 CONTROLLED only where certified;
                                  `uncontrolledMultiplicity ≠ []`
    EDGE-DEPENDENT WEIGHTS:       FIRST OPEN PACKET = `edgeDependentD2`
                                  (`edgeDependent_not_common` forbids coercion)
    MULTIPLE HIGH-P3 OPERATORS:   RESIDUAL OPERATORS FOUND
                                  (`multiple_highP3_operators_unrouted`)
    EXCEPTION BANK:               TARGET-SPLICED only for the routed sectors
    GATE1A ALL-m:                 OPEN
    GATE1B:                       UNCHANGED
    FULL TYPE II:                 NOT INFERRED
    TWIN PRIMES:                  NOT INFERRED

--------------------------------------------------------------------------
## Gate-0 / Gate-1A scope firewall (permanent)

The Gate 1A *generic analytic engine* may well be all-`m` and P3-free: that is
exactly the content of `ESharpGenericIsP3Free`, which is a statement about the
data the engine consumes.

The Gate-0 / source compiler is a **different** question: whether every
*actual* source packet feeds that engine.  Therefore

    "the analytic theorem works for all m"

does **not** imply

    "the actual all-m Gate 1A source is exhaustively covered".

The census in `V95PacketCensus` is the machine-visible record of the gap.

--------------------------------------------------------------------------
## Ford–Maynard downstream firewall

Even if `Gate1AAllMClosureCertificate` were constructed, Full Type II would not
follow: the downstream argument needs an actual non-negative sequence with
complete Type-I/Type-II information, and Gate 1B together with the remaining
Gate-0 / source pieces are separate requirements.  Nothing in this bank
declares Full Type II or twin primes.

--------------------------------------------------------------------------
The `#print axioms` calls below are the axiom audit: only `propext`,
`Classical.choice` and `Quot.sound` may appear.  No user axiom exists in this
bank.
-/
import RequestProject.NANC.Gate1A.SafeExtensions.V95PacketCensus
import RequestProject.NANC.Gate1A.SafeExtensions.V95WeightFirewall
import RequestProject.NANC.Gate1A.SafeExtensions.V95Multiplicity
import RequestProject.NANC.Gate1A.SafeExtensions.V95ESharpScope
import RequestProject.NANC.Gate1A.SafeExtensions.V95Assembly
import RequestProject.NANC.Gate1A.SafeExtensions.V95Closure

namespace TwinPrimeProject.NANC.Gate1A.V95

#print axioms census_nodup
#print axioms census_not_all_classified
#print axioms firstUnclassified_is_edgeDependentD2
#print axioms firstUnclassified_weightDependence
#print axioms firstUnclassified_target
#print axioms multiplicity_not_fully_controlled
#print axioms multiple_highP3_operators_unrouted
#print axioms ofCommon_coeff_const
#print axioms edgeDependent_not_common
#print axioms finiteTemplate_nuclear_cost
#print axioms FiniteTemplateCertificate.weight_norm_le
#print axioms multiplicity_energy_le
#print axioms PacketMultiplicityCertificate.energy_le
#print axioms multiplicity_not_from_injectivity
#print axioms ESharpGenericIsP3Free
#print axioms genericBound_depends_only_on_esharpData
#print axioms cleanP3_controlled_of_generic
#print axioms actualSource_eq_generic_add_exceptions
#print axioms no_silent_double_counting
#print axioms genericPackets_nuclearAssembly
#print axioms localRepair_does_not_imply_targetClosed
#print axioms ESharpAdapter.packetBound
#print axioms ExceptionalPacketCertificate.packetBound
#print axioms allM_packet_exhaustive
#print axioms AllMExhaustiveness.packet_bound
#print axioms Gate1AAllMClosureCertificate.toTarget
#print axioms Gate1ACleanP3ClosureCertificateV95.toTarget
#print axioms gate1A_target_bridge
#print axioms commonD2_target_eq_ML4_over_H

end TwinPrimeProject.NANC.Gate1A.V95
