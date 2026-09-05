# UNIVERSAL v9.5 — GATE 1A ALL-m PACKET EXHAUSTIVENESS

New files only. The v9 / v9.1 / v9.2 / v9.4 banks are untouched.

---

## A. Regression

| item | value |
|---|---|
| HEAD at session start | `b5d73be` |
| Baseline `lake build` | 8406 jobs, 0 errors |
| Final `lake build` | **8435 jobs, 0 errors** |
| Files deleted | none |
| Existing theorems modified / weakened | none |

## B. Environment

Lean `leanprover/lean4:v4.28.0`; Mathlib at the revision pinned in `lake-manifest.json`.
All new modules are covered by the `RequestProject.+` glob in `lakefile.toml`, so a plain
`lake build` builds them.

## C. Files added

```
RequestProject/NANC/Gate1A/SafeExtensions/
    V95PacketCensus.lean
    V95WeightFirewall.lean
    V95Multiplicity.lean
    V95ESharpScope.lean
    V95Assembly.lean
    V95Closure.lean
    V95Status.lean       (#print axioms audit)
```

## D. Repository source objects located

The census is anchored to objects that **actually exist in this repository**:

* `RequestProject/CenteredCRTRootNormalForm.lean` — `CommonD2Data`,
  `EdgeDependentD2Data`, `target_eq_ML4_over_H`
* `RequestProject/VaughanPacketAlgebra.lean` — Vaughan P1/P2/P3 packets
* `RequestProject/HighP3Status.lean` — `K0R9`, `K0R10`, `R9` sparse mass
* `RequestProject/NANC/FF4Interfaces.lean` — Route-A edge variance, FF4 row,
  row diagonal, same-prime, single-frequency
* `RequestProject/NANC/CDVMixedCovarianceInterface.lean` — mixed covariance
* `RequestProject/NANC/W4Frontier/*` — Salié fibres, signed mean value
* `RequestProject/NANC/D4/Prop44PacketRouting.lean` — Prop-44 residual
* `RequestProject/NANC/Gate1BDet2/FullFaceFixedPacket.lean` — det-2 full face

## E. The packet census (§26 table)

`census : List Gate1APacket` — **19 entries**, `census_nodup` proved by `decide`.

| # | packet | source file | operator | weight dep. | mult. | target | route |
|---|---|---|---|---|---|---|---|
| 1 | `commonD2` | `CenteredCRTRootNormalForm.lean` | bilinearLargeSieve | common | 1 | `gate1A_ML4overH` | genericESharp |
| 2 | **`edgeDependentD2`** | `CenteredCRTRootNormalForm.lean` | bilinearLargeSieve | **edgeDependent** | **none** | `gate1A_ML4overH` | **unrouted** |
| 3 | `vaughanP1` | `VaughanPacketAlgebra.lean` | bilinearLargeSieve | common | 1 | `gate1A_ML4overH` | genericESharp |
| 4 | `vaughanP2` | `VaughanPacketAlgebra.lean` | bilinearLargeSieve | common | 1 | `gate1A_ML4overH` | genericESharp |
| 5 | `vaughanP3` | `VaughanPacketAlgebra.lean` | bilinearLargeSieve | finiteTemplate | none | `gate1A_ML4overH` | unrouted |
| 6 | `routeAEdgeVariance` | `NANC/FF4Interfaces.lean` | dispersionSquare | edgeDependent | none | `gate1A_ML4overH` | unrouted |
| 7 | `ff4Row` | `NANC/FF4Interfaces.lean` | fourthMomentGram | common | 1 | `globalFF4_RMD2` | unrouted |
| 8 | `ff4MixedCovariance` | `NANC/CDVMixedCovarianceInterface.lean` | fourthMomentGram | edgeDependent | none | `globalFF4_RMD2` | unrouted |
| 9 | `rowDiagonal` | `NANC/FF4Interfaces.lean` | localCorrection | common | 1 | `perFibre_KD2` | exceptional/principal |
| 10 | `samePrimeSector` | `NANC/FF4Interfaces.lean` | localCorrection | common | 1 | `perFibre_KD2` | exceptional/repeatedPrime |
| 11 | `singleFrequencyCorrection` | `NANC/FF4Interfaces.lean` | localCorrection | common | 1 | `perFibre_KD2` | exceptional/zeroFrequency |
| 12 | `k0R9FixedCell` | `HighP3Status.lean` | dispersionSquare | common | none | `gate1A_ML4overH` | unrouted |
| 13 | `k0R10FixedCell` | `HighP3Status.lean` | dispersionSquare | common | none | `gate1A_ML4overH` | unrouted |
| 14 | `r9RepeatedPrimeSparseMass` | `HighP3Status.lean` | localCorrection | common | 1 | `gate1A_ML4overH` | exceptional/repeatedPrime |
| 15 | `det2FullFace` | `NANC/Gate1BDet2/FullFaceFixedPacket.lean` | bilinearLargeSieve | common | 1 | `gate1A_ML4overH` | exceptional/properConductor |
| 16 | `w4Salie` | `NANC/W4Frontier/Salie.lean` | localCorrection | common | none | `perFibre_KD2` | unrouted |
| 17 | `w4SignedMeanValue` | `NANC/W4Frontier/CurrentFrontier.lean` | dispersionSquare | common | none | `perFibre_KD2` | unrouted |
| 18 | `prop44Residual` | `NANC/D4/Prop44PacketRouting.lean` | bilinearLargeSieve | common | none | `gate1A_ML4overH` | unrouted |
| 19 | `zeroProjective` | `SafeExtensions/ProjectiveSourceInterfaces.lean` | projectiveCrossedConvolution | common | 1 | `gate1A_ML4overH` | exceptional/projective |

Proved census facts (all by `decide`, no hand-waving):

* `census_nodup`
* `census_not_all_classified : unroutedPackets ≠ []`
* `multiplicity_not_fully_controlled : uncontrolledMultiplicity ≠ []`
* `multiple_highP3_operators_unrouted` (`3 ≤ unroutedPackets.length`)
* `firstUnclassified_is_edgeDependentD2`
* `firstUnclassified_weightDependence`
* `firstUnclassified_target`

## F. FIRST UNCLASSIFIED PACKET (§23 block)

```
PACKET ID        : edgeDependentD2
SOURCE FILE      : RequestProject/CenteredCRTRootNormalForm.lean
SOURCE OBJECT    : EdgeDependentD2Data
OPERATOR KIND    : bilinearLargeSieve
COEFFICIENT KIND : divisorBounded
WEIGHT DEPENDENCE: edgeDependent
MULTIPLICITY     : none  (uncontrolled)
TARGET           : gate1A_ML4overH
ROUTE            : unrouted
WHY BLOCKED      : `edgeDependent_not_common` proves that an edge-dependent
                   coefficient family cannot be coerced into `CommonD2Data`,
                   so the generic E-sharp adapter does not apply; and no
                   finite-template certificate (`FiniteTemplateCertificate`)
                   has been constructed for it.
```

Also unrouted: `vaughanP3`, `routeAEdgeVariance`, `ff4Row`, `ff4MixedCovariance`,
`k0R9FixedCell`, `k0R10FixedCell`, `w4Salie`, `w4SignedMeanValue`, `prop44Residual`.

## G. Weight firewall

`V95WeightFirewall.lean`

* `ofCommon`, `ofCommon_coeff_const` — a common-coefficient packet has a constant
  coefficient profile.
* `edgeDependent_not_common` — **firewall**: an edge-dependent family is provably not of
  the common form. This is what blocks packet #2.
* `finiteTemplate_norm_le`, `finiteTemplate_nuclear_cost` — a genuinely finite template
  costs only its nuclear rank.
* `FiniteTemplateCertificate`, `weight_norm_le` — the conditional route for
  finite-template packets. **No inhabitant for `vaughanP3`.**

## H. Multiplicity ledger

`V95Multiplicity.lean`

* `packetCopies`, `mem_packetCopies`, `sum_over_packetCopies`.
* `multiplicity_energy_le` — if every fibre over a physical row has at most `D`
  occurrences, assembling occurrences into rows costs at most a factor `D` in energy.
* `PacketMultiplicityCertificate` + `.energy_le`.
* `multiplicity_not_from_injectivity` — **negative result**: multiplicity may *not* be
  inferred from geometric injectivity; a countermodel is supplied.

## I. E-sharp scope and P3-freeness

`V95ESharpScope.lean`

* `ESharpRow`, `CleanP3Row extends ESharpRow`, `forgetP3`, `ESharpSource`,
  `CleanP3Source`, `CleanP3Source.toESharp`, `GenericBPPBound`.
* `ESharpGenericIsP3Free` — the generic E-sharp bound applies to a clean-P3 source
  through the forgetful map, using no P3 field. This is **structural**, not a text search:
  `ESharpRow` has no P3 field at all.
* `genericBound_depends_only_on_esharpData`, `forgetP3_forgets`,
  `cleanP3_controlled_of_generic`.

`GenericBPPBound` is deliberately **uninhabited**: the generic analytic bound is an open
input.

## J. Assembly

`V95Assembly.lean`

* `actualSource_eq_generic_add_exceptions` — exact finite decomposition of the actual
  source into generic part plus named exceptions.
* `no_silent_double_counting` — the decomposition is a partition; nothing is counted twice.
* `genericPackets_nuclearAssembly` — the generic packets assemble with nuclear cost.
* `LocalRepairComplete`, `PacketTargetClosed`,
  `localRepair_does_not_imply_targetClosed` — **firewall**: completing every local repair
  does *not* imply the packet target is closed. This forbids the usual silent upgrade.

## K. Closure compilers (all certificates NOT CONSTRUCTED)

`V95Closure.lean`

* `ESharpAdapter` + `.packetBound`; `ExceptionalPacketCertificate` + `.packetBound`.
* `PacketClassified`; **`allM_packet_exhaustive`** — if every packet carries either a
  generic E-sharp adapter or an exceptional certificate, every packet meets the Gate 1A
  target. The classification is a total function, so no unclassified packet is
  representable *inside the hypothesis*; the census shows the hypothesis is **not**
  discharged for the actual source.
* `SourceExactPacketDictionary`, `contribution`, `actualSource_eq_sum_contribution`.
* `AllMExhaustiveness`, `packet_bound`.
* `Gate1AAllMClosureCertificate` + `.toTarget`.
* `Gate1ACleanP3ClosureCertificateV95` + `.toTarget`.
* `gate1A_target_bridge`, `commonD2_target_eq_ML4_over_H` — the bridge to the repository's
  own `target_eq_ML4_over_H`.

Uninhabited structures (machine-visible open fields):
`SourceExactPacketDictionary`, `GenericBPPBound`, `AllMExhaustiveness`,
`Gate1AAllMClosureCertificate`, `Gate1ACleanP3ClosureCertificateV95`.

## L. Axiom audit

`V95Status.lean` — `#print axioms` on the public v9.5 theorems returns only
`propext`, `Classical.choice`, `Quot.sound`. **No user axiom.**

## M. Trust audit

```
rg -n "^\s*(sorry|admit|axiom |opaque |unsafe )|native_decide|@\[implemented_by" --type lean \
   RequestProject Gate1A Gate1B Universal UniversalV8 Gate04Root
```
Only prose / doc-comment matches. No code-level trust token anywhere.

## N. Final status

```
FINAL VERDICT: ARISTOTLE_GATE1A_V9_5_ALLM_BANK_PARTIAL

PACKET CENSUS               : 19 ENTRIES, nodup PROVED
ALL-m EXHAUSTIVENESS        : NOT ESTABLISHED (unroutedPackets ≠ [] proved)
FIRST UNCLASSIFIED PACKET   : edgeDependentD2
MULTIPLICITY                : NOT FULLY CONTROLLED (proved)
CLOSURE COMPILERS           : PROVED
CLOSURE CERTIFICATES        : NOT CONSTRUCTED
GATE 1A CLEAN-P3 / ALL-m    : OPEN
GATE 1B                     : UNCHANGED
FULL TYPE II                : NOT DECLARED / NOT INFERRED
TWIN PRIMES                 : NOT DECLARED / NOT INFERRED
```

## O. Next mathematical action

Construct, or refute, a `FiniteTemplateCertificate` for `EdgeDependentD2Data`, since that
is the single first machine-visible blocker in the census.
