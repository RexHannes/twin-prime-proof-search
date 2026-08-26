# UNIVERSAL v9.6 — Gate 1A actual-source inhabitance report

FINAL VERDICT: **ARISTOTLE_GATE1A_V9_6_ACTUAL_SOURCE_PARTIAL**

---

## A. Regression

* HEAD at start: `0d78ad7563b455048299b0754c554f6a7732c721`.
* Toolchain: `leanprover/lean4:v4.28.0`; Mathlib at the revision pinned in
  `lake-manifest.json` (`v4.28.0` tag of `mathlib4`).
* Baseline `lake build`: **Build completed successfully (8435 jobs), 0 errors**.
  Only pre-existing warning: `manifest out of date: source kind (git/path) of
  dependency 'mathlib' changed`, plus pre-existing style-linter warnings in
  v9–v9.5 files.
* Trust-token scan (`sorry`, `admit`, `axiom`, `opaque`, `unsafe`,
  `native_decide`, `implemented_by`) over all Lean libraries: **only prose and
  doc-comment matches**, no occurrence in code.
* No previous file was edited or deleted. v9.6 is **new files only**:
  five modules under `RequestProject/NANC/Gate1A/SafeExtensions/`.

## B. Prior bank (kept, not reopened)

v9 post-determinant finite algebra, corrected fixed-quotient CRT, authoritative
S1 normalization, weighted root-fibre theorem, finite defect multiplier,
root-defect finite compiler, projective crossed convolution, positive
Clean-P3 → `E♯` row enlargement, BPP finite compiler, the retraction of the
direct `R^(-1)` moving-family route, the controlling BPP ledger
(`R^(-1/2)` family energy, `R^(-1/4)` after one relative root), the vertex
arithmetic `V1 = 1/72`, `V2 = 1/24`, `V3 = 1/32`, the `U^(-2)` recombination
error arithmetic, and the separation of Clean-P3 from all-`m` closure: all
untouched and still building.

## C. Authoritative source paths inspected

| object | path |
|---|---|
| `CommonD2Data`, `CommonD2Data.edgeSum`, `LargeSieveTarget` | `RequestProject/CenteredCRTRootNormalForm.lean` |
| `EdgeDependentD2Data` | `RequestProject/CenteredCRTRootNormalForm.lean` |
| `VaughanP1`, `VaughanP2`, `centeredP3` | `RequestProject/VaughanPacketAlgebra.lean` |
| `FF4Hypothesis`, `FF4MixHypothesis`, `RouteAVarianceHypothesis`, `RowDiagonalHypothesis`, `SamePrimeSectorHypothesis`, `SingleFrequencyCorrectionHypothesis` | `RequestProject/NANC/FF4Interfaces.lean` |
| `CDVMixedCovarianceInput` | `RequestProject/NANC/CDVMixedCovarianceInterface.lean` |
| `K0R9FixedCellDistributionInput`, `K0R10FixedCellDistributionInput`, `R9RepeatedPrimeSparseMassInput` | `RequestProject/HighP3Status.lean` |
| `Gate1BDet2.FullFace.lambdaRouted` | `RequestProject/NANC/Gate1BDet2/FullFaceFixedPacket.lean` |
| `salieLargeWFibres5And8`, `genericSignedMeanValue` | `RequestProject/NANC/W4Frontier/Salie.lean`, `.../CurrentFrontier.lean` |
| `D4.ResidualPacket` | `RequestProject/NANC/D4/Prop44PacketRouting.lean` |
| `V91.projRow` | `RequestProject/NANC/Gate1A/SafeExtensions/ProjectiveSourceInterfaces.lean` |

Every one of these is `#check`ed by fully qualified name in
`V96SourceLocators.lean`, so the census provenance is now compile-time checked:
if a declaration is renamed or removed, the module stops building.

## D. Actual `W_D` / `W_{D,e}`

**ACTUAL_WEIGHT_ARBITRARY_EDGE_DEPENDENT.**

Source path:

```
RequestProject/CenteredCRTRootNormalForm.lean
  :: TwinPrimeProject.CenteredCRTRoot.EdgeDependentD2Data.coeff
     coeff : Edge → Pair → Harm → ℂ
```

The structure carries **no** field relating the coefficient families of two
edges: no common-weight equation, no finite-template equation, no smooth
parameter `Φ(t/D, θ_e)`, no compactness and no smoothness. This is made
machine-visible by `edgeData_coeff`: every function `Edge → Pair → Harm → ℂ`
whatsoever is the coefficient field of an actual `EdgeDependentD2Data`.

Recorded in Lean as `actualWeightVerdict = ActualWeightVerdict.arbitraryEdgeDependent`
with `actualWeightSourcePath`.

Secondary source fact: the repository defines `edgeSum`, `lhs`, `energy` and
`LargeSieveTarget` **only** for `CommonD2Data`. `EdgeDependentD2Data` has no
target functional at all, so it is *data only*
(`edgeDependentD2_is_dataOnly`).

## E. Edge-dependent resolution

**EDGEDEPENDENT_D2_NOT_ESharp_ADMISSIBLE** (Section 9 branch taken).

* `template_count_ge_of_linearIndependent` — if the edge weights are linearly
  independent and each decomposes over `n` common templates, then
  `#Edge ≤ n`.
* `deltaEdgeData` — an actual `EdgeDependentD2Data` whose `N` edges carry the
  `N` orthogonal delta directions; `deltaEdgeData_linearIndependent` proves
  independence.
* `deltaEdgeData_no_small_template` and
  `finiteTemplateCertificate_delta_card` — any finite-template decomposition,
  and in particular any inhabitant of the existing `FiniteTemplateCertificate`
  for these weights, uses at least `N` templates.

So no `X^{o(1)}` common-template reduction follows from functional analysis
alone. This is a death certificate for the common-template route on arbitrary
edge dependence, not a repairable gap.

Positive direction: the common branch is inhabited, and only it —
`commonFiniteTemplate` gives a one-template, unit-nuclear-cost certificate for
a common weight (`commonFiniteTemplate_cost`).

## F. Actual packet census (source-kind refinement)

The v9.5 census of 19 packets is kept as is. v9.6 adds, for each packet, the
*exact declaration* it points to (`sourceDecl`) and the *kind of object* that
declaration is (`sourceKind`):

| kind | packets |
|---|---|
| defined operator **with** a defined target functional | `commonD2` |
| defined operator, no target functional | `vaughanP1`, `vaughanP2`, `vaughanP3`, `det2FullFace`, `zeroProjective` |
| data only (no functional at all) | `edgeDependentD2` |
| `Prop`-carrying interface | `routeAEdgeVariance`, `ff4Row`, `ff4MixedCovariance`, `rowDiagonal`, `samePrimeSector`, `singleFrequencyCorrection`, `k0R9FixedCell`, `k0R10FixedCell`, `r9RepeatedPrimeSparseMass` |
| status-ledger entry | `w4Salie`, `w4SignedMeanValue` |
| predicate on exponent data | `prop44Residual` |

Proved by decision procedure:

* `commonD2_is_the_only_dictionary_ready_packet` — exactly one packet has a
  defined operator together with a defined target;
* `interfaceOnlyPackets_length = 12` and `majority_of_packets_are_interfaces`;
* `first_non_dictionary_ready = some edgeDependentD2`.

Consequence: `SourceExactPacketDictionary.coversActualSource` cannot be
inhabited over the census, because twelve packets have **no contribution
vector to put into the sum** — their source is an externally supplied
proposition, not an operator.

## G. Packet multiplicity

* Actual common-D2 dictionary: exact multiplicity **1** per physical row,
  proved (`commonD2Multiplicity`, `commonD2Multiplicity_exact`), reusing the
  v9.5 `PacketMultiplicityCertificate`.
* All interface-only packets: **PACKET_MULTIPLICITY_SOURCE_MISSING** — the
  source exposes no decomposition measure (no ordered-factorization labels, no
  Heath–Brown/Vaughan labels, no Mellin or dyadic cell structure) on which a
  fibre could even be defined.

Nothing is inferred from geometric injectivity; the v9.5 firewall
`multiplicity_not_from_injectivity` still applies.

## H. Normalization

The three scales are kept apart exactly as in v9.5 (`TargetNormalization`:
`perFibre_KD2`, `globalFF4_RMD2`, `gate1A_ML4overH`). The only bridge used in
v9.6 is the repository's own
`CommonD2Data.target_eq_ML4_over_H` (`M L² D = M L⁴ / H` under `D H = L²`),
re-exported in v9.5 as `commonD2_target_eq_ML4_over_H`. No numerically stronger
target was substituted for a source arrow.

## I. Generic `E♯` adapters

`esharpAdapter_nonempty_iff` (new): for a non-negative generic target, an
`ESharpAdapter` for a packet exists **iff** the packet already satisfies the
bound. The adapter is therefore an exact repackaging of an estimate; it never
creates one. Every adapter used in v9.6 is built from an explicitly supplied
per-packet bound hypothesis, never from an axiom.

P3-free audit: the adapters constructed here mention only norms of packet
contributions; no `m = π₁π₂π₃`, no `π ∣ m` and no clean-P3 field occurs. The
v9.5 structural theorem `ESharpGenericIsP3Free` is unchanged.
**GENERIC_ENGINE_P3_FREE: YES.**

## J. Exceptional adapters

Unchanged from v9.5: `rowDiagonal` (principal), `samePrimeSector` /
`r9RepeatedPrimeSparseMass` (repeated prime), `singleFrequencyCorrection`
(zero frequency), `det2FullFace` (proper conductor), `zeroProjective`
(projective) are routed; the remaining sectors are not. v9.6 adds no new
exceptional certificate, and the v9.5 firewall
`localRepair_does_not_imply_targetClosed` still forbids accepting a local
identity in place of a weighted global bound.

## K. Source partition identity

**PROVED for the actual common-D2 source**:

```
commonD2_source_partition :
  commonD2Source d = ∑ p, (commonD2Dictionary d target).contribution p
```

with `commonD2Source d e = d.edgeSum e`, one packet per `(pair, harmonic)`,
literal coefficient `d.coeff a h`, literal base packet `e ↦ d.phase e a h`, and
exactly one analytic copy. The dictionary is **pinned**:
`commonD2Dictionary_pins : PinsSource (commonD2Dictionary d target) (commonD2Source d)`.

**NOT proved for the full census** — see F.

## L. Clean-P3 certificate construction

`cleanP3Certificate_of_bound` inhabits the existing
`Gate1ACleanP3ClosureCertificateV95` from a supplied `E♯` bound, an exception
bank and a budget inequality; `cleanP3Certificate_physical_target` instantiates
the target at the physical `M L⁴ / H`.

Audit finding attached to it: `cleanP3Certificate_self_referential` shows the
type is inhabited for *every* non-negative energy if one is allowed to choose
the target to be the quantity being bounded. Hence **inhabiting the type is not
closure**; the content is entirely in supplying the generic bound and the
physical target from outside. Status: **CONSTRUCTED CONDITIONALLY.**

## M. All-`m` exhaustiveness construction

`AllMSourceExhaustivenessCertificate` (repository name `AllMExhaustiveness`) is
constructed only for the actual common-D2 dictionary and only under an explicit
per-packet bound hypothesis (`commonD2Exhaustiveness`). Over the full census it
is **NOT CONSTRUCTED**: twelve packets are unclassifiable because they have no
source operator.

## N. All-`m` closure certificate construction

`commonD2Closure : Gate1AAllMClosureCertificate (d.Pair × d.Harm) (d.Edge → ℂ)`
is constructed for the actual common-D2 source under the same hypothesis, and
compiles to `commonD2Closure_bound`:

```
‖commonD2Source d‖ ≤ (#(Pair × Harm)) * T .
```

Honesty record `commonD2Closure_finalTarget_is_trivial`: the final target is
exactly the triangle-inequality target `#packets · T`. The compiler performs no
cancellation, so this reaches the Gate 1A target only if the supplied
per-packet bound already has strength `target / #packets`. Status:
**CONSTRUCTED CONDITIONALLY, TRIVIAL TARGET.**

## O. First missing actual field

Two are recorded, in dependency order.

1. **Packet contribution for the non-operator packets.**
   `SourceExactPacketDictionary.basePacket` / `coversActualSource` cannot be
   filled for the twelve interface-only packets. First offender in census
   order: `edgeDependentD2`.
   * Exact source file: `RequestProject/CenteredCRTRootNormalForm.lean`.
   * Exact required object: an `edgeSum`-style functional on
     `EdgeDependentD2Data` together with the equation expressing the Gate 1A
     source as a sum of such contributions.
2. **Analytic pinning of the generic engine.**
   `GenericBPPBound.normalizedEnergy` is a free field, so the structure has a
   vacuous inhabitant (`genericBPPBound_vacuously_inhabited`) and controls no
   other functional (`genericBPP_says_nothing_about_other_energy`). What is
   missing is the equation pinning `normalizedEnergy` to the actual Gate 1A
   `E♯` energy, together with the bound at target `M H L⁴ X^{o(1)}`.

The same *free-field* pattern is what makes `RootDefectSourceFactorization` and
`ZeroProjectiveSourceFactorization` inhabitable canonically (Section P below):
in all four cases the analytic content lives in a pinning equation, not in the
inhabitance of the structure.

## P. Secondary open fields now settled

* `RootDefectSourceFactorization`: **canonical inhabitant constructed**
  (`canonicalRootDefect`), with the rigidity theorem
  `rootDefect_hardParent_unique` showing the factorization hypothesis
  determines `hardParent`; pinning to the actual Gate hard parent remains open.
* `ZeroProjectiveSourceFactorization`: **canonical inhabitant constructed**
  (`canonicalZeroProjective`) with the trivial fibre multiplicity
  `#(Row × Graph)` (`canonicalZeroProjective_fibreCard`); an `X^{o(1)}` fibre
  bound and the pinning equation remain open.

## Q. Axiom audit

`#print axioms` in `V96Status.lean` covers all thirty-four public v9.6
theorems. Every one depends only on `propext`, `Classical.choice`,
`Quot.sound`, or on no axioms at all. **No user axiom exists in this bank**,
and none was added for Bernstein, primes in short intervals, BPP
participation, smooth finite-template approximation, `X^{o(1)}` divisor
multiplicity, Ford–Maynard, or any Kloosterman theorem.

## R. Final scope

* Gate 1A clean-P3: **analytically conditional** — the compiler is proved and
  now inhabitable, but only from a supplied `E♯` bound.
* Gate 1A all-`m`: **source-exhaustiveness open** — twelve census packets have
  no source operator; the actual all-`m` source is not covered.
* Gate 1B: **unchanged**.
* Full Type II: **not inferred**. Twin primes: **not inferred**.

Next mathematical action: define the missing contribution functional on
`EdgeDependentD2Data` (an `edgeSum`-style map plus its Gate 1A target) so that
the edge-dependent packet acquires a contribution vector at all — without it,
neither routing nor refutation of that packet can be expressed in the
dictionary.
