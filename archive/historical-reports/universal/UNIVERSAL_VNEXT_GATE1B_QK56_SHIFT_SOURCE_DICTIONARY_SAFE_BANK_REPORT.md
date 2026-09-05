# UNIVERSAL V13 — GATE 1B QK5/6 CHARACTER-GRAM REPAIR / SHIFTED TT\* SOURCE INTERFACE / SOURCE-EXACT HIGH-`p₃` PACKET DICTIONARY / FM → GATE FINITE COMPILER

**Append-only safe bank.  No previously banked file was modified.**

Verdict: `ARISTOTLE_VNEXT_QK56_SHIFT_SOURCE_SAFE_BANK_PARTIAL`

---

## A. Baseline regression

`lake build` (all six libraries, 8593 jobs) — **PASS**, before and after the V13
additions.  V8.x / V9.x / V10 / V11 / V12 banks untouched.

## B. Same-`q` character Gram (exact algebra)

`Gate1B/SafeAlgebra/SameQCharacterGramDiagonalization.lean`

| object | status |
|---|---|
| `gramKernel`, `sameQGram`, `sameQGramDiag`, `sameQGramOff` | definitions |
| `sameQGram_split` — exact diagonal/off-diagonal decomposition | PROVED |
| `sameQGramDiag_eq` — diagonal = `|Ch|⁻² K(1) ∑ |c(χ)|²` | PROVED |
| `sameQGramDiag_eq_zero_of_centred` | PROVED |
| `sameQGramDiag_ne_zero_of_flat_kernel` (Counterguard A) | PROVED |

An earlier concrete two-element countermodel was **withdrawn as false**
(diagonal and off-diagonal both equal `1/2` there) and replaced by the two
abstract theorems above.

## C. Product-residue character kernel and its spectrum

`Gate1B/SafeAlgebra/ProductResidueCharacterKernel.lean`

`productResidueWeight`, `weightTransform`, `productKernel`, `productResidueMean`,
`centredKernel`, `centredEigenvalue` with

* `kernel_eq_sum_productResidue`, `productKernel_one` — PROVED;
* `centredKernel_fourier_eq` (eigenvalues `|G|(g(r) − mean)`) — PROVED;
* `centredKernel_convolution_eigen`, `centredSpectralRadius_isGreatest` — PROVED.

## D. Same-`q` diagonal router

`Gate1B/SafeExtensions/SameQDiagonalRouter.lean`

* `SameQDiagonalResidueEnergyInput` — **UNINHABITED** interface (no repository
  object has the same source sequence and target);
* `sameQGramDiag_bound_of_input` — PROVED implication;
* non-vacuity guard — PROVED.

## E. Modular-hyperbola discrepancy

`Gate1B/SafeExtensions/ModularHyperbolaDiscrepancy.lean`

* `ModularHyperbolaDiscrepancyInput` — **UNINHABITED**; no numerical value such
  as `q^{1/2+o(1)}` is inserted anywhere;
* `sum_chi_eq_zero_of_ne_one`, `centredKernel_norm_le_of_discrepancy` (`≤ |G|Δ`
  at non-principal characters), `sameQGramOff_bound_of_kernel_bound`,
  `sameQGramOff_bound_of_discrepancy` — PROVED.

## F. Same-`q` capacity arithmetic (CAPACITY ONLY)

`Gate1B/SafeAlgebra/SameQDiscrepancyCapacity.lean`

* `discrepancy_relative_exponent` : `q^{3/2}/((Q/Y)(Q/Y)) = Y²/Q^{1/2}` — PROVED;
* `relative_exponent_in_X` : `= X^{2/9 − ω/2}` — PROVED;
* `sameQ_capacity_margin` : `ω ≥ 13/18 ⟹ margin ≤ −5/36` — PROVED;
* `sameQ_capacity_margin_neg` — PROVED.

These are exponent bookkeeping identities under stated abstract assumptions.
**They do not supply the discrepancy input** and conclude no analytic theorem.

## G. Cross-`q` Θ fibre counting

`Gate1B/SafeAlgebra/CrossQThetaFibre.lean`

* `card_residue_class_in_interval` : `#{b ∈ [x, x+L) : b ≡ a (q)} ≤ L/q + 1` — PROVED;
* `card_residue_class_in_interval_rat` : rational form `≤ 1 + L/q` — PROVED;
* `maxThetaFibre_le` : product fibre bound — PROVED.

## H. Cross-`q` Θ spread

`Gate1B/SafeExtensions/CrossQThetaSpread.lean`

* `crossL1`, `crossL2` definitions;
* `crossL2_sq_le_maxFibre_mul_l1`, `crossL1_le_states_mul_maxFibre`,
  `crossL2_le_crossL1` — PROVED;
* `crossQ_spread_criterion` : `‖A‖_∞ ≤ F` and `F ≤ ρ²‖A‖₁` give `‖A‖₂ ≤ ρ‖A‖₁` — PROVED;
* `ProductMultiplicityCertificate`, `CrossQThetaSourceMassCertificate` —
  interfaces, **never inhabited for the actual source**;
* `crossQThetaSourceMassCertificate_of_multiplicity` — PROVED bridge;
* non-vacuity guard — PROVED.

## I. QK5/6 conditional closure

`Gate1B/SafeExtensions/QK56ConditionalClosure.lean`

* `QK56V13SourceDictionary` — literal routing dictionary (principal character,
  parent = same-`q` Gram + cross-`q` remainder, cross-`q` remainder dominated by
  its `ℓ²` source mass).  Carries **no** estimate;
* `qk56_full_covariance_of_v13_inputs` — PROVED CONDITIONAL: dictionary +
  UNINHABITED diagonal energy input + UNINHABITED discrepancy input +
  UNINHABITED spread certificate + deterministic pins ⟹ project-local
  `TwinPrimeProject.Gate1BV11.QK56FullCovarianceBound`;
* `v13_to_v10AnalyticLeaves` — PROVED bridge to the four V10 analytic leaves
  (`V11AnalyticLeafBundle`), **no type mismatch**;
* guards: neither conclusion is automatic.

## J. Literal shifted TT\* source and shift-source-linked moment

`Gate1B/SafeExtensions/ShiftTTStarLiteralSource.lean`

* `edgeTuple`, `ShiftTTStarLiteralSourceCertificate` — non-circular source
  dictionary (allowed multiplier tuples = edge tuples of prescribed corner
  four-cycles, edge map injective).  **Never inhabited here**;
* `shiftSourceLinkedCharacterMoment` — built on the *proved* four-cycle
  discriminant `fourCycleDisc`, summed over physical cycles, never over a
  Cartesian product of four free multipliers;
* `shiftMult4CharacterMoment_eq_linked` — PROVED exact identity;
* `ShiftSourceLinkedCharacterBound` — **UNINHABITED** analytic interface, with
  non-vacuity guard.

## K. SHAPE metadata

Same module: `DeterminantCharacterShape`, `MonomialCharacterShape`,
`ReciprocalMultilinearShape` are metadata predicates only.

* `monomialShape_of_determinantShape`, `fourCycle_det_determinantShape` — PROVED;
* `fourCycle_trace_not_determinantShape` — PROVED counterguard (shape metadata
  does not transport from determinant to trace).

## L. Source-exact weighted high-`p₃` packet dictionary

`Universal/SafeExtensions/SourceExactHighP3PacketDictionary.lean`

* `WeightType` = `common | finiteTemplate | edgeDependent`;
* `HighP3Packet`, `HighP3Packet.honest`,
  `SourceExactWeightedHighP3PacketDictionary` — dictionary **type**; only the
  empty dictionary is exhibited, no real high-`p₃` inhabitant;
* `common_weight_constant`, `edgeDependent_not_constant` — PROVED.

## M. Weight-dependence compiler

`Universal/SafeAlgebra/WeightDependenceCompiler.lean`

* `packetSum_common` (constant weight factors out) — PROVED;
* `packetSum_finiteTemplate` (split into `#template` common-weight sums) — PROVED;
* `packetSum_edgeDependent_le` (triangle bound only) — PROVED;
* `edgeDependent_not_absorbed_by_common` — PROVED counterguard.

## N. FM → Gate coordinate census (SOURCE-BLOCKED)

`Gate1B/SafeExtensions/FMToGateCoordinateCensus.lean`

* `FMToGateCoordinateCensus` requires **both** the absent
  `RealFordGrammarCertificate` and a real packet dictionary;
* `census_slots_generated` — PROVED (the only content the census transports);
* `census_requires_fordProvenance`, `census_requires_packetDictionary` — PROVED
  source blocks.

## O. Counterguards A–H

`Gate1B/SafeExtensions/V13Counterguards.lean` — all kernel-checked:

A same-`q` diagonal not automatically negligible · B discrepancy interface not
vacuous · C `ℓ² = ℓ¹` possible, so `ℓ² ≤ ℓ¹` is not a saving · D edge-dependent
weights not absorbed by a common-weight theorem · E four Cauchy copies ≠ four
independent physical parameters · F conditional compiler ≠ closure · G census
source-blocked · H SHAPE metadata not transportable.

## P. Axiom audit

`Gate1B/SafeExtensions/V13QK56ShiftSourceStatus.lean` — 52 `#print axioms`
checks.  Every principal V13 theorem depends only on
`[propext, Classical.choice, Quot.sound]` (a few on `[propext]` alone).
No `sorry`, no `admit`, no user `axiom`, no `opaque`, no `unsafe`, no
`native_decide`, no `@[implemented_by]`.

## Q. Gate1B research status

```
SAME-q ALGEBRA:                    PROVED (split, diagonal identity, spectrum)
MODULAR-HYPERBOLA DISCREPANCY:     UNINHABITED
SAME-q CAPACITY:                   X^(−5/36) CONDITIONAL BOOKKEEPING ONLY
CROSS-q FIBRE:                     PROVED FINITE
CROSS-q SPREAD CERTIFICATE:        UNINHABITED (criterion PROVED)
QK56 PARENT:                       CONDITIONAL (implication PROVED)
SHIFT TT* LITERAL SOURCE:          UNINHABITED
SHIFT-SOURCE-LINKED MOMENT BOUND:  UNINHABITED
HIGH-P3 PACKET DICTIONARY:         UNINHABITED (type only)
WEIGHT DEPENDENCE COMPILER:        PROVED
FM→GATE CENSUS:                    SOURCE-BLOCKED
V10 ANALYTIC LEAF BRIDGE:          PROVED (no type mismatch)
GATE1B:                            OPEN
TWIN PRIMES:                       NOT PROVED
```

FIRST FORMAL BLOCKER:
`Gate1B.SafeExtensions.ModularHyperbolaDiscrepancyInput` (uninhabited).

FIRST GATE1B ANALYTIC OPEN: `SHIFT-SOURCE-LINKED-CHAR45`.

FIRST DOWNSTREAM SOURCE OPEN:
`SOURCE-EXACT-WEIGHTED-HIGHP3-PACKET-DICTIONARY45`.
