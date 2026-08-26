# UNIVERSAL v9.4 — GATE 1A CORRECTED BPP BANK

New files only. The v9 / v9.1 / v9.2 banks are untouched.

---

## A. Regression / environment

Lean `v4.28.0`, pinned Mathlib, final `lake build` = 8435 jobs, 0 errors.
No deletion, no weakening, no modification of earlier proofs.

## B. Files added

```
RequestProject/NANC/Gate1A/SafeExtensions/
    PrimeParticipationFinite.lean
    BPPFamilyEnergy.lean
    BPPBudget.lean
    V94Retractions.lean
    PositiveRowEnlargement.lean
    PBUnitRepair.lean
    SmoothRSourceEnvelope.lean
    ProjectiveClosure.lean
    QuotientRecombinationInterfaces.lean
    FixedStateExclusion.lean
    AllMExhaustiveness.lean
    Gate1AClosureCertificates.lean
    AnalyticInterfacesV94.lean   (comments only — zero declarations)
    V94Status.lean               (#print axioms audit)
```

## C. Prime participation — finite consequences only

`PrimeParticipationFinite.lean`

* `ParticipationEnvelope` — structure carrying the participation plateau data.
* `participation_of_plateau`, `sup_le_envelope` — finite consequences of the plateau.
* `PrimeParticipationCertificate` — the analytic input as a **certificate field**, never
  as an axiom.

`BPPFamilyEnergy.lean`

* `rowMass`, `totalAbsEnergy`.
* `envelopeMass_le_of_participation`, `familyEnergy_of_participation`,
  `PrimeParticipationCertificate.familyEnergy` — the family-energy bound that follows
  *from* a certificate, with no analytic content proved.

## D. Corrected budget arithmetic (exact ℚ)

`BPPBudget.lean`, frozen exponents `mExp = 1/3`, `hExp`.

| theorem | value |
|---|---|
| `bpp_gate_margin_V1` | `1 / 72` |
| `bpp_gate_margin_V2` | `1 / 24` |
| `bpp_gate_margin_V3` | `1 / 32` |
| `bpp_gate_margins_pos` | all three are strictly positive |
| `obsolete_margins` | the retracted ledger values `1/12`, `1/9`, `5/48` |
| `ledgers_not_interchangeable` | corrected ≠ obsolete, proved |

Further exact ℚ/ℝ results in the same file:

* `recombinationError_U2_budget` — the recombination error meets the `U2` budget.
* `errorMarginU2_vertices`, `errorMarginU1_fails_at_V2` — the `U1` error margin **fails**
  at `V2`; only the `U2` margin survives. Recorded as a negative result.
* `pb_oneSided_budget_eq_one` — the one-sided PB budget is exactly `1`.
* `outerFourCycle_rootDepth`, `oneRoot_energy_to_operator` — one-root energy converts to an
  operator bound with the explicit rate `R^{-1/4}`.

All conditional. No analytic closure is claimed.

## E. Retractions and countermodels

`V94Retractions.lean`

* `StepStatus`, `directR1WeightedFamilyPromotion = .RetractedAsClosureStep`.
* `directR1WeightedFamilyPromotion_retracted`, `..._not_proved`.
* Finite countermodel `famRow` (2×2 identity family): `famRow_pairwise_orthogonal`,
  `famRow_coherent_energy`, `famRow_natural_energy`, and hence
  `directR1_promotion_countermodel` plus `directR1_promotion_countermodel_general`.

## F. Positive row enlargement

`PositiveRowEnlargement.lean`

* `PositiveRowEnlargement`, `cleanRows ⊆ esharpRows`.
* `cleanP3_energy_le_esharp_energy`, `cleanP3_energy_le_of_esharp_bound` — the clean-P3
  energy is dominated by the E-sharp energy, so an E-sharp bound transfers.
* `rowEnlargement_not_reversible` — the converse fails; the enlargement is one-way.

## G. PB unit repair

`PBUnitRepair.lean`

* `klSum`, `klSum_unit_scaling` — the Kloosterman-type finite sum is invariant under unit
  scaling.
* `pbQFrequency_unitRepair`, `pbQFrequency_normPreserved`, `pbQFrequency_card_preserved`.
* `pbQFrequency_repair_not_identity` — the repair is a genuine relabelling, not the
  identity; recorded so the two coordinates are never conflated.

## H. Smooth-R source envelope

`SmoothRSourceEnvelope.lean`

* `SmoothRSourceEnvelope`, `profile_of_coeff_ne`, `coeff_lipschitz`.
* `commonSource_not_rIndependent` — **firewall**: the common source is *not* independent
  of `r`; an `r`-independent treatment is refuted by countermodel.
* `SmoothEnvelopeCertificate` + `.variation_bound` — the variation bound as a conditional
  consequence of a certificate.

## I. Projective closure frame

`ProjectiveClosure.lean`

* `deltaOut`, `deltaOut_self`, `deltaOut_antisymm`.
* `outerProjectiveCollision_iff_dvd_deltaOut` — exact collision criterion.
* `projectiveCollision_unitEquiv`.
* `projAxis` and the **exact axis-sum correlation identity**
  `projAxis_correlation : … = s² · 1_{U = U'} − s`,
  with the special cases `projAxis_zero_zero`, `projAxis_axis_U`, `projAxis_axis_V`.
  This is an **exact finite orthogonality identity, not a Weil bound**; it is stated as
  such so that no square-root cancellation is silently imported.

## J. Quotient recombination interfaces

`QuotientRecombinationInterfaces.lean`

* `packetEnergy`, `packetEnergy_nonneg`, `packetEnergy_split`.
* `QuotientRecombinationCertificate` + `source_energy_le`
  (`≤ 2 * mainBound + 2 * errorBound`).
* `packetEnergy_split_factor_needed` — the factor `2` is necessary; a lossless split is
  refuted.

## K. Fixed-state exclusion

`FixedStateExclusion.lean`

* `FixedStateExclusionCertificate`, `excluded`, `excluded_card_le`, `exists_admissible`.
* `rDependent_obstruction_excludes_everything` — if the obstruction is allowed to be
  `r`-dependent, the exclusion set is everything. This bounds the scope of the exclusion
  argument.

## L. Sector table and closure certificates

`AllMExhaustiveness.lean`

* `Gate1ACleanP3Sector`, `SectorStatus`, `sectorStatus`.
* `sectorStatus_not_all_banked` — **proved**: the table is not fully banked.
* `genericFullConductor_analyticOpen`, `projective_sourceInterfaceOpen`.
* `Gate1AFrozenExceptionBank`, `AllMSourceExhaustivenessCertificate` + `total_le_budget`.
  The certificate is **NOT CONSTRUCTED**.

`Gate1AClosureCertificates.lean`

* `FinalBudgetMet`, `SectorEnergyCertificate`, `Gate1ACleanP3ClosureCertificate`,
  `Gate1ACleanP3ClosureCertificate.toFinalBudget`.
  Compiler proved; certificate **NOT CONSTRUCTED**.

## M. Comments-only analytic interfaces

`AnalyticInterfacesV94.lean` contains **zero declarations**. It documents, in prose only:
`OmegaResidueMass1A`, `RootDefectSourceFactor1A`, `DefectMultiplierConcrete1A`,
`ZeroProjSourceSplice1A`, `FQ_S1S2S3_Cleanroom1A`, `Gate1ACleanP3Closed`.
No inhabitants.

## N. Axiom audit

`V94Status.lean` — `#print axioms` on the public v9.4 theorems: only `propext`,
`Classical.choice`, `Quot.sound`. **No user axiom.**

## O. Final status

```
FINAL VERDICT: ARISTOTLE_GATE1A_V9_4_BANK_PARTIAL

CORRECTED BPP MARGINS      : PROVED (1/72, 1/24, 1/32)
OBSOLETE MARGINS           : RETRACTED (1/12, 1/9, 5/48)
DIRECT R1 PROMOTION        : RETRACTED with countermodel
PROJECTIVE AXIS IDENTITY   : PROVED EXACT (not a Weil bound)
ALL CLOSURE CERTIFICATES   : NOT CONSTRUCTED
GATE 1A CLEAN-P3           : OPEN
GATE 1B                    : UNCHANGED
FULL TYPE II / TWIN PRIMES : NOT DECLARED
```
