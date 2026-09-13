# TWIN GATE1B / R11 — reconciliation of the old formal frontier with the current analytic frontier

Append-only continuation. Gate1A was not touched. No pre-existing Gate1B/R11 declaration was
edited, renamed, weakened or deleted. Every new theorem is kernel-proved with `#print axioms`
restricted to `propext`, `Classical.choice`, `Quot.sound`; there is no `sorry`, no custom
`axiom`, no `native_decide`, no `@[implemented_by]`, no `unsafe` and no `opaque` in the new
directory.

## Files added — all under `Gate1B/R11/Frontier/Latest/`

| module | content |
|---|---|
| `GlobalCoreAggregation.lean` | `R_j = ∑_M g(M−2) H_j(M)`: linearity in the rows and in the source, exact mask split with disjointness, off-support vanishing, shift reindexing; the exact **all-gcd-class covariance identity** with genuinely coprime residual variables; the signed `(ν,k) → m` reassembly. |
| `RamanujanKernel.lean` | `c_p(v) = p·1_{p∣v} − 1`: exact decomposition, exact **complete-period vanishing** (negative branch), positive-branch reindexing `v = p w`, exact **`χ(p)` cancellation**, the **frozen-`p` capacity firewall** (a periodic countermodel: shorter range ⇒ no cancellation), and the source-valid alternative coordinate in which `p` remains a summation variable. |
| `FactorSplitAndCounting.lean` | the **universal window split** (greedy/minimal-divisor argument) and its **3/7–4/7** specialisation; exact near-diagonal counting (residue classes in a range, divisor-bounded modulus counts). |
| `AffineCharacterGram.lean` | the additive character algebra, complete-sum orthogonality, the **affine character Gram identity** `V*V = ℓI`, and **Parseval**, i.e. the exact `√ℓ` operator norm. |
| `NonunitStripping.lean` | exact unit/nonunit stripping with no double charge; nonunits mod a prime are `{0}`; **prime-denominator D2 nonunit centered covariance is exactly zero**; the general one-point-fibre form. |
| `KloostermanSynthesisEnergy.lean` | mean-zero space, scaled isometries, `synthesis` = affine transform, `‖synthesis‖₂` = scaled source residue energy, **isometry ⇒ no contraction**, and the **per-mode firewall** (termwise budgets sum to `Nε`, attained). |
| `ZeroResonanceLedger.lean` | the retained zero region `1 − A log L/L < Re ρ ≤ 1`, `|Im ρ| ≤ L^D`; exact trichotomy against its complement; monotonicity and boundedness; zero families, the **zero/source moment** proposition, subfamily monotonicity and exact splitting; the three separate statuses (zero-density-closed, Deuring–Heilbronn-conditional, exceptional-moment-open) with the only bridge between them proved. |
| `AnalyticInterfaces.lean` | Siegel–Walfisz, zero density for `L(s,χ)` (using Mathlib's `DirichletCharacter.LFunction`), explicit-formula **data + deterministic adapter**, KMS-type, Blomer–Pascadi, Wright, source-AP bank — all named propositions, **never inhabited**; plus the kernel-proved deterministic half of the source-side affine character estimate. |
| `PositiveBranchOwner.lean` | the D2 positive `p∣v` survivor as a first-class object: sector data, the exact facts, the capacity firewall with the .69–.711 exponent window, the alternative coordinate, the open node `PositiveBranchMomentBound`, and a proof that the identities alone imply no bound. |
| `RestAndD3.lean` | mask/rest reassembly, the `−3 log M` chamber with `chamberCoefficient_ne_zero` (it cannot be dropped), its status enumeration (currently `d3Open`), the chamber reduction of `R_rest`, the D1/D2/D3 object, and the **D3 firewall**: absence of D3 must be proved, never assumed. |
| `CurrentStatusLatest.lean` | the authoritative status module: 49 nodes, evidence categories, dependency lists, computed dependency closure, and the **minimal open cut set computed and checked by `decide`**; every `kernelProved` row is re-ascribed to an actual theorem of this layer. |
| `FrontierAlignment.lean` | the old-to-new alignment: verdicts for every old cut-set node, `no_old_node_discharged`, and the two proved bridges (see below). |

Modified for aggregation/audit only: `Gate1B/R11/Frontier/Bank.lean` (imports + one marker) and
`Gate1B/R11/Frontier/AxiomAudit.lean` (`#print axioms` for every new principal theorem).

## The two proved bridges of the alignment

1. **`sharp_rowConsumer_oscillation_fails`** — in the sharpness instance of the existing bank the
   residue-fibre oscillation of the selected row consumer is *not* `0`: otherwise the row consumer
   would be residue-determined and `R_loc-top,3` would vanish exactly, contradicting the
   kernel-proved value `1`. Hence `RowConsumerResidueOscillation` is an **independent owner**; it
   is not discharged by any universally valid identity, and it must not be re-labelled as one of
   the new analytic objects.
2. **`oldFrontier_reduction_still_valid`** — the old deterministic reduction is preserved
   verbatim: oscillation hypothesis + finite budget ⇒ `RLocTop3Bound`.

## Alignment verdicts for the old cut set

| old node | verdict |
|---|---|
| `RowConsumerResidueOscillation` | INDEPENDENT OWNER (still open, still consumed by `R11`) |
| `Mod3CenteredCaller` | INDEPENDENT OWNER (external analytic, never inhabited) |
| `RealFordGrammarObligationFor` | STILL LIVE |
| `ConditionalConsumerComparison` | STILL LIVE |
| historical Ford obligation *as originally stated* | FALSE / DEFECTIVE (vacuously satisfiable — recorded in the previous run) |
| ordinary local top | SUPERSEDED |

`no_old_node_discharged` is a kernel-checked guard: **no** old node is recorded as discharged.

## STRICT FINAL OUTPUT

```
PREVIOUS FORMAL BANK:
PRESERVED   (append-only; nothing edited, renamed, weakened or deleted; the only pre-existing
             defect on record — the vacuous historical Ford obligation — is unchanged and
             re-recorded, not repaired by relabelling)

FULL LAKE BUILD:
PASS        (default targets RequestProject, Gate04Root, Gate1A, Gate1B, UniversalV8, Universal;
             the new modules are imported by Gate1B.R11.Frontier.Bank, which is inside the
             Gate1B library glob, so they are really in the build)

AXIOM AUDIT:
PASS        (every new principal theorem depends only on a subset of
             {propext, Classical.choice, Quot.sound}; a machine search of the new directory finds
             no sorry, admit, custom axiom, native_decide, unsafe, @[implemented_by] or opaque)

OLD R_loc-top,3 FRONTIER:
STILL LIVE / INDEPENDENT   (proved: sharp_rowConsumer_oscillation_fails)

D2 NEGATIVE BRANCH:
KERNEL-REDUCED + ANALYTIC-CONDITIONAL
  kernel: cpKernel_eq, sum_cpKernel_complete_period, chi_p_cancels, sum_positive_branch
  analytic: sourceAffineCharacterEstimate (CONDITIONAL_ANALYTIC, consumes sourceAPBank)

D2 POSITIVE p|v BRANCH:
Gate1B.R11.Frontier.Latest.PositiveBranchMomentBound   (OPEN; owner object
  PositiveBranchSector; firewall positive_branch_complete_period_unavailable proves the
  complete-period route is unavailable once p is frozen)

ZERO-RESONANCE:
Gate1B.R11.Frontier.Latest.ExceptionalMomentOpen  (= Retained A D ∧ ZeroMomentBound F B)
  OPEN.  Not assumed: no GRH, no "no exceptional zero", no "one zero in the strip".

GLOBAL SOURCE CROSS-ENERGY:
Node globalSourceCrossEnergy — the signed source-energy / cross-covariance estimate.  OPEN.
  Firewall on record: synthesis_no_source_contraction (the simultaneous synthesis is a scaled
  isometry and supplies no contraction) and summed_wrapper_nonclosing (termwise KMS is
  quantitatively nonclosing).

D2 UNIT:      OPEN   (node d2UnitCovariance)
D1:           OPEN   (node d1CenteredCovariance)

GLOBAL FOURIER OWNERSHIP:
INCOMPLETE    (node fullCircleFourierOwnership: critical corona, adjacent coronas, old narrow
               packets, clipped numerator-dependent cells, large denominators, row-mask →
               global-chart transfer)

R_rest:       OPEN, but deterministically reduced to its chambers
              (rest_abs_le_of_chamber_bounds, rest_eq_single_chamber)

D3:           OPEN — neither constructed nor certified absent (d3_zero_not_automatic).
              The five-prime raw chamber carrying −3 log M has the explicit formal owner
              `chamberStatus = ChamberStatus.d3Open`, and chamberCoefficient_ne_zero proves it
              cannot be silently dropped.

CURRENT MINIMAL OPEN CUT SET TO R11   (computed: theorem cutSet_r11, checked by decide)
1. d2PositiveMoment                 — PositiveBranchMomentBound: the D2 positive p|v nonunit
                                      zero/source moment ≪ x L^{-B}.  Consumer: R11.
2. exceptionalZeroWedge             — ExceptionalMomentOpen: the retained near-1, low-height
                                      zero family moment ≪ x L^{-B}.  Consumer: R11.
3. d2UnitCovariance                 — the D2 unit centered covariance.  Consumer: R11.
4. d1CenteredCovariance             — the D1 centered covariance.  Consumer: R11.
5. globalSourceCrossEnergy          — the signed global source cross-energy estimate; must beat
                                      the isometry (no contraction from synthesis alone).
6. fullCircleFourierOwnership       — full-circle ownership of all coronas/packets/cells.
7. rRestMasks                       — R_rest current masks and selected-principal reassembly.
8. fivePrimeChamber                 — the −3 log M chamber owner.
9. d3Construction                   — D3: construct it or prove it absent.
10. rowConsumerResidueOscillation   — the old formal owner, still live and independent.
11. realFordGrammarObligation       — the non-vacuous historical provenance obligation.
12. conditionalConsumerComparison   — the historical weighted-pushforward evidence parameter.

EXTERNAL ANALYTIC INPUTS CONSUMED ON THE WAY TO R11   (theorem externalInputs_r11)
siegelWalfisz, zeroDensityInput, deuringHeilbronn, blomerPascadi, sourceAPBank,
mod3CenteredCaller — all named propositions, none inhabited, none marked KERNEL_PROVED.

R11:          OPEN

ADDITIONAL CUT SET R11 → HSTAR / GATE1B   (theorem cutSet_gate1B_extra)
1. r11ToHstarSplice   — the R11 → HSTAR downstream splice.
2. hstar              — HSTAR itself.

HSTAR:        OPEN
GATE1B:       OPEN

NO TWIN-PRIME CLAIM.
```

## NEXT_GENERATION_STATE

Begin from the computed cut set above (`cutSet_r11`, kernel-checked). Concretely:

1. The two source-most-exact members are `fivePrimeChamber` and `rRestMasks`: both are now
   reduced to a chamber-by-chamber ownership question by `rest_abs_le_of_chamber_bounds` /
   `rest_eq_single_chamber`, so what is needed is either a removal/routing proof for the
   `−3 log M` chamber or its budget.
2. `d2PositiveMoment` must be attacked in the *alternative coordinate*
   (`positive_branch_prime_divisor_coordinate`); the frozen-`p` route is closed by
   `positive_branch_complete_period_unavailable`.
3. `globalSourceCrossEnergy` cannot be closed by any per-mode callable: see
   `summed_wrapper_nonclosing` and `synthesis_no_source_contraction`. A genuine contraction
   mechanism, not an isometry, is required.
4. `rowConsumerResidueOscillation` stays exactly where the previous run left it, and
   `sharp_rowConsumer_oscillation_fails` shows it cannot be discharged by identities.
