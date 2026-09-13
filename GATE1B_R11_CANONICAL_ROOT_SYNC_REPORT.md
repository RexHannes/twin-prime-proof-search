# GATE 1B / R11 — CANONICAL ROOT SYNC (append-only formal run)

All new material is under `Gate1B/R11/Frontier/CanonicalRootSync/`.  The only pre-existing files
touched are the two designated aggregator files `Gate1B/R11/Frontier/Bank.lean` (imports plus one
aggregation marker) and `Gate1B/R11/Frontier/AxiomAudit.lean` (`#print axioms` lines).  Nothing
was edited, renamed, weakened or deleted; Gate 1A was not touched.

## New modules

| module | content |
|---|---|
| `CanonicalRoot.lean` | the canonical scalar root object (P1): `rootSum s g b = ∑ g(n)[Λ(n+2) − b(n)]`, exact split, exact mask split, linearity, the identity `F = rootSum + Err`, and the **derivation from an existing exact owner**: `rootSum s g (bLoc Bc) = R11Residual s g Bc`. The error budget `CanonicalRootErrorBudget` and the target `ScalarBudget` are interfaces; budget algebra (`add`, `congr`, `mono`, `of_parts`) is kernel-proved; `errorBudget_not_implied_by_identity` separates algebra from estimate. |
| `KFiveAlgebra.lean` | the K = 5 rank algebra (P3): `hbCoeff`, the literal row `5, −10, 10, −5, 1`, the ring identity `1 − (1−x)^5 = 5x − 10x² + 10x³ − 5x⁴ + x⁵`, its `∑_{j=1}^{5}` form, its instantiation in the Dirichlet convolution ring at a truncated Möbius block, the isolated `j = 2` branch, and the physical packet with the **retained** constraints `0 ≤ η < 99/200`, `η + 5a ≤ 1`, `η + 5b ≤ 1` (the revoked `e ≤ x^σ` assumption is not imported). Physical ceiling `θ < 697/1000` proved. |
| `WrightPrefix.lean` | exact Wright prefix geometry (P4): the region `θ ≤ 45/89 − ε_W`, the conditional membership statement (Wright is a named, uninhabited proposition), and the **universal η prefix** `η ≤ 47/267 − (5/3) ε_W`, proved as an iff and with the failure statement above the prefix. |
| `PascadiFirewall.lean` | the capacity firewall (P5): Pascadi condition sets as declared data, dual certificates, the general LP-duality ceiling theorem, the literal certificate, and `PascadiCallable ⟹ θ ≤ 4/7 − 6 ε_P` **for all six permutations**; plus non-vacuity and a sharpness witness showing the `4/7` constant is attained at the maximal physical packet `η = 2/7, a = b = 1/7`. |
| `OpenBoxCertificate.lean` | the open j = 2 box (P6): `η = 2/5, a = 11/100, b = 111/1000`, `θ = 621/1000`, physical, `4/7 < θ < 5/8`, `θ > 45/89`, every Pascadi permutation fails (derived from the firewall), outside the Wright region; hence the survivor region is nonempty. |
| `FixtureReconciliation.lean` | fixtures (P7): the `.619` fixture is **formally nonphysical** (`a, b > (1−η)/5`), satisfies only the *revoked relaxed* condition set, and that relaxation is proved to destroy the `4/7` ceiling; the `.563` fixture **passes** the physical constraints and is literally Pascadi-callable at slack `1/2000` — an exponent/interface statement only. |
| `J2ResidualOperator.lean` | the residual operator (P8): `pairing`, `dbRaw` (coefficient `−10`), `dbPrincipal`, `dbCentered` (`D_B`), `dbMasked`; exact `raw = centered + principal`, exact mask split, mean-zero centering, deterministic adapters, the **chart-independence theorem** (charts do not manufacture owners), exactly one open analytic proposition `J2ResidualCenteredBound`, and the countermodel showing the algebra does not imply it. |
| `CanonicalConditionalClosure.lean` | the strongest conditional theorem (P10): `r11_of_canonical_route`, whose hypotheses are three exact bridges and six analytic interfaces and whose conclusion is the R11 scalar target; plus satisfiability of the bridges and a countermodel proving the `j = 2` owner is load-bearing. |
| `OwnerBridge.lean` | the old-owner audit (P2): the twelve owners, the five verdicts, the classification rule, and the justifications — the absorption witness (the route theorem itself) and the independence countermodel (re-ascribed from the bank) — plus the three **missing exact bridges**. |
| `CutSetRecomputation.lean` | the two graphs (P9): the legacy cut re-ascribed verbatim (12 nodes), the canonical-sync graph **retaining every legacy node**, and the computed canonical-sync cut (10 nodes) with the proof that no legacy owner is consumed by the canonical route. |
| `RLocTop3Alignment.lean` | the alignment test (P11): the old reduction re-ascribed unchanged, the proof that the owner is **not implied** by the canonical root, and the proof that it is **not consumed** by the canonical route; verdict `independentButOffRoute`. |
| `CanonicalSyncStatus.lean` | the ledger (P12/P13): the analytic interface list, the two cut sizes, the composition of the canonical cut, the classification counts, and the guards. |

## STRICT FINAL OUTPUT

**PREVIOUS FORMAL BANK:** PRESERVED

**FULL LAKE BUILD:** PASS (all default targets)

**AXIOM AUDIT:** PASS — every new exported theorem depends only on a subset of
`propext`, `Classical.choice`, `Quot.sound`; a machine scan of the new directory finds no
`sorry`, `admit`, custom axiom, `native_decide`, `unsafe`, `opaque` or `@[implemented_by]`.

**CANONICAL ROOT FORMAL OBJECT:** COMPLETE — the three layers (exact identity, error-budget
proposition, analytic estimate) are separated, and the exact identity is *derived* from the
pre-existing owner `R11Residual` (`rootSum_eq_R11Residual`).  The realisation of the identity for
the physical chart is listed explicitly as a missing bridge.

**OLD → CANONICAL BRIDGE:** exact theorem `absorption_witness` (= `r11_of_canonical_route`) for
the nine absorbed owners; countermodel `independence_witness` for `rowConsumerResidueOscillation`;
**missing theorem** for `realFordGrammarObligation` and `conditionalConsumerComparison`.

**K=5 IDENTITY:** PROVED (ring form, `∑_{j=1}^5` form with coefficients `5, −10, 10, −5, 1`, and
the Dirichlet-convolution instantiation).

**WRIGHT PREFIX GEOMETRY:** PROVED (`η ≤ 47/267 − (5/3) ε_W`, as an iff).

**PASCADI 4/7 FIREWALL:** PROVED for all six permutations, by exact rational LP duality, with a
sharpness witness at `θ = 4/7`.

**OPEN j=2 BOX:** PROVED (`θ = 621/1000`, physical, `4/7 < θ < 5/8`, `θ > 45/89`, no Pascadi
permutation callable, outside Wright).

**q=.619 FIXTURE:** FORMALLY NONPHYSICAL.

**q=.563 FIXTURE:** PHYSICAL (and literally Pascadi-callable at slack `1/2000`; exponent /
interface level only).

**j=2 RESIDUAL OPERATOR:** defined — raw, centered, principal, packet mask, with all currently
available algebraic equalities proved and exactly **one** open analytic proposition,
`J2ResidualCenteredBound`.

**LEGACY CUT SET (12, unchanged):** `d2PositiveMoment`, `exceptionalZeroWedge`,
`d2UnitCovariance`, `d1CenteredCovariance`, `globalSourceCrossEnergy`,
`fullCircleFourierOwnership`, `rRestMasks`, `fivePrimeChamber`, `d3Construction`,
`rowConsumerResidueOscillation`, `realFordGrammarObligation`, `conditionalConsumerComparison`.

**CANONICAL-SYNC MINIMAL CUT SET (10, computed):** `rootChartRealisation`,
`rankDecompositionRealisation`, `j2CenteredSplitRealisation` (three missing exact bridges);
`canonicalRootErrorBudget`, `branchBound1`, `branchBound3`, `branchBound4`, `branchBound5`,
`principalBudget`, `j2ResidualCenteredBound` (seven analytic nodes, exactly one of them the
`j = 2` owner).

**LEGACY OWNERS ABSORBED (9, route-level and conditional on the three missing bridges):**
`d2PositiveMoment`, `exceptionalZeroWedge`, `d2UnitCovariance`, `d1CenteredCovariance`,
`globalSourceCrossEnergy`, `fullCircleFourierOwnership`, `rRestMasks`, `fivePrimeChamber`,
`d3Construction`.

**LEGACY OWNERS STILL INDEPENDENT:** `rowConsumerResidueOscillation` (independence **proved** by
countermodel); `realFordGrammarObligation` and `conditionalConsumerComparison` (no bridge and no
countermodel — unresolved, retained).

**MISSING BRIDGES:** (1) the canonical root chart realisation for the physical
`F₁₁^new`; (2) the K = 5 rank decomposition realisation of the physical root; (3) the centered /
principal split realisation of the physical `j = 2` branch.  Additionally the two owner bridges
listed above.

**RLocTop3 STATUS:** independent (proved: not implied by the canonical root identity) **and** not
consumed by the canonical route (proved: absent from the computed canonical-sync cut).  The old
reduction is re-ascribed unchanged.

**STRONGEST CONDITIONAL R11 THEOREM** (`r11_of_canonical_route`):

> If `F = Root + Err` (canonical root identity), `Root = B₁ + B₂ + B₃ + B₄ + B₅` (K = 5 rank
> decomposition), `B₂ = Cen + Prin` (centered/principal split of the `j = 2` branch), and if
> `Err` satisfies `CanonicalRootErrorBudget … S₀`, each of `B₁, B₃, B₄, B₅` and `Prin` satisfies
> `ScalarBudget … (S₀+2)`, and `Cen` satisfies `J2ResidualCenteredBound … S₀`,
> then `R11ScalarTarget F S₀`.

None of its analytic hypotheses is inhabited anywhere in the repository.

**R11:** OPEN (closed only if all analytic hypotheses are actually inhabited — they are not).

**HSTAR:** OPEN.  **GATE1B:** OPEN.  **TWIN PRIME:** NO CLAIM.

## FINAL QUESTION

*After formal reconciliation with the latest canonical root, how many of the twelve open owners
are genuinely independent analytic obstructions, and how many were artifacts of an older
decomposition?*

Formally, and with no upgrade beyond what is proved:

* **1** owner is a proved-independent obstruction: `rowConsumerResidueOscillation` is not implied
  by the canonical root identity (countermodel in the bank, re-ascribed here).  It is,
  nevertheless, **not consumed** by the canonical route.
* **9** owners are artifacts of the older D1/D2/D3/Rest decomposition of the *same* scalar: the
  canonical route reaches the R11 scalar target without calling any of them.  This absorption is
  **conditional** on three exact bridges that are not yet proved for the physical chart, and none
  of the nine is discharged.
* **2** owners (`realFordGrammarObligation`, `conditionalConsumerComparison`) are unresolved: no
  bridge theorem and no countermodel.

Inside the canonical route the analytic cut is seven nodes, of which exactly **one**
(`J2ResidualCenteredBound`) is the surviving `j = 2` residual owner; the remaining six are the
error budget, the four non-`j=2` branch budgets and the exact-principal budget.
