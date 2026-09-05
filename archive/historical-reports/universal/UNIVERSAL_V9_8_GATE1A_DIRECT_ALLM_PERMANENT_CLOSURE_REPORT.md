# UNIVERSAL v9.8 — Gate 1A Direct all-`m` common-weight bank

Append-only run.  Seven new modules under
`RequestProject/NANC/Gate1A/SafeExtensions/`:

* `V98CanonicalDirectSource.lean`
* `V98CanonicalAllMRows.lean`
* `V98DirectEnergyPin.lean`
* `V98BPPProvenance.lean`
* `V98DirectClosure.lean`
* `V98Gate0ScopeSplit.lean`
* `V98Status.lean`

plus this report and an appended block in `LEDGER.md`.

---

## A. Regression

* Baseline `HEAD` at the start of the run: `76f8f5c`.
* Baseline `lake build`: **8440 jobs, 0 errors** (Lean `v4.28.0`, Mathlib at the
  revision pinned in `lake-manifest.json`).  The only pre-existing warning is
  the manifest `source kind` notice.
* No file from Gate 1A v9 … v9.7 was edited, renamed, deleted, weakened or
  restated.  All new material is in new files; every reuse is by `import` and
  by calling the existing declaration (for example
  `V94.familyEnergy_of_participation`, `V94.bpp_gate_margin_V1`,
  `V95.ESharpRow`, `V95.forgetP3`, `V96.template_count_ge_of_linearIndependent`,
  `V96.trivialGenericBPPBound`, `RouteAFibreFrame.Fibre`,
  `TwinPrimeProject.CenteredCRTRoot.rho`).
* `LEDGER.md` was appended to only.  `ARISTOTLE_SUMMARY.md` was not modified.

## B. Canonical Gate 1A source provenance

`Gate1ADirectCanonicalSource` transcribes the authoritative normalized
pre-square Direct source literally:

```
ctilde e = ∑_p b_p ∑_{q, q ≠ p} d_q ∑_h ω_{m,p,q}(h) · e_{m q}(2 h k · inv[p(m+kr)])
ω_{m,p,q}(h) = (H/(pq)) · Ŵ_D(h/(pq)) · exp(−hα/(pqm))
```

No term absent from the displayed source was added.  The modular inverse is a
field `inv` carrying its defining congruence `inv_spec`.  Provenance of the
formula: **`sourceInspectedNotProved`**.  Everything proved about it
(`ctilde_def`, `ctilde_excludes_diagonal`, `norm_phase`,
`omegaCanonical_weight_factor`, `omegaCanonical_congr_of_common_weight`) is
definitional or algebraic and is `leanProved`.

## C. Common `W_D`

The physical smoothing datum is a single field `DirectSourceScalars.What`.
`gate1A_direct_physicalWeight_common` proves every canonical coefficient equals
`rowScale · Ŵ_D(commonWeightArg p q h)`, where `commonWeightArg` takes **no row
argument**: the row enters only through the scalar prefactor and the smooth
factor.  At the physical level, `PhysicalDirectSource.WD` likewise carries no
row index, and `covariance_eq_weight_pairing` writes every row's covariance as
the pairing of the *same* weight with a row kernel.
`exists_rowDependent_weight_not_common` exhibits a per-row weight family that
comes from no common weight — the type-A datum that the canonical source is
not.

Derived (type-B) row dependence is handled by `SmoothSeparationCertificate`, an
**uninhabited source-specific analytic interface** (finite Fourier–Mellin
templates with nuclear cost).  Given it, `canonicalWeight_finiteTemplate`
produces a template decomposition with `#(P × Q) · n` templates, a count with no
`#Row` factor; contrast `arbitraryEdgeDependent_needs_edge_many_templates`
(the v9.6 rank obstruction: an arbitrary edge-dependent family needs at least
`#Edge` templates).

## D. Canonical all-`m` row family

`Gate1ADirectAllMRow := V95.ESharpRow` — reuse, not restatement.  Its fields are
exactly `r ∼ R` prime, `|k| ≤ K`, `m ∼ M`, `m + k r ∼ M`, generic unit; there is
no P3 field of any kind.  `allMRow_witness` inhabits it and
`exists_allMRow_not_cleanP3` shows the family is strictly larger than the
clean-P3 family (`m = 3` has one prime factor).

## E. Source transport / physical root geometry

The fibre objects come from the existing `RouteAFibreFrame.Fibre`.  With the
base point `j = 0` and the shifted point `j = k`,

```
Fibre.direct_determinant_identity : (c + k r) · A_e(t) − c · B_e(t) = 2 k
```

is proved from the single fibre axiom `c·w0 + 2 = r·a0`.  The covariance
`C_e(b,d)` is built from the repository's exact centred divisibility factor
`rho`, and `covariance_determinant` attaches the determinant identity to every
row of a physical source.  The `H`-scale profile `β`, the quotient lift and the
post-`ν` amplitude of the source document were **not** transcribed as theorems:
they are source-level formulas whose Lean transcription is not needed by any
statement proved here, and inventing them would exceed the safe scope.

## F. Exact Gate 1A energy

```
Gate1ADirectPacket.normalizedEnergy  = ∑_{e ∈ E♯} ‖Ctilde_e‖²
gate1ADirectAllMPhysicalEnergy       = ∑_{e ∈ E♯} ‖C_e‖²
normalizedDirectTarget M H L Xo      = M · H · L⁴ · X^o
physicalDirectTarget   M H L Xo      = (M · L⁴ / H) · X^o
```

`directTarget_bridge : M H L⁴ X^o = (M L⁴/H · X^o) · H²`, and
`physical_of_normalized_bound` transports a normalized bound to the physical
target under the explicit source normalisation convention
`physical = normalized / H²`.  No target is borrowed from a Gate 0 FF4 / D2
interface.

## G. BPP energy pin

`Gate1ADirectBPPEnergyPin G K` has exactly one field:

```
G.normalizedEnergy K.toESharpSource = K.normalizedEnergy
```

It mentions no dictionary, no multiplicity, no Gate 0 assembly.  **No inhabitant
is constructed.**  Guards:

* `energyPin_not_automatic` — the v9.6 vacuous `GenericBPPBound` fails the pin
  on the explicit unit packet;
* `energyPin_not_implied_by_conclusion` — a generic bound whose target already
  dominates the actual energy still fails the pin;
* `energyPin_nonempty_iff` — inhabitance is exactly the equation.

Compilers: `Gate1ADirectBPPEnergyPin.energy_le` and
`normalizedEnergy_le_target_of_pin`.

## H. BPP external analytic provenance

`Gate1ABPPPrimeParticipationInput` is the narrowest external interface: a
continuous-envelope participation datum plus the plateau lower bound.  Its
provenance is a field (`externallyPublished` / `sourceSpecificAnalyticPass`)
with a citation string.  The deterministic compiler
`primeParticipation_familyEnergy` derives `E_off ≤ (D·S/P²)·T_abs` from it using
the already-proved v9.4 finite compiler.  `participationInput_not_self_inhabiting`
shows the interface is a genuine restriction (empty plateau refutes it).

Repository/Mathlib search for the five ingredients (Section 25):

* Bernstein's inequality for trigonometric polynomials — **absent**
  (Mathlib's `Analysis/SpecialFunctions/Bernstein.lean` is Bernstein
  *polynomials* / Weierstrass approximation, a different statement);
* primes in intervals of length `R^{3/4}` — **absent** (Mathlib has Bertrand's
  postulate and Chebyshev-type bounds only);
* Fourier truncation / smooth approximation at degree `R^{1/4}` in the form
  required — **absent**.

Therefore no analytic inhabitant was built, and **no axiom was introduced**.
First external analytic theorem missing from Lean: *prime asymptotics in
intervals shorter than `R^{3/4}`* (a fortiori the published `x^{17/30+o(1)}`
short-interval theorem is not formalised in Mathlib).

## I. Root depth and margins

`familyEnergyExp_eq : 0 + 1 − 2·(3/4) = −1/2`, `oneRoot_exponent : −1/4`,
`oneRoot_real` (the v9.4 real-analytic root).  Vertex margins re-exported from
the frozen ledger: `directMargin_V1 = 1/72`, `directMargin_V2 = 1/24`,
`directMargin_V3 = 1/32`, all positive (`directMargins_pos`).  The retracted
`R^{-1}` route and its `1/12, 1/9, 5/48` margins are untouched and unused.
`directGateComparison_of_margin` turns a non-negative margin into the actual
required comparison `M · R^{-1/4} ≤ H`.

## J. Projective / axis closure

The banked v9.4 axis-safe projective results (`V94.projAxis`,
`projAxis_axis_U`, `projAxis_axis_V`, `projAxis_correlation`, …) are reused
unchanged; v9.8 adds nothing there and does not invoke any Gate 0 packet census
in that argument.

## K. `U^{-2}` recombination error

`directRecombinationError_U2` re-exports the controlling identity
`(U^{-2} M² L⁴)/(M H L⁴) = M/D` with `U = L/H`, `D H = L²`, and
`directErrorMargins_U2` the spare margins `1/18, 1/18, 1/24`.  The weaker
`U^{-1}` narrative remains recorded as failing at `V₂`.

## L. Clean-P3 corollary

`cleanP3_energy_le_allM_energy` and `cleanP3_of_allM_bound`: for non-negative
row energies the clean rows are a subset of the all-`m` rows, so any all-`m`
bound is inherited.  No separate clean-P3 analytic theorem is used.

## M. EdgeDependent-D2 scope relocation

`EdgeDependentD2Data` is **not** deleted or weakened
(`edgeDependentD2Data_still_available` re-exports the v9.6 fact).  It is
reclassified: `edgeDependentD2_is_gate0_adapter_obligation` places it in the
Gate 0 / source-adapter scope, and `gate0_disjoint_from_gate1ADirect` proves the
scopes are disjoint.  No `EdgeDependentD2Bound` is required by any Gate 1A
Direct statement in this run.

## N. Root-defect secondary status

`rootDefect_is_secondary_route`.  The root-defect source factorisation is not a
field of `Gate1ADirectClosureCertificate`; `closureCertificate_nonempty_iff`
lists the certificate's entire content (positivity, the normalized bound, the
normalisation convention), so no root-defect datum can block Gate 1A Direct.

## O. Gate 0 / Gate 1A compiler separation

`Gate0.Gate0ToGate1AExhaustivenessCertificate` lives in its own namespace, is
uninhabited here, and is provably not definitional
(`gate0Exhaustiveness_not_definitional`), with
`gate0Exhaustiveness_nonempty_iff` characterising inhabitance.
`gate1ADirect_closure_independent_of_gate0` and
`gate1ADirect_does_not_imply_gate0` give the two-way separation: Gate 1A Direct
is not blocked by the Gate 0 census, and closing it does not close Gate 0.

## P. Interaction with NANC Gate 0/2 V5.1

No Gate 0/2 V5.1 module exists in this repository, and nothing outside the seven
new Gate 1A files was touched, so the controlling Gate 0/2 statuses are
unchanged by this run: Gate 0 `PERMANENT ANALYTIC PASS (research)` /
`EXTERNAL-UNINHABITED (Lean)`; Gate 2 conditional on `FullFMTypeII_OneSixth` and
`FMLemma718RoughBound` as stated; Full FM Type II open/uninhabited; twin primes
not proved.  v9.8 changes only the Gate 1A analytic-theorem status and the
Gate 0 / Gate 1A scope boundary.

## Q. Axiom audit

`lake build`: **PASS** (8440 jobs at baseline; all seven new modules build, the
final full build is clean).  Repository-wide scan for `sorry`, `sorryAx`,
`admit`, `axiom`, `opaque`, `unsafe`, `native_decide`, `@[implemented_by]`:
only prose / doc-comment matches; **no user axiom, no `sorry`**.
`#print axioms` is run in `V98Status.lean` on all 68 new public theorems; every
one returns either no axioms or a subset of `propext`, `Classical.choice`,
`Quot.sound`.

## R. Final scientific / Lean status

* **Lean status of `GATE1A_DIRECT_ALLM_COMMONWEIGHT_BPP`:
  EXTERNAL-UNINHABITED.**  The statement is pinned, the source is pinned, the
  energies and targets are defined from the source, the finite compilers and the
  exponent ledger are kernel-checked, and the closure compiler is proved.  What
  is missing is an inhabitant of the external analytic input (plateau
  participation), which is not available in Mathlib.
* **Research status: NOT CLOSED *in this repository*.**  The "permanent analytic
  pass" reading is a *source* status: it is carried as ledger data with
  provenance `externallyPublished` / `sourceSpecificAnalyticPass`, and
  `research_status_is_not_lean_evidence` proves that such data are not Lean
  evidence.  This run neither verified nor refuted the external analytic
  argument.
* Gate 0 → Gate 1A source compiler: **OPEN**.
* Full FM Type II: **OPEN / UNINHABITED**.  Twin primes: **NOT PROVED**.

---

# ARISTOTLE_GATE1A_V9_8_DIRECT_ALLM_CLOSURE_REPORT

```
BASELINE HEAD:              76f8f5c
FINAL HEAD:                 final commit of this run (see `git log -1`)
BUILD:                      PASS — lake build, 0 errors
SORRY:                      NONE (repository-wide scan; prose matches only)
USER AXIOMS:                NONE (propext / Classical.choice / Quot.sound only)
OLD GATE1A V9-V9.7 BANK:    PRESERVED
NANC GATE0/2 V5.1 BANK:     PRESERVED (not present in this repository; untouched)
AUTHORITATIVE DIRECT SOURCE: PINNED  (Gate1ADirectCanonicalSource, ctilde_def)
PHYSICAL W_D:               COMMON  (gate1A_direct_physicalWeight_common)
CANONICAL ALL-m ROW FAMILY: CONSTRUCTED (Gate1ADirectAllMRow = ESharpRow)
CANONICAL GATE1A DIRECT ENERGY: CONSTRUCTED (normalized and physical)
PHYSICAL-NORMALIZED TARGET BRIDGE: PROVED (directTarget_bridge)
BPP ENERGY PIN:             INTERFACE CONSTRUCTED, UNINHABITED — compiler proved
BPP FINITE COMPILER:        PROVED (primeParticipation_familyEnergy)
BPP EXTERNAL ANALYTIC INPUT: EXTERNALLY PUBLISHED, NOT FORMALIZED
BPP FAMILY ENERGY:          R^(-1/2+o)
ONE ROOT:                   R^(-1/4+o)
V1:                         1/72
V2:                         1/24
V3:                         1/32
PROJECTIVE / AXES:          CLOSED (v9.4 axis-safe bank reused unchanged)
RECOMBINATION ERROR:        U^(-2) CLOSED (identity + margins 1/18, 1/18, 1/24)
CLEAN-P3:                   COROLLARY
EDGEDEPENDENT-D2:           GATE0 ADAPTER OBLIGATION
ROOTDEFECT SOURCE FACTORIZATION: SECONDARY OPEN
GATE1A DIRECT ALL-m RESEARCH STATUS: NOT CLOSED — the external BPP analytic
    input is neither formalized nor verified here; its "permanent analytic pass"
    reading is source-provenance data, not a result of this run
GATE1A DIRECT ALL-m LEAN STATUS: EXTERNAL-UNINHABITED
GATE0 SOURCE -> GATE1A COMPILER: OPEN
GATE0:                      UNCHANGED FROM V5.1
GATE2:                      UNCHANGED FROM V5.1
FULL FM TYPE II:            OPEN / UNINHABITED
FULL TYPE-II REASSEMBLY:    OPEN
TWIN PRIMES:                NOT PROVED
FIRST MISSING GATE1A SOURCE FIELD: NONE for the canonical Direct statement
    (source assembly of β, the quotient lift and the post-ν amplitude are
    source-document formulas, not needed by any statement proved here)
FIRST MISSING GATE1A ANALYTIC INPUT: prime asymptotics in intervals shorter than
    R^(3/4) (with Bernstein's trigonometric-polynomial inequality), absent from
    Mathlib — required to inhabit Gate1ABPPPrimeParticipationInput
FIRST MISSING GATE0->GATE1A FIELD: an admissible-route relation for the actual
    global source packets, i.e. an inhabitant of
    Gate0.Gate0ToGate1AExhaustivenessCertificate
FILES ADDED:                RequestProject/NANC/Gate1A/SafeExtensions/
                            V98CanonicalDirectSource.lean,
                            V98CanonicalAllMRows.lean, V98DirectEnergyPin.lean,
                            V98BPPProvenance.lean, V98DirectClosure.lean,
                            V98Gate0ScopeSplit.lean, V98Status.lean;
                            UNIVERSAL_V9_8_GATE1A_DIRECT_ALLM_PERMANENT_CLOSURE_REPORT.md
FILES MODIFIED:             LEDGER.md (append only)
REPORT:                     UNIVERSAL_V9_8_GATE1A_DIRECT_ALLM_PERMANENT_CLOSURE_REPORT.md
LEDGER:                     APPENDED
AXIOM AUDIT:                68 new public theorems audited; only propext,
                            Classical.choice, Quot.sound occur
TRUST TOKEN SEARCH:         no sorry / sorryAx / admit / axiom / opaque / unsafe /
                            native_decide / @[implemented_by] in new code
FINAL SCIENTIFIC STATEMENT: The canonical Gate 1A Direct all-m common-weight
    source, its all-m row family, its normalized and physical energies, the
    H-normalisation bridge, the BPP finite compiler, the exponent ledger with
    margins 1/72, 1/24, 1/32 and the closure compiler are kernel-checked in
    Lean, and the theorem is now conditional on exactly one uninhabited external
    analytic interface (plateau prime participation) plus its energy pin — with
    the Gate 0 source-routing obligation proved to lie outside the statement.
```

---

## Addendum — re-verification after the Gate 1B v8.2 additions

The Gate 1A v9.8 bank is unchanged by the later Gate 1B v8.2 work: no
`RequestProject/NANC/Gate1A/**` file was modified after the v9.8 commits, the
repository-wide `lake build` passes (8472 jobs, 0 errors), and a repository-wide
scan finds no `sorry`, `admit`, user `axiom`, `opaque`, `native_decide` or
`@[implemented_by]` in any source file.  The Gate 1A v9.8 verdict block above
therefore still stands verbatim.

Commits of this line of work: `c832a6d` (Gate 1A v9.8 modules), `ac3adbe`
(v9.8 status, axiom audit, report, LEDGER), followed by the Gate 1B v8.2
commits.
