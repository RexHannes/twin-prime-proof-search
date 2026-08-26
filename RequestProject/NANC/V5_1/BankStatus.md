# NANC V5.1 — GATE 0 / GATE 2 CONSERVATIVE PROVENANCE AND CONDITIONAL-CLOSURE PATCH

Append-only extension of the V5 controlling layer.  Nothing analytic is
inhabited; the purpose of the run is to make the bank *more conservative*.

## A. Baseline / repository facts

| item | value |
| --- | --- |
| baseline HEAD | `15be349` ("Initial commit") — contains `RequestProject/NANC/V5/Controlling/` |
| controlling-bank commit | `15be349` (the controlling layer is part of that commit) |
| parent of baseline | none (root commit) |
| Lean | 4.28.0 |
| Mathlib | `8f9d9cff6bd728b17a24e163c9402775d9e6a365` (path dependency in `.lake/packages/mathlib`) |
| baseline `lake build` | PASS (8072 jobs) |
| final `lake build` | PASS (8083 jobs) |

`git diff` over `RequestProject/NANC/V4` and `RequestProject/NANC/V5`
(including `V5/Controlling/`) is **empty**: those trees are byte-identical.  The
only pre-existing file changed is `RequestProject/NANCBank.lean`, which gained a
single import line.

## B. New layout

```
RequestProject/NANC/V5_1.lean
RequestProject/NANC/V5_1/
    ProvenancePatch.lean
    N2RoughBoundInterface.lean
    FordMaynardSourceAudit.lean
    DependencyAuditPatch.lean
    N2CellSumRepairs.lean
    Gate02StatusPatch.lean
    ConditionalEndgamePatch.lean
    Counterguards.lean
    BankStatus.lean
    Main.lean
    BankStatus.md
```

Namespace `NANC.V5_1`; imports `RequestProject.NANC.V5.Controlling`; no parent
definition is copied.

## C. New provenance class

`V51Provenance` extends the parent status universe with

* `assumedSourceReading` — attributed to a source whose relevant passage was
  **not** inspected in the material available to this bank;
* `sourceInspectedNotProved` — passage read verbatim, still not a Lean proof;
* `sourceSpecificAnalyticPass` — the parent universe has no such label.

The parent `ControlStatus` embeds by `V51Provenance.ofControl`, proved
**injective** and proved to miss all three new labels, so no two distinct
statuses are identified.  Proved inequalities include

```
assumedSourceReading ≠ leanProved
assumedSourceReading ≠ externallyPublished
assumedSourceReading ≠ opusAuditedAnalyticPass
assumedSourceReading ≠ sourceSpecificAnalyticPass
sourceInspectedNotProved ≠ leanProved
```

plus `V51Entry.inspection_does_not_promote` and
`V51Entry.promoteByInspection_not_leanEvidence`: **source verified ≠ Lean proof**.

## D. Source availability

No readable copy of the Ford–Maynard manuscript is present in this repository
(`fordMaynardSourceTextPresent = false`), so **no passage was inspected in this
run**, and every new Ford–Maynard attribution carries provenance
`assumedSourceReading` with inspection state `notInspected`.

## E. `FMLemma718RoughBound`

Defined as a structure over `Lemma718Data` with the literal source-reading
content

```
σ = ν − 2ε,   H(n) = (1 ∗ g)(v(n)) · 1_{P⁻(n) ≥ n^σ},   |H(n)| ≤ C_{g,ν} on N₂(ε)
```

and **left uninhabited**.  Provenance: `assumedSourceReading`.

## F. Sigma arithmetic (Lean-proved, elementary)

* `sigma_ge_of_eps_le_nu_div_hundred` : `0 ≤ ε ≤ ν/100`, `σ = ν − 2ε` ⟹ `σ ≥ (49/50)ν`;
* `sigma_ge_49_300_of_nu_one_sixth` and its real form : `ν = 1/6` ⟹ `σ ≥ 49/300`;
* `rough_length_primeFactorsList_le_six` / `rough_cardFactors_le_six` :
  if `n > 1` and every prime factor of `n` is `≥ n^σ` with `σ ≥ 49/300`, then
  **Ω(n) ≤ 6** — the total number of prime factors *with multiplicity*
  (`ArithmeticFunction.cardFactors`), not `ω(n)`.  The sharp bound `6` is
  obtained, not a weaker `7`.
* `PEpsilon_rough_cardFactors_le_six` : the combined `ν = 1/6`, `σ = 1/6 − 2ε`
  form.

Firewall: this arithmetic is not evidence that Ford–Maynard uses this σ.

## G. `N2HUniformity`

Defined over a family `N2Family` and left uninhabited.  The map

```
FMLemma718RoughBound at every admissible ε   →   N2HUniformity
```

(`lemma718_projects_to_N2HUniformity`) is documented and classified as a **field
projection / definitional unfolding**, not a new analytic derivation: the uniform
bound is the `H_bound` conjunct of the rough-bound interface.

Firewall CG-14 (`uniform_factor_bound_not_H_uniformity`): a family every element
of whose region is σ-rough (hence `Ω ≤ 6`) can still fail `N2HUniformity`.

## H. Dependency table, edge by edge

| target | premise | claimed by inherited audit | this bank asserts | inspected here |
| --- | --- | --- | --- | --- |
| Lemma 7.20 | comparison condition (b.2) | `sourceVerified` | `assumedSourceReading` | no |
| Proposition 7.19 | (w), Type I, Type II | `uninspectedSourceDependency` | `assumedSourceReading` | no |
| Lemma 7.21 | Type I | `uninspectedSourceDependency` | `assumedSourceReading` | no |
| Theorem 8.2 final N₂ step | bounded-class pointwise estimate | `inheritedAuditClaim` | `assumedSourceReading` | no |

Proved: the table is not fully source-verified; exactly one edge is *claimed*
verified; upgrading that edge leaves the other three literally unchanged
(`upgrade_lemma720_leaves_others`); no upgrade ever produces Lean evidence.

**Dependency table status: PARTIALLY SOURCE-VERIFIED (at claim level only).**

## I. The four N₂ cellsum repairs (recorded as typed metadata)

| id | content | kind |
| --- | --- | --- |
| A | largest active prime isolated as the final two-linear-form sieve variable | analytic architecture |
| B | coarse mesh `1 ≪ N ≪ log x`, not a microscopic pointwise cell mesh | analytic architecture |
| C | `REM ≪ P^(1−2δ)(log x)²`, aggregate contribution `x^(1−2δσ)/(2δ)` | external analytic estimate |
| D | the comparison `b`-side of this N₂ cellsum step does not need (b.2) | hypothesis-usage claim |

No asymptotic statement is encoded as exact arithmetic, and none of the four is
Lean evidence.  CG-16 separates "(b.2) required for Lemma 7.20" from "(b.2)
required by the N₂ b-side".

## J. External / uninhabited inventory (extended)

Added in V5.1: **two-linear-form Selberg upper sieve**, **Mertens/PNT input for
the prefix-volume identity**.  Retained: Ford–Maynard Theorems 2.7 / 4.16 / 8.2 /
8.3, Bombieri–Vinogradov, Brun–Titchmarsh, comparison progression asymptotics,
FM (b.1)/(b.2)/(w), `FM-N2-CELLSUM-UPPER45`, the ε-uniform N₂ splice,
`FMLemma718RoughBound`, `N2HUniformity`, `FMShiftedPrimeT82Splice`,
`FullFMTypeII_OneSixth`, full Type-II reassembly, twin-prime infinitude.
Proved: no inventory entry is Lean evidence.

## K. Gate statuses

```
GATE 0
    RESEARCH:  PERMANENT ANALYTIC PASS   (opusAuditedAnalyticPass, ≠ leanProved)
    LEAN:      EXTERNAL / UNINHABITED
    parent Gate-0 compilers preserved, unchanged.

GATE 2
    CLOSED ONLY CONDITIONAL ON
        FullFMTypeII_OneSixth              (openStatus, no Lean inhabitant)
      AND
        FMLemma718RoughBound AS STATED     (assumedSourceReading, no Lean inhabitant)
    LEAN:      EXTERNAL / UNINHABITED
    gate2Status51 = conditionalOnTwoAntecedents,  proved ≠ closed.

FULL FM TYPE II            OPEN / UNINHABITED
FULL TYPE-II REASSEMBLY    OPEN / UNINHABITED
TWIN PRIMES                NOT PROVED
TWIN-PRIME INFINITUDE      NOT DECLARED
```

`gate2Dependencies` carries the two antecedents as **data**; CG-11 proves the
Type-II antecedent alone is not the package.

## L. Conditional endgame wrapper

`V51ShiftedPrimeEndgamePackage` = the inherited controlling package **plus** the
`FMLemma718RoughBound` field.  Uninhabited.  Projections for Type II, Lemma 7.18,
Gate-0 Type I, the cell-sum bound and the twin-mass conclusion.  The only Lean
deduction is the inherited finite step

```
positive weighted twin mass  ⟹  ∃ p ∈ window, p and p+2 prime.
```

`no_v51Package_without_lemma718` shows the second antecedent is load-bearing;
`twinMassPositive_not_automatic` shows the positivity input is a genuine
requirement.  Twin-prime infinitude is not declared.

## M. Threshold-convention audit (append-only)

`PublishedThresholdConventionAudit` stores both readings side by side:

* parent V5 metadata: **strict** `ν > 0.1663`;
* later audit reading: **non-strict** `ν ≥ 0.1663`;
* later-reading provenance: `assumedSourceReading` (no source inspected).

The only downstream fact used remains `1/6 > 1663/10000` with margin
`11/30000` — the existing V4/V5 proofs, re-exported, not re-proved — and `ν = 1/6`
satisfies **both** conventions (`one_sixth_satisfies_both_conventions`).

## N. Counterguards

CG-9 … CG-18 are all proved (see `Counterguards.lean`), and the eight inherited
controlling guards are listed and remain in force.

## O. Axiom / trust-token audit

`BankStatus.lean` runs `#print axioms` on **113** inhabited V5.1 declarations.
Every one depends on at most `propext, Classical.choice, Quot.sound`; many depend
on `propext` only or on nothing.

`rg -n "sorry|admit|axiom|unsafe|opaque|native_decide|implemented_by"` over
`RequestProject/NANC/V5_1` and `RequestProject/NANCBank.lean` matches only

* the `#print axioms` commands in `BankStatus.lean`, and
* documentation lines that mention the word "axioms".

No `sorry`, no `admit`, no custom `axiom`, no `unsafe`, no `opaque` proof hack,
no `native_decide`, no `@[implemented_by]` — in V5.1 or anywhere else in the
repository sources.

## P. Required final report

```
BUILD:                              PASS
BASELINE HEAD:                      15be349 ("Initial commit")
FINAL HEAD:                         see git log (V5.1 commits on top of 15be349)
CONTROLLING BANK COMMIT:            15be349
LEAN:                               4.28.0
MATHLIB:                            8f9d9cff6bd728b17a24e163c9402775d9e6a365
V4 PRESERVED:                       YES (byte-identical)
EARLIER V5 PRESERVED:               YES (byte-identical)
V5 CONTROLLING PRESERVED:           YES (byte-identical)
NEW V5.1 PATH:                      RequestProject/NANC/V5_1{.lean,/}
PROVENANCE CLASS:                   assumedSourceReading ADDED
ASSUMED-SOURCE FIREWALL:            PROVED
FMLemma718RoughBound:               UNINHABITED
FMLemma718RoughBound PROVENANCE:    ASSUMED SOURCE READING
SIGMA ARITHMETIC:                   PROVED
SIGMA LOWER BOUND:                  49/300
TOTAL PRIME FACTOR BOUND:           Omega(n) <= 6
N2 H-UNIFORMITY:                    UNINHABITED
N2 H-UNIFORMITY RESEARCH STATUS:    CONDITIONAL (on FMLemma718RoughBound as stated)
DEPENDENCY TABLE:                   PARTIALLY SOURCE VERIFIED
VERIFIED DEPENDENCY EDGES:          Lemma 7.20 <- (b.2)  [claimed by inherited audit only;
                                    not inspected in this run]
UNINSPECTED DEPENDENCY EDGES:       Proposition 7.19 <- (w), Type I, Type II;
                                    Lemma 7.21 <- Type I;
                                    Theorem 8.2 final N2 step <- bounded-class pointwise estimate
N2 CELLSUM REPAIRS:
  LARGEST-PRIME FINAL VARIABLE:     RECORDED
  COARSE MESH:                      RECORDED
  AGGREGATE REMAINDER:              RECORDED
  B-SIDE NO-b.2:                    RECORDED
TWO-LINEAR-FORM SELBERG SIEVE:      EXTERNAL
PREFIX-VOLUME MERTENS/PNT:          EXTERNAL
N2 CELLSUM:                         RESEARCH PASS CONDITIONAL ON LEMMA 7.18
N2 CELLSUM LEAN:                    UNINHABITED
N2 EPSILON UNIFORMITY:              RESEARCH PASS CONDITIONAL ON LEMMA 7.18
THEOREM-8.2 SHIFTED-PRIME SPLICE:   CONDITIONAL / PARTIALLY SOURCE VERIFIED
GATE0 RESEARCH STATUS:              PERMANENT ANALYTIC PASS
GATE0 LEAN ANALYTIC STATUS:         EXTERNAL / UNINHABITED
GATE2 RESEARCH STATUS:              CLOSED CONDITIONAL ON FULL FM TYPE II
                                    AND FMLemma718RoughBound
GATE2 LEAN ANALYTIC STATUS:         EXTERNAL / UNINHABITED
FULL FM TYPE II:                    OPEN / UNINHABITED
FULL TYPE-II REASSEMBLY:            OPEN / UNINHABITED
THRESHOLD PARENT METADATA:          STRICT > 0.1663
THRESHOLD LATER AUDIT READING:      NONSTRICT >= 0.1663
THRESHOLD LATER READING PROVENANCE: ASSUMED SOURCE READING
1/6 THRESHOLD MARGIN:               11/30000  LEAN-PROVED (inherited proof re-exported)
TWIN PRIMES:                        NOT PROVED
TWIN PRIME INFINITUDE THEOREM:      NOT DECLARED
SORRY:                              0
ADMIT:                              0
CUSTOM AXIOM:                       0
UNSAFE ESCAPES:                     0
AXIOM AUDIT:                        PASS (propext, Classical.choice, Quot.sound or fewer)
FULL REGRESSION BUILD:              PASS
```

**FINAL VERDICT:** `ARISTOTLE_NANC_V5_1_GATE02_CONSERVATIVE_PATCH_PASS`

Controlling mathematical ledger:

```
GATE0:
PERMANENT ANALYTIC PASS.

GATE2:
CONDITIONAL ENDGAME ONLY —
requires FullFMTypeII_OneSixth
and FMLemma718RoughBound as stated.

FMLemma718RoughBound:
UNINHABITED;
source provenance remains conservative unless inspected.

FULL FM TYPE II:
OPEN.

FULL TYPE-II REASSEMBLY:
OPEN.

TWIN PRIMES:
NOT PROVED.

NO ANALYTIC SOURCE CLAIM HAS BEEN PROMOTED TO A LEAN PROOF.
```
