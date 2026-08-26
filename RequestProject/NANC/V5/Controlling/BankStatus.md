# NANC V5 CONTROLLING LAYER — GATE 0 / GATE 2 FORD–MAYNARD SHIFTED-PRIME CONTROLLING INTERFACES

Append-only extension of the existing NANC V4 and V5 banks.
Namespace `NANC.V5.Controlling`; sources in `RequestProject/NANC/V5/Controlling/`.

## A. Baseline (reported, not fabricated)

| item | value |
| --- | --- |
| HEAD at start of run | `d608d6e` ("Initial commit") |
| parent | none (root commit) |
| Lean | 4.28.0 (`x86_64-unknown-linux-gnu`, commit `7e01a1bf5c70fc6167d49c345d3bf80596e9a79b`) |
| Mathlib | `8f9d9cff6bd728b17a24e163c9402775d9e6a365` |
| baseline `lake build` | PASS (8061 jobs) |
| final `lake build` | PASS (8072 jobs) |

`RequestProject/NANC/V4` and all pre-existing `RequestProject/NANC/V5` files are
**byte-identical** after this run (`git diff` over them is empty).  The only
modified pre-existing file is `RequestProject/NANCBank.lean`, which gained one
import line.

## B. Regression

`lake build` builds the whole library, including
`RequestProject.NANC.V4`, `RequestProject.NANC.V5`,
`RequestProject.NANC.V5.Controlling` and `RequestProject.NANCBank`.

## C. Status system (`Status.lean`)

`ControlStatus` = `leanProved | conditionalCompiler | opusAuditedAnalyticPass |
externallyPublished | uninhabitedInterface | sourceMissing | openStatus |
failedRoute`, with the Lean-proved firewalls

* `opusAuditedAnalyticPass ≠ leanProved`
* `externallyPublished ≠ leanProved`
* `uninhabitedInterface ≠ leanProved`
* `conditionalCompiler ≠ leanProved`
* `sourceMissing ≠ failedRoute`, `openStatus ≠ failedRoute`
* no status is simultaneously Lean evidence and non-Lean evidence
* the translations into the V5 and V4 status systems never promote a non-Lean
  status to a proof-bearing one.

## D. Ford–Maynard metadata (`FordMaynardMetadata.lean`)

* Source record: Ford–Maynard, *On the theory of prime-producing sieves*,
  arXiv:2407.14368 (public 107-page version), status `externallyPublished`.
* Threshold banked as the **exact rational** `1663/10000`; the V4 facts
  `1/6 > 1663/10000` and `1/6 − 1663/10000 = 11/30000` are re-exported, not
  re-proved.
* **Published Theorem 2.7(b) uses the STRICT inequality `ν > 0.1663`.**  Both the
  strict and non-strict hypotheses are defined; `strict → non-strict` is proved,
  and `nonStrict_not_strict` exhibits `ν = 0.1663` as a witness separating them.
* `P_ε` geometry: `γ = 1/2 − ε`, `θ = ε`, `ν = 1/6 − 2ε`; proved
  `θ + ν = 1/6 − ε`, `γ > θ + ν`, `γ < 1/2` for `ε > 0`, and
  `ν > 1663/10000` for `0 < ε < 11/60000`.
* `FMTheorem416` — **uninhabited** external interface (vanishing outside the
  support window).  Lean-proved conditional compiler:
  `FMTheorem416 → ordinary P_ε coefficient = 0` for every `ε > 0`.
* Ordinary vs bounded sequence class recorded as data; `ordinary ≠ bounded`, and
  the bounded class carries the extra requirement `condition (4.1)`.
* `FMDependencyAudit`: metadata for the **displayed** dependency chain only
  (Prop. 7.19 uses (w),(I),(II); Lemma 7.20 uses (b.2); Lemma 7.21 uses Type I;
  the displayed Theorem-8.2 proof uses the pointwise bounded-class condition at
  the final `N₂` estimate).  Scope guard proved: the record does not exclude
  indirect uses elsewhere.

## E. Exact Type-II convention (`TypeIIExactConvention.lean`)

Endpoints defined with real exponentiation:
`(X/2)^θ < m ≤ X^(θ+ν)`, versus the naive `X^θ < m ≤ X^(θ+ν)`.

* `exact_range_ne_naive_range` — the conventions differ (witness `X = 4`,
  `θ = 1`, `ν = 0`, `m = 3`).
* `FMTypeIIExactAtScale` — the V4 Type-II predicate over the exact range; the
  universal quantifier over arbitrary divisor-bounded `ξ, κ` is retained
  literally.  **Uninhabited.**
* `sourceSpecific_not_FMTypeIIExact` — finite counterexample: a source-specific
  bilinear bound does not give the exact hypothesis.

## F. Twin comparison (`TwinComparison.lean`)

Parity algebra for the candidate `a_n = log(n+2)·1_{n+2 prime}`,
`b_n = 2C₂·1_{n odd}·∏_{p|n,p>2}(p−1)/(p−2)`, `w = a − b`:
`m` even ⟹ `b(m·n) = 0`; `m` even and `m·n > 0` ⟹ `a(m·n) = 0` and `w(m·n) = 0`;
whole even-multiplier inner sums vanish; nonnegativity; `b(1) = 2C₂`.
No analytic property of `b` is proved or assumed.

## G. Gate 0 (`Gate0Status.lean`)

* Interfaces, all **uninhabited**: `BombieriVinogradovShift2`,
  `BrunTitchmarshShift2`, `TwinComparisonProgressionMean`.
* Deterministic compilers (Lean-proved, reusing V4/V5): residue form
  (`BV + reindexing bridge → Gate-0 Type I` for `w = a − b`) and multiplicative
  form (prime side + comparison side → Type I with summed target).
* `GATE0 RESEARCH STATUS: opusAuditedAnalyticPass`;
  `GATE0 LEAN STATUS: conditionalCompiler` (analytic inputs external).
  Both proved `≠ leanProved`.

## H. Gate 2 controlling interface (`N2CellSumInterface.lean`)

* `N2CellData`: ε, dimension `k`, `H₂` cells, prefix prime factors, final-prime
  interval `J`, `H`-weight, shifted-prime weight, geometric mass.
* `FMN2CellSumUpperAtScale` (= `FM_N2_CELLSUM_UPPER45`), **uninhabited**:
  `total mass ≤ (x / log x) · (geometricMass + error)` — aggregate, **not**
  pointwise.
* `cellSum_does_not_give_pointwise` — the pointwise short-cell estimate is
  strictly stronger than the controlling target.
* Deterministic compiler chain (Lean-proved): two-linear-forms upper sieve per
  cell + prefix-cell decomposition + aggregate remainder control ⟹
  `FM_N2_CELLSUM_UPPER45`.
* `EpsilonUniformN2` (**uninhabited**) and the ε-uniform compiler: a bound for
  each admissible ε together with ε-uniformity of the error family gives one
  error constant valid throughout the admissible range.  (The V5 separation
  theorem shows the fixed-ε statement alone does not.)
* Theorem-8.3 insertion (Lean-proved): with the external mass bound
  `geometricMass ≤ C·ε` the controlling bound becomes `(x/log x)·(C·ε + err)`.

## I. Gate-2 status and patch hook (`Gate2Status.lean`)

```
GATE2:        OPEN
FIRST OPEN:   FM-N2-CELLSUM-UPPER45
RESEARCH:     Gate2ReducedToOneSourceSpecificAggregateUpperSieveLemma
```

`gate2_not_closed` and `gate2_not_conditionalClosed` are proved; neither
`Gate2Closed` nor `Gate2ConditionalClosed` is recorded.

`N2ProVerdict = pending | pass | reducedToExplicitSieveRemainder |
shortIntervalFail | epsilonUniformityFail | endgameFail`; current value
`pending`.  `verdict_never_leanProved`: **no** verdict, including `pass`, maps to
`leanProved`; `pass` maps to `opusAuditedAnalyticPass`.

## J. Conditional endgame DAG (`ConditionalEndgame.lean`)

`ShiftedPrimeFMEndgamePackage` with the explicit fields `gate0TypeI`,
`comparisonRegularity`, `fullFMTypeII`, `n2CellSumUpper`, `epsilonUniformity`,
`theorem83Mass`, `fmPositiveCertificate`, `weightedTwinMassPositive`, plus
projection lemmas.  The only Lean deduction is the finite V4 step
positive twin mass ⟹ explicit twin pair.  `no_endgamePackage_from_nothing`
shows the package is contentful.  **Twin-prime infinitude is NOT declared.**

## K. Counterguards (`Counterguards.lean`)

1. `width_arithmetic_not_twin_primes` — `1/6 > 0.1663` ≠ twin primes.
2. `gate0AuditPass_not_leanProof` — Gate-0 analytic pass ≠ Lean proof.
3. `gate0_and_gate2_not_fullTypeII` — Gate 0 + Gate 2 ≠ full Type II.
4. `fullTypeII_not_gate1AB` — Gate1A + Gate1B ≠ full Type II without a
   reassembly certificate.
5. `pointwise_stronger_than_cellSum` — pointwise short-cell estimate is strictly
   stronger than the cell-summed source-minimal target.
6. `fixedEpsilon_not_epsilonUniform` — fixed-ε `N₂` bound ≠ ε-uniform splice.
7. `ordinary_not_bounded_class` — ordinary `C⁻` ≠ bounded `C⁻_bd`.
8. `sourceSpecificRepair_not_general` — a source-specific Theorem-8.2 repair is
   not a theorem for arbitrary ordinary sequences.

## L. Uninhabited / external (unchanged policy)

Ford–Maynard Theorems 2.7, 4.16, 8.2, 8.3; Bombieri–Vinogradov; Brun–Titchmarsh;
comparison progression asymptotics; FM (b.1)/(b.2)/(w); the two-linear-forms
Selberg sieve; `FM-N2-CELLSUM-UPPER45`; the ε-uniform `N₂` splice; full
arbitrary-coefficient Ford–Maynard Type II; twin-prime infinitude.

## M. `#print axioms`

`BankStatus.lean` runs `#print axioms` on all 87 inhabited declarations of the
controlling layer.  Every one depends on at most `propext`, `Classical.choice`,
`Quot.sound`; 15 depend on no axioms at all.  No custom axiom exists anywhere in
the project.

## N. Trust-token audit

```
rg -n "sorry|admit|axiom|unsafe|opaque|native_decide|implemented_by" \
   RequestProject/NANC/V5/Controlling RequestProject/NANCBank.lean
```

Matches: only the `#print axioms` commands and the two comment lines of this
layer's `BankStatus.lean` that describe the allowed axioms.  No `sorry`,
`admit`, user `axiom`, `unsafe`, `opaque`, `native_decide` or
`@[implemented_by]` occurs in code, in this layer or anywhere else in the
project.

## O. Final report

```
BUILD:                              PASS
HEAD (start of run):                d608d6e  (root commit, no parent)
LEAN:                               4.28.0
MATHLIB:                            8f9d9cff6bd728b17a24e163c9402775d9e6a365
V4 PRESERVED:                       YES  (V5 also byte-identical)
FM THRESHOLD:                       1663/10000
PUBLISHED THM 2.7(b) INEQUALITY:    STRICT > 0.1663   (recorded)
1/6 WIDTH ARITHMETIC:               LEAN PROVED
TYPE-II LOWER ENDPOINT CONVENTION:  RECORDED  ((X/2)^θ < m ≤ X^(θ+ν))
P_EPSILON GEOMETRY:                 PROVED
THEOREM 4.16:                       UNINHABITED EXTERNAL INTERFACE
TWIN COMPARISON:                    DEFINED (parity/positivity algebra)
GATE0 RESEARCH STATUS:              OPUS-AUDITED ANALYTIC PASS
GATE0 LEAN STATUS:                  ANALYTIC INPUTS EXTERNAL
FM DEPENDENCY AUDIT:                RECORDED (displayed chain only)
GATE2 STATUS:                       OPEN
GATE2 FIRST OPEN:                   FM-N2-CELLSUM-UPPER45
TWO-LINEAR-FORM SIEVE:              UNINHABITED
EPSILON UNIFORMITY:                 UNINHABITED
THEOREM 8.3 MASS:                   UNINHABITED EXTERNAL INTERFACE
FULL FM TYPE II:                    UNINHABITED
CONDITIONAL ENDGAME DAG:            LEAN BANKED (dependencies as fields)
TWIN PRIME INFINITUDE:              NOT DECLARED
N2 PRO VERDICT:                     PENDING
SORRY / ADMIT / USER AXIOM:         0
FULL BUILD:                         PASS

FINAL BANK VERDICT:
    ARISTOTLE_NANC_V5_GATE02_CONTROLLING_BANK_PARTIAL
```
