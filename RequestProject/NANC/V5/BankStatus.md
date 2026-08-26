# NANC V5 — GATE 0 / GATE 2 AUDITED SHIFTED-PRIME FORD–MAYNARD INTERFACE BANK

## A. Repository state

* Commit at the start of this run: `262cbd0` (`Initial commit`), **no parent**
  (single-commit history; nothing was fabricated and nothing was reset).
* The repository contained the V4 bank (`RequestProject/NANC/V4/…`), the
  aggregator `RequestProject/NANCBank.lean`, `LEDGER.md` and
  `RequestProject/Main.lean`.

## B. Versions

* Lean `4.28.0`.
* Mathlib pinned by the project manifest at
  `8f9d9cff6bd728b17a24e163c9402775d9e6a365`.

## C. Regression

* Baseline `lake build`: **PASS** (8044 jobs) before any change.
* Final `lake build`: **PASS** (8060 jobs), including
  `RequestProject.NANC.V4`, `RequestProject.NANC.V5`,
  `RequestProject.NANCBank`.
* **V4 is unchanged**: `git diff 262cbd0 HEAD -- RequestProject/NANC/V4` is
  empty.  `RequestProject/Main.lean` and the existing part of `LEDGER.md` are
  untouched; `RequestProject/NANCBank.lean` was modified only to add the V5
  import.

## D. Layout

`RequestProject/NANC/V5.lean` and

```
RequestProject/NANC/V5/
  AuditStatus.lean          ComparisonRegularity.lean   FullTypeIIInterface.lean
  Provenance.lean           Gate0Interfaces.lean        Gate2Interfaces.lean
  FordMaynardSource.lean    N2Geometry.lean             ConditionalTwinEndgame.lean
  TwinComparison.lean       EpsilonLedger.lean          Counterguards.lean
  ComparisonEuler.lean      BankStatus.lean             Main.lean
  BankStatus.md
```

Namespace `NANC.V5`; V4 is imported and reused, never duplicated.

## E. Provenance / audit-status system (LEAN PROVED)

`AuditStatus` = `leanProved | externallyPublished | opusAudited | researchClaim |
uninhabited | refuted | sourceMissing`, with the predicates `IsLeanEvidence`
and `IsNonLeanEvidence` and the firewalls

* `opusAudited ≠ leanProved`,
* `researchClaim ≠ externallyPublished`,
* `uninhabited ≠ leanProved`,
* `externallyPublished ≠ leanProved`,
* `not_leanEvidence_and_nonLeanEvidence` — no status is both,
* `toV4_not_proofBearing` — the translation into the V4 status system can never
  promote a non-Lean status to a V4 proof-bearing one.

`Provenance` records (status, source name, version, scope, notes) carry these
guarantees: `Provenance.not_leanEvidence_of_nonLean`, `Provenance.not_both`.

## F. Ford–Maynard source metadata (DATA ONLY)

`fordMaynardPaper` records *On the theory of prime-producing sieves*,
arXiv:2407.14368, public 107-page version, status `externallyPublished`.
The published Theorem-2.7(b) threshold is banked as the exact rational
`publishedThreshold = 1663/10000`.  An internal numerical witness of roughly
`0.16623` is recorded **as metadata only** (`internalNumericalWitnessNote`,
status `opusAudited`) and is never substituted for the published value.
The V4 exact facts are re-exported, not re-proved:
`v5_one_sixth_gt_threshold` (`1663/10000 < 1/6`) and
`v5_margin` (`1/6 − 1663/10000 = 11/30000`).

## G. Twin comparison candidate and finite algebra (LEAN PROVED)

* `twinComparisonWeight C₂` (= the V4 local factor), with nonnegativity for
  `C₂ ≥ 0`, even-support vanishing, and value `2C₂` at `n = 1`.
* The candidate triple `a` = shifted-prime log weight, `b` = comparison weight,
  `w = a − b`, as a V4 comparison model (`twinCandidateModel`), plus the
  abstract positive-prime-weight variant (`genericCandidateModel`).
* `prod_one_add_eq_powersetSum` : `∏_{p∈P}(1+f p) = ∑_{T⊆P} ∏_{p∈T} f p`.
* `oddLocalRatio_eq_one_add` : `(p−1)/(p−2) = 1 + 1/(p−2)` for primes `p > 2`.
* `oddPrimeProduct_eq_squarefreeDivisorSum`,
  `twinLocalFactor_eq_squarefreeDivisorSum` — the local factor as a sum over
  squarefree divisors of its odd prime support.
* `oddPrimeProduct_split_at`, `twinComparisonWeight_split_at` — the
  multiplicative split at a fixed multiplier `m`.
* `twinComparison_mul_argument_expansion` — the expansion of
  `∏_{p∣n, p∤m}(1+1/(p−2))` as a squarefree-divisor sum.
* `truncatedTwinEulerProduct_pos`, `truncatedTwinEulerProduct_mono` —
  elementary facts about *truncated* Euler products only.

## H. Euler-product and progression interfaces (UNINHABITED)

* `TwinConstantEulerIdentity C₂` — convergence of the truncated products
  `∏_{p>2}(1 + 1/(p(p−2)))` to `C₂⁻¹`.  **No inhabitant.**
* `TwinComparisonProgressionMean` — the uniform interval estimate
  `∑_{n∈I} b(m·n) = (m/φ(m))|I| + error`.  **No inhabitant.**

## I. Comparison regularity (UNINHABITED)

`TwinComparisonData` carries sequence, scale, `ε`, multiplier range, interval
family and admissible error; `FMComparisonB1Twin`, `FMComparisonB2Twin`,
`FMConditionWTwin` are the three conditions, and
`TwinComparisonRegularityPackage` bundles them (no default constructor).
`no_regularity_package_from_nothing` shows the package is contentful.

## J. Gate-0 interfaces and compilers

UNINHABITED analytic inputs:

* `WeightedMaximalBVShift2Residue` — `τ^B`-weighted maximal Bombieri–Vinogradov
  for the shifted primes in the residue class `2 mod q`, with the interval
  maximum and the required saving explicit;
* `Shift2ReindexingBridge` — the divisor-switching passage from the
  residue-class form to the multiplicative form;
* `WeightedMaximalBVShift2`, `TwinComparisonProgressionInput` — the
  multiplicative-form prime-side and comparison-side inputs (V4 interfaces).

LEAN PROVED (deterministic bookkeeping only):

* `shift2_residue_bridge_imp_multiplicative`,
* `weightedBV_and_comparison_imply_gate0TypeI`,
* `shift2_bridge_imply_gate0TypeI`.

No fake `τ^B` absorption: `TauWeightNeedsAnalyticInput` is a provenance marker
with status `uninhabited`, and `tauBounded_not_weightedBV` exhibits data where
the outer weight is bounded and the BV input fails.

## K. Theorem-8.2 boundedness-use audit (METADATA)

`FMTheorem82DependencyAudit` records `boundednessUsedInN2`,
`boundednessUsedElsewhere` and notes, with `opusAudited` provenance.  The
primary-source observation recorded is that an explicit pointwise use appears in
the final `N₂` estimate; any claim that this is the *only* (indirect) use stays
external-audit metadata.  `n2Use_does_not_exclude_otherUses` proves that the
first assertion does not exclude the second.

## L. N₂ geometry and the sieve compiler

* `N2RegionData` — exceptional set, factorization dimension `k`, prime-factor
  lower bound, geometric mass, `H`-weight bound.
* `ShiftedPrimeN2UpperAtScale` — `∑_{n∈N₂} a_n|H(n)| ≤ C·(x/log x)·mass + err`.
  **UNINHABITED.**
* `TwoLinearFormsUpperSieveData` / `TwoLinearFormsUpperSieve` — the upper-bound
  sieve for `p`, `M·p+2`, with admissibility, interval length, gcd conditions
  and singular-factor bound as explicit hypotheses.  **UNINHABITED.**
* `twoLinearForms_and_geometry_imply_n2Upper` — **LEAN PROVED** compiler:
  pointwise sieve bounds along a disjoint factorization decomposition, plus a
  geometric summation input, give the `N₂` bound.
* `pointwiseSieve_not_uniformN2` — pointwise bounds are not the aggregate bound.

## M. ε-ledger and uniformity firewall

* `EpsAdmissible ε` := `0 < ε < 11/60000`; on this range the V4 arithmetic gives
  `1/6 − 2ε > 1663/10000` and `θ(ε) + ν(ε) = 1/6 − ε`.
* `N2UniformInEpsilon` — **UNINHABITED**.
* `n2ForEachEpsilon_not_uniformInEpsilon` — **LEAN PROVED** separation: the
  family `F ε = 1/ε` bounds a quantity for every admissible `ε` and is
  unbounded on that range.  A bound for each fixed `ε` is therefore never the
  ε-uniform statement the splice needs.

## N. Full Ford–Maynard Type II at 1/6

`FullFMTypeIIAtOneSixth` quantifies over every exponent `σ ∈ [ε, 1/6−ε]` and, in
the V4 predicate, over **all** divisor-bounded complex `ξ, κ`.  **UNINHABITED.**
`Gate1ABFullReassemblyCertificate` carries the V4 packet certificate *and* the
conversion into the interval statement; `gate1AB_not_fullTypeIIAtOneSixth`
proves, with a finite counterexample, that Gate-1A + Gate-1B outputs alone never
give it.

## O. Gate-2 interfaces

* `T82SpliceData` / `FMShiftedPrimeT82Splice` — the shifted-prime Theorem-8.2
  splice, whose fields are comparison regularity, Gate-0 Type I, full Type II,
  the `N₂` upper bound, ε-uniformity, the published non-`N₂` inputs, and the
  legality of the substitution.  **UNINHABITED**; there is deliberately **no**
  `gate2_closed` theorem, and `no_t82_splice_from_nothing` shows the structure is
  contentful.
* `FMTheorem83H2Mass` — `mass(H₂) ≤ C·ε` on the admissible range, provenance
  `externallyPublished`.  **UNINHABITED here.**

## P. Conditional twin endgame

`EndgameData` / `ShiftedPrimeEndgamePackage` bundles comparison regularity,
Gate-0 Type I, full Type II, the Theorem-8.2 splice, the Theorem-8.3 mass bound,
a positive sieve constant, **and** the conclusion (positivity of the weighted
twin mass) as a field — no deep analysis is hidden in a proof term.
`endgamePackage_gives_twin_pair` (LEAN PROVED, via the V4 finite lemma) extracts
an explicit twin-prime pair, and
`endgamePackagesAtAllScales_imp_infinitely_many_twins` derives infinitude from
the **uninhabited** eventual-existence interface.  **Twin-prime infinitude is not
declared.**

## Q. Permanent counterguards (all LEAN PROVED)

1. `width_arithmetic_not_fullTypeII` — `1/6 > 0.1663` ≠ full Type II.
2. `auditPass_not_leanProof` — an external audit PASS ≠ a Lean proof.
3. `n2Use_not_exclusive` — one explicit use of boundedness ≠ no indirect uses.
4. `pointwiseSieve_not_uniformIntegration` — pointwise sieve ≠ uniform `N₂`
   geometric integration.
5. `fixedEps_not_uniformEps` — `N₂` for fixed `ε` ≠ ε-uniform splice.
6. `gate0Compiler_not_weightedBV` — the Gate-0 compiler ≠ weighted maximal BV.
7. `gate0_gate2_not_twins_without_typeII` — Gate 0 + Gate 2 ≠ twin primes
   without full Type II.

## R. Axiom audit

`RequestProject/NANC/V5/BankStatus.lean` runs `#print axioms` on **every**
inhabited V5 theorem.  Every one depends on at most
`propext`, `Classical.choice`, `Quot.sound`; several depend on `propext` only or
on nothing at all.  No custom axiom is declared anywhere.

## S. Trust-token audit

```
rg -n "sorry|admit|axiom|unsafe|opaque|native_decide|implemented_by" \
   RequestProject/NANC/V5 RequestProject/NANCBank.lean
```

* Code occurrences: **none**.
* Remaining matches: the `#print axioms` commands in
  `RequestProject/NANC/V5/BankStatus.lean` and the word "axiom" in comments.
* Pre-existing V4 matches are of the same two kinds and are unchanged.

## T. Final report

```
BUILD:                          PASS
HEAD (start of run):            262cbd0  (no parent)
LEAN:                           4.28.0
MATHLIB:                        8f9d9cff6bd728b17a24e163c9402775d9e6a365
V4 PRESERVED:                   YES (byte-identical)
V5 PROVENANCE SYSTEM:           PROVED
TWIN LOCAL FACTOR ALGEBRA:      PROVED
SQUAREFREE DIVISOR EXPANSION:   PROVED
INFINITE EULER PRODUCT:         UNINHABITED
COMPARISON PROGRESSION MEAN:    UNINHABITED
FM b.1:                         UNINHABITED
FM b.2:                         UNINHABITED
FM condition (w):               UNINHABITED
WEIGHTED MAXIMAL BV:            UNINHABITED
GATE0 DETERMINISTIC COMPILER:   PROVED
THEOREM-8.2 BOUNDEDNESS AUDIT:  METADATA
TWO-LINEAR-FORM SIEVE:          UNINHABITED
N2 SHIFTED-PRIME UPPER:         UNINHABITED
EPSILON UNIFORMITY:             UNINHABITED (non-implication PROVED)
THEOREM-8.2 SPLICE:             UNINHABITED
FULL FM TYPE II:                UNINHABITED
CONDITIONAL TWIN ENDGAME DAG:   PROVED
TWIN PRIME INFINITUDE:          NOT DECLARED
SORRY / ADMIT / USER AXIOM:     0
FULL BUILD:                     PASS

FINAL BANK VERDICT:
    ARISTOTLE_NANC_V5_GATE02_AUDITED_INTERFACE_BANK_PARTIAL
```
