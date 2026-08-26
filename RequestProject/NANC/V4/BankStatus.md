# NANC V4 — GATE 0/2 FORD–MAYNARD ENDGAME SAFE BANK

## A. Repository state

* Repository HEAD at the start of this run: `b068673` ("Initial commit"), which is
  the root commit — it has **no parent**.
* The repository contained **no pre-existing NANC bank**: the only Lean file was
  `RequestProject/Main.lean` (a set-options preamble). There is therefore no
  V2/V3 bank in this repository to preserve; no prior history has been rewritten,
  reset or fabricated. `RequestProject/Main.lean` is unchanged.

## B. Versions

* Lean: `4.28.0` (commit `7e01a1bf5c70fc6167d49c345d3bf80596e9a79b`).
* Mathlib: checked out at `8f9d9cff6bd728b17a24e163c9402775d9e6a365`
  (the manifest records mathlib as a local path dependency).

## C. Regression

* `lake build` — **PASS** (all targets, including `RequestProject.NANCBank`
  and `RequestProject.NANC.V4`).
* `RequestProject/Main.lean` untouched; nothing was deleted or overwritten.

## D. Ford–Maynard finite predicates (`FordMaynardPredicates.lean`)

* `FMTypeIAtScale X R intervals tau w target` — the Type-I shape is preserved
  exactly: outer `m`-sum, `τ^B(m)` outer weight, maximum over the interval family
  (encoded by universally quantifying over interval *selection functions*, which
  avoids nonemptiness side conditions), multiplicative argument `w(m·n)`, and the
  dyadic window `X/2 < m·n ≤ X` written as `X < 2·m·n ∧ m·n ≤ X`.
  **No inhabitant.**
* `FMTypeIIAtScale X R Rn dwM dwN w target` — the universal quantifier over
  **arbitrary** divisor-bounded complex `ξ, κ` appears literally:
  `∀ ξ κ, DivisorBoundedCoeff … → DivisorBoundedCoeff … → ‖∑∑ ξ_m κ_n w(mn)‖ ≤ target`.
  **No inhabitant.**
* Firewall `sourceSpecificTypeII_not_definitionally_FMTypeII` — a **finite
  counterexample**: a bound for one fixed coefficient pair holds while the
  universal Type-II statement fails on the same data.

Neither predicate is asymptotic; `x^γ` is never invented. The finite ranges are
supplied as data, and the passage from finite-at-scale to asymptotic form is part
of the external analytic layer.

## E. Width certificate (`Parameters.lean`, `WidthLedger.lean`)

Exact rational arithmetic in `ℚ` — no decimals, no floating point:

* `gamma0 = 1/2`, `theta0 = 0`, `nu0 = 1/6`, `fmThreshold = 1663/10000`;
* `one_sixth_gt_fm_threshold : fmThreshold < nu0` — **Lean proved**;
* `one_sixth_threshold_margin : nu0 - fmThreshold = 11/30000` — **Lean proved**;
* `shrinkParams eps = (1/2 - eps, eps, 1/6 - 2·eps)`;
* `shrunk_nu_gt_threshold_of_eps_small` : `0 < eps`, `eps < 11/60000`
  ⟹ `1/6 - 2·eps > 1663/10000` — **Lean proved**
  (the hypothesis `0 < eps` is retained because it is part of the intended
  parameter range, though the inequality needs only the upper bound);
* `shrunk_theta_add_nu : θ(ε) + ν(ε) = 1/6 - ε`, so the Type-II exponent interval
  is `[ε, 1/6 - ε]` (`typeIIInterval_eq`) — **Lean proved**;
* `fm_central_width_one_sixth_conditional` and `fm_shrunk_width_conditional` are
  **conditional**: they apply the uninhabited interface `FMPositiveCentralWidth`
  to the rational inequality. They assert nothing about whether that interface
  holds.

Firewall `width_arithmetic_alone_not_positivity`: the rational inequality holds
while there exist sieve coefficients with `C⁻(1/2,0,1/6) ≤ 0`. Hence

    PARAMETER_RANGE_MATCH ≠ THEOREM_APPLICATION.

## F. Gate-0 compiler (`TypeICompiler.lean`)

* `MaximalWeightedBVShiftedPrime` — analytic input, prime side. **Uninhabited.**
* `ComparisonProgressionMean` — analytic input, comparison side. **Uninhabited.**
* `shiftedPrime_inputs_imply_FMTypeI` — **PROVED**. From the two inputs (and
  nonnegativity of the outer weight), `FMTypeIAtScale` holds for `w = a - b`
  with target `targetA + targetB`. The proof uses only `w = a - b`, the triangle
  inequality and finite sum bounds; all analytic content stays in the explicit
  hypotheses.

Status: `GATE0_FM_TYPEI_COMPILER: LEAN_BANKED (conditional)`,
`GATE0_ANALYTIC_INPUT: OPEN / EXTERNAL`.

## G. Shifted-prime comparison model (`ShiftedPrimeModel.lean`, `ComparisonModel.lean`)

* `shiftedPrimeWeight n = if (n+2).Prime then log(n+2) else 0`, with
  nonnegativity, vanishing off the shifted primes, and positivity for `n ≥ 1`.
* Generic `PrimeWeight` structure for use when `Real.log` is inconvenient.
* `ShiftedPrimeComparisonModel` with `a, b ≥ 0` and `w = a - b`.
* `twinLocalFactor C2 n` = `0` on even `n`, otherwise `2·C₂·∏_{p ∣ n, p > 2} (p-1)/(p-2)`.
  Proved: nonnegativity for `C₂ ≥ 0`, even-support vanishing, value `2·C₂` at
  `n = 1`, the finite-product decomposition, and the new-odd-prime multiplication
  rule. **No PNT, progression mean, or singular-series asymptotic is proved.**

## H. Type-II universal-coefficient firewall (`TypeIICompiler.lean`)

* `Gate1AOutput`, `Gate1BOutput` — abstract, source-specific packet bounds.
* `FullFMTypeIIReassembly` — the full reassembly obligations (all dyadic blocks
  covered, arbitrary coefficients retained, no packet omitted, exceptional
  sectors routed, multiplicities controlled, exact main subtraction, no
  double-spending). **Uninhabited.**
* `gate1AB_certificate_imp_full_reassembly` — only a reassembly certificate
  yields the full statement.
* `gate1A_gate1B_not_FMTypeII` — **finite counterexample**: Gate-1A and Gate-1B
  outputs exist on data where the universal Type-II hypothesis is false.

## I. C_bd normalization firewall (`Counterguards.lean`)

* `scale_comparison_prime_mass : primeMass S (b/L) = primeMass S b / L` — **PROVED**.
* `scale_comparison_prime_mass_lt`: for `L > 1` and positive prime mass, the
  rescaled mass is strictly smaller — **PROVED**.
* `ordinary_positive_ne_bounded_positive`: there are data where `C⁻_bd`-positivity
  holds and ordinary `C⁻`-positivity fails, so the two must never be identified.

Status: `C_bd compatibility: ANALYTIC / SEQUENCE-CLASS INTERFACE, NOT AUTOMATIC.`

## J. N₂ repair interface (`N2RepairInterface.lean`)

* `N2Region`, `N2UpperBound`, `FMShiftedPrimeN2Upper` — explicit finite
  inequality on an abstract exceptional region. **Not inhabited for any
  non-degenerate region**; only the vacuous empty-region instance
  `n2Upper_of_empty` is available and is explicitly labelled as carrying no
  analytic content.
* `FMShiftedPrimeEndgameSplice R target L` — the (strictly stronger) claim that
  the `N₂` bound may substitute for the bounded-sequence step. **Uninhabited.**
* `n2_alone_does_not_close_gate2` — the interface alone does not close Gate 2.
* Optional two-linear-forms upper-sieve scaffold (`TwoLinearFormsUpperSieveInput`,
  `TwoLinearFormsUpperSieveOutput`, `Gate2N2SieveApplication`) — interfaces only;
  no sieve theorem is invented or instantiated.

## K. Twin-mass finite implication (`TwinMass.lean`)

* `weightedTwinMass S = ∑_{p ∈ S, p prime} shiftedPrimeWeight p`.
* `positive_weightedTwinMass_exists_twin` — **PROVED**: positive weighted twin
  mass yields `∃ p ∈ S, p` and `p+2` prime.
* `positive_genericTwinMass_exists_twin` — same for an abstract `PrimeWeight`.
* `EventuallyPositiveTwinMass` — **uninhabited** interface; the conditional
  theorem `eventuallyPositiveTwinMass_imp_infinite` derives twin-prime infinitude
  *from it*. Twin-prime infinitude is **NOT declared**.

## L. Analytic interfaces still uninhabited

maximal weighted Bombieri–Vinogradov; comparison progression mean; FM comparison
b.1 / b.2 / growth condition; Ford–Maynard Theorem 2.7 positivity
(`FMPositiveCentralWidth`); bounded-variant positivity
(`FMBoundedPositiveNearCentral`); full FM Type-II reassembly;
`FMShiftedPrimeN2Upper` (non-degenerate); `FMShiftedPrimeEndgameSplice`;
two-linear-forms upper sieve; eventual positivity of twin mass; twin-prime
infinitude.

## M. `#print axioms`

`RequestProject/NANC/V4/BankStatus.lean` prints axioms for every Lean-banked
theorem listed above. Observed results: each is either

* `does not depend on any axioms`, or
* `depends on axioms: [propext]`, or
* `depends on axioms: [propext, Classical.choice, Quot.sound]`.

No custom axiom appears anywhere.

## N. Trust-token audit

`rg -n "sorry|admit|axiom|unsafe|opaque|native_decide|implemented_by"` over
`RequestProject/` returns only:

* the `#print axioms` audit lines and the words "axiom"/"axioms" in comments of
  `RequestProject/NANC/V4/BankStatus.lean`.

There are **no** `sorry`, `admit`, `axiom` declarations, `unsafe`, `opaque`,
`native_decide`, or `@[implemented_by]` occurrences in code — neither in V4 nor
anywhere else in `RequestProject/` (the `.lake/` dependency tree is not part of
this repository's sources and was not audited).

## O. Build status

`lake build`: **PASS**, 0 errors, and `RequestProject.NANC.V4` and
`RequestProject.NANCBank` both build.

---

## FINAL VERDICT

```
BUILD STATUS:                       PASS
COMMIT:                             743ad52, 28e3336 (+ final report commit)
PARENT:                             b068673 (root commit; no parent)
LEAN VERSION:                       4.28.0
MATHLIB:                            8f9d9cff6bd728b17a24e163c9402775d9e6a365
OLD NANC BANK PRESERVED:            N/A — none existed; Main.lean unchanged
FORD-MAYNARD TYPE-I PREDICATE:      DEFINED
FORD-MAYNARD TYPE-II PREDICATE:     DEFINED
ARBITRARY xi,kappa QUANTIFIER:      PRESENT
1/6 > 0.1663:                       LEAN PROVED
EXACT MARGIN:                       11/30000
EPSILON-SHRUNK RANGE ARITHMETIC:    PROVED
FORD-MAYNARD THEOREM 2.7:           UNINHABITED EXTERNAL INTERFACE
SHIFTED-PRIME MODEL:                DEFINED
TWIN COMPARISON CANDIDATE:          DEFINED (elementary algebra only)
COMPARISON b.1:                     UNINHABITED
COMPARISON b.2:                     UNINHABITED
MAXIMAL WEIGHTED BV:                UNINHABITED
GATE-0 DETERMINISTIC COMPILER:      PROVED
GATE-0 ANALYTIC TYPE-I:             OPEN
FULL FM TYPE-II REASSEMBLY:         UNINHABITED
C_bd NORMALIZATION FIREWALL:        PROVED
N2 SHIFTED-PRIME UPPER REPAIR:      UNINHABITED
FORD-MAYNARD ENDGAME SPLICE:        UNINHABITED
POSITIVE WEIGHTED TWIN MASS -> TWIN PAIR:  PROVED
TWIN PRIME INFINITUDE:              NOT DECLARED
GATE 0:                             FORMAL COMPILER BANKED / ANALYTIC INPUT OPEN
GATE 2:                             CONDITIONAL ENDGAME INTERFACES BANKED / NOT CLOSED
SORRY / ADMIT / USER AXIOM IN NEW V4 CODE:  0
AXIOM AUDIT:                        propext / Classical.choice / Quot.sound only
FULL BUILD:                         PASS
REPORT:                             RequestProject/NANC/V4/BankStatus.md
LEDGER:                             APPENDED (LEDGER.md)

FINAL BANK VERDICT:
    ARISTOTLE_NANC_V4_GATE02_FM_ENDGAME_SAFE_BANK_PARTIAL
```
