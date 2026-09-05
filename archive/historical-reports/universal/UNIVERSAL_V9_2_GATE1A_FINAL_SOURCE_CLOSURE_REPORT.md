# UNIVERSAL v9.2 — GATE 1A CORRECTED FIXED-QUOTIENT / S1 SOURCE-CLOSURE

Continuation of the v9.1 safe extension. New files only; nothing modified.

---

## A. Regression / environment

Same as v9.1: Lean `v4.28.0`, pinned Mathlib, final `lake build` = 8435 jobs, 0 errors,
no deletions, no weakening.

## B. Corrected fixed-quotient normal form

File: `RequestProject/NANC/Gate1A/SafeExtensions/CorrectedFixedQuotient.lean`.

| declaration | content |
|---|---|
| `CorrectedFixedQuotientData` | the corrected finite datum `(p,q,r,m,d,c,s)` with its defining congruence |
| `correctedFixedQuotient_unique` | the corrected root is unique: two solutions `s, s'` of the corrected congruence coincide |
| `CorrectedFixedQuotientData.root_unique` | packaged form of the above |
| `oldNew_congruence_not_interchangeable` | **firewall**: the old and corrected congruences are not the same relation |
| `oldNew_rootSets_differ` | explicit finite witness that the two root sets differ |
| `oldNewQCoordinate_unitEquiv` | the old/new `q`-coordinates are related by an explicit unit equivalence of `ZMod q` |
| `oldNewQCoordinate_l2Preserved` | that equivalence is ℓ²-isometric |
| `oldNewQCoordinate_card_preserved` | and cardinality-preserving |

Consequence recorded honestly: the correction **changes the root set** but **does not
change the ℓ² energy** of the `q`-coordinate packet. Energy statements banked with the old
coordinate therefore survive; root-set statements do not.

## C. Corrected S1 closed form and Fourier identity

File: `CorrectedS1.lean`.

* Self-contained finite additive-phase API: `ee`, `ee_add`, `ee_neg`, `ee_period`,
  `ee_congr`, `ee_pow`, `ee_eq_one_iff`, `ee_scale`, `ee_collapse`, `sum_ee_range`.
* `betaCell`, `betaCellCentred`, `quotientCell_phaseFactor`, `betaCell_zero_eq`.
* `correctedS1_closed_form` — exact closed form of the corrected `S1` cell sum.
* `cellIndicator`, `correctedQuotient_fourier` — exact finite Fourier expansion of the
  centred quotient-interval kernel.
* `correctedQuotient_crt_phase` — the CRT phase split.

### Sign-convention finding (reported, not hidden)

* `correctedQuotient_authoritative_match` — with shift `c = -2` and kernel `e_C(-h s)`,
  **both** authoritative factors of the repository source are reproduced.
* `correctedQuotient_match_c_two` — with `c = +2` only the `q`-factor matches.

This is a pinned convention discrepancy in the informal sources; the Lean statement
records which convention actually reproduces the banked factors.

## D. Normalisation constant

* `Uq` with `Uq_div_q : Uq q H = q / H` — the corrected quotient normalisation is `q/H`.
* `Uq_ne_reciprocal_of_ne` — the frequently-quoted reciprocal form `H/q` is **not** equal
  to it unless `q = H`; a countermodel is supplied.

## E. Abstract amplitude

`centeredQuotientKernel_withAmplitude` — the finite identity is stable under multiplication
by an arbitrary abstract scalar amplitude. The literal source amplitude was **not**
invented from prose, so this is not a source transcription.

## F. Axiom / trust audit

`#print axioms` on the v9.2 public theorems returns only `propext`, `Classical.choice`,
`Quot.sound`. No `sorry`, `admit`, `axiom`, `opaque`, `unsafe`, `native_decide`,
`implemented_by` at code level anywhere in the repository.

## G. Status

```
CORRECTED_FIXED_QUOTIENT_NORMAL_FORM : PROVED (finite)
CORRECTED_S1_CLOSED_FORM             : PROVED (finite)
CORRECTED_QUOTIENT_FOURIER           : PROVED (finite)
Uq = q/H                             : PROVED
OLD/NEW COORDINATE ENERGY EQUIVALENCE: PROVED
FULL GATE SOURCE TRANSCRIPTION       : NOT CLAIMED
GATE 1A                              : OPEN
FULL TYPE II / TWIN PRIMES           : NOT DECLARED
```
