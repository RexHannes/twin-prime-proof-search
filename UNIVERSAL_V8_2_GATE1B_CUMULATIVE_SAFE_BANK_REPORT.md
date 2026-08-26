# UNIVERSAL + GATE 1B v8.2 — CUMULATIVE SAFE FORMAL BANK REPORT

All statements below are machine-checked in this repository unless explicitly
marked OPEN or INTERFACE.  **No new analytic theorem is claimed.**  Every new
declaration is either unconditional finite algebra (Tier 1) or carries its
analytic input as an explicit hypothesis (Tier 2).

---

## A. Scope and safety rules observed

* New material only; **no v8.1 file was modified, renamed, weakened or deleted**.
* `LEDGER.md` appended only.
* Forbidden tokens absent from all new files: `sorry`, `sorryAx`, `admit`,
  `axiom`, `opaque`, `unsafe`, `native_decide`, `@[implemented_by]`.
* No user axiom: every new public theorem depends at most on
  `propext`, `Classical.choice`, `Quot.sound`
  (`Gate1B/SafeExtensions/V82CumulativeStatus.lean` prints them all).
* Gate 1B is **not** declared closed; Full Type II and twin primes are **not**
  inferred.

## B. Reuse audit (nothing restated)

The following pre-existing results were reused rather than re-proved:

| Needed | Reused from |
| --- | --- |
| product/powerset ANOVA identity | `Universal.SafeAlgebra.finset_prod_add_eq_sum_powerset` |
| nine-box ANOVA | `Gate1B.SafeExtensions.fullNine_anova` |
| P44 partition ledger | `Gate1B.SafeExtensions.p44_only_320_has_hard_interior` |
| signed-parent Cauchy / sign erasure | `Gate1B.SafeExtensions.SignedParentCauchy` |
| reciprocity / CRT shell | `Gate1B.SafeExtensions.ReciprocityShell` |
| weighted Schur | `Universal.SafeAlgebra.weightedBlockSchur` |
| finite character diagonalisation | `Gate1B.SafeExtensions.QK5FiniteBank` |

## C. Tier 1 — permutation and product energy (`Universal/SafeAlgebra`)

* `PermutationEnergy.lean`: `l2Energy`, `l2Energy_comp_equiv(')`,
  `squareMulEquiv`, `squareTwist`, `squareTwist_l2Energy` (square-twist
  unitarity), `gramEntry`, `gramEntry_norm_le`, `squareTwist_gram_bound`,
  `squareTwist_gram_diagonal`.
* `ProductEnergyInjective.lean`: `l2Energy_pi_product` (exact factorisation of
  the ℓ² energy of a labelled product), `l2Energy_product_of_injective`, and
  `l2Energy_product_needs_injective` (injectivity is load-bearing).

## D. Tier 1 — critical-five geometry

`Gate1B/SafeAlgebra/CriticalFiveGeometry.lean`: `cLabelExponent`,
`aLabelExponent`, `labelExponent_total = 1`, `defectEnergyExponent j = 2j/9 − 1`,
`defectEnergy_le_neg_one_ninth_of_le_four`, `defectEnergy_order_four = −1/9`,
`defectEnergy_order_five = +1/9`, `defectEnergyExponent_strictMono`,
`defectEnergy_neg_iff_le_four`.  Capacity arithmetic only.

## E. Tier 1 — κ₄ normalisation

`Kappa4Normalization.lean`: `C(9,2)=36`, `C(9,4)=126`,
`kappa4_over_kappa2_eq_two_sevenths = 2/7`, `card_powersetCard_two/_four`,
`labelledFixedSubset_multiplicity_one`.

## F. Tier 1 — arithmetic source routers

* `TwoAdicSourceGuard.lean`: `odd_mul_add_two_not_even`,
  `odd_mul_not_congr_neg_two_mod_even`, `odd_mul_not_modEq_neg_two_mod_even`;
  and `emptyCount_does_not_determine_E` recording that an empty physical count
  does **not** determine `E`.
* `BNonunitGuard.lean`: on the shell `q ∣ B + 2`, no odd prime divisor of `q`
  divides `B` (`not_dvd_of_shell_congr`, `not_dvd_of_shell_modEq`,
  `shell_B_ne_zero_mod`).
* `SquarefreeSourceRouter.lean`: `squarefree_mul_prime_of_not_dvd`,
  `dvd_of_not_squarefree_mul_prime`, `squarefree_router_dichotomy`.

## G. Tier 1 — D₁₂ slot

* `D12CRT.lean`: `d12Value`, `d12_spec_left`, `d12_spec_right`,
  `d12_exists_unique`.
* `D12ResidueFactor.lean`: exact ℓ¹ and ℓ² factorisation of the D₁₂
  pushforward along a supplied CRT bijection.

## H. Tier 1 — seven-box energy and global zero mode

* `SevenBoxEnergy.lean`: `sevenBoxEnergy_factor`, `sevenBoxEnergy_of_injective`.
  No box count or density is asserted.
* `GlobalZeroMode.lean`: `zeroMode`, `nonzeroPart`,
  `centeredResidue_eq_zeroMode_add_nonzero`, `sum_nonzeroPart_eq_zero`,
  `nonzeroPart_independent_expectedTerm`, `zeroMode_rewrite_of_E_eq_MT`
  (hypothesis `E = MT` explicit).

## I. Tier 2 — finite Kloosterman theory

`FiniteKloosterman.lean` introduces the **supplied** interface
`AdditiveCharacterSystem q` (additivity, unimodularity, conjugation,
orthogonality) and the sum `kloosterman A B`, with `chi_zero`, `chi_ne_zero`
and the exact unit-reindexing invariance `kloosterman_scale`.

`KloostermanSquareMass.lean` proves the exact identity

    ∑_{A} S(A,B) · conj S(A,B) = q · #(ZMod q)ˣ

(`kloosterman_squareMass`, real form `kloosterman_squareMass_real`).  The
"`B` is a unit" hypothesis is **not** needed and is therefore absent.
**No Weil-type bound is claimed anywhere.**

`GCDTwist.lean`: with a supplied unit bijection and a supplied twisted phase
decomposition, `kloosterman_mul_coprime_twisted` and
`qk5_sharedG_twistedFactorization` give the exact multiplicative factorisation.

`RamanujanUnitBaseline.lean`: `ramanujan`, `ramanujan_zero = φ(q)`,
`ramanujan_fourier` (`∑_a c_q(−a) χ(an) = q·1_unit(n)`), and the baseline
`unit_indicator_baseline`.

## J. Tier 2 — capacity layer

* `GCDTwistUnitary.lean`: `gcdTwistFamily`, `gcdTwistFamily_energy`,
  `gcdTwistFamily_gram_bound`, `gcdTwistFamily_total_energy`.
* `GCDSchurCapacity.lean`: `gcdSchurCapacity` (specialisation of the banked
  weighted Schur bound), `gcdSchur_rowBudget_of_uniform`,
  `gcdSchur_exponentCapacity`, `gcdSchur_budget_mono`.
* `GBetaSourceMassCapacity.lean`: `gcdBetaMass_of_strata_bounds`,
  `gcdBetaMass_capacity_Exponent`, `gcdBetaWeightedSchur_of_bounds`.

## K. QK5 capacity margins (exact ℚ exponents)

`QK5CapacityMargins.lean` (every name contains `Capacity`/`Exponent`):

| Item | Value | Theorem |
| --- | --- | --- |
| PV medium margin in `Y` (`Q ≥ Y^{13/2}`, `C ≤ Y⁷/Q`) | `≤ −1/2` | `pvMedium_marginY_Exponent` |
| conversion `Y = X^{1/9}` | `−1/18` | `pvMedium_marginX_Exponent` |
| overlap point | `J = Y^{1/2}` | `overlapPointExponent` |
| overlap threshold | `C_* = Y^{2/3}` | `overlapThresholdExponent` |
| PV = large-sieve exponent | `−1/6` | `overlapExponents_agree` |
| overlap margin in `X` | `−1/54` | `overlapMargin_X_Exponent` |
| axis budget | `X^{-1/9}` | `axisBudgetExponent`, `axisBudget_negative_Exponent` |
| source mass `(D/Y)(Q²/D) = Q²/Y` | identity | `sourceMass_capacity_Exponent` |
| real form of the PV margin | `Y ≥ 1` | `pvMedium_marginY_Capacity` |

## L. Countermodels (all proved)

`CountermodelsV82.lean`:

* **A** sign erasure destroys cancellation;
* **B** the nonzero part does not determine the family;
* **C** the maximal fibre does not determine the ℓ² energy;
* **D** a trivial quotient modulus makes the CRT statement vacuous;
* **E** the zero-mode compiler is false without `E = MT`.

## M. Interfaces and compilers (nothing inhabited)

* `QK5InterfacesV82.lean` — **documentation only, zero declarations**: the five
  residual analytic interfaces (PV medium, large sieve, axis, GCD-β,
  Kloosterman cancellation) are listed as OPEN.
* `CapacityInterfacesV82.lean` — deterministic compilers taking the analytic
  estimate as an explicit hypothesis: `pvMedium_of_analyticHyp`,
  `overlap_of_ls_and_pv_hypotheses`, `axisBudget_of_axisBound`,
  `gcdBudget_of_sourceMassAndSchur`, plus
  `capacityCompiler_not_self_inhabiting`.
* `ZeroModeConditional.lean` — `zeroModeCompiler_of_E_eq_MT`,
  `zeroModeCompiler_partition`, `zeroModeCompiler_hypothesis_needed`.
* `ReassemblyAbstract.lean` — `GateFace`, `GateFaceCertificate`,
  `reassemble_of_face_certificates`, `gateFaceCertificate_not_automatic`,
  `reassembly_not_self_certifying`.  **No face certificate is inhabited.**

## N. Anti-self-reference guards

`capacityCompiler_not_self_inhabiting`, `gateFaceCertificate_not_automatic`,
`reassembly_not_self_certifying`, `zeroModeCompiler_hypothesis_needed`,
`emptyCount_does_not_determine_E`, `l2Energy_product_needs_injective` — each
shows that a hypothesis of the corresponding compiler is genuinely load-bearing
and cannot be manufactured from the conclusion.

## O. Axiom / regression audit

`lake build` succeeds repository-wide.  `Gate1B/SafeExtensions/V82CumulativeStatus.lean`
prints axioms for all new public theorems: only `propext`, `Classical.choice`,
`Quot.sound` (one countermodel uses `propext` alone).  No user axiom, no
`sorry`.

## P. What is still open

Gate 1B remains open.  The residual analytic interfaces of §M are not
inhabited, no Kloosterman cancellation is proved, and no face certificate
exists.  Consequently:

* Gate 1B: **NOT CLOSED**;
* Full Type II: **NOT INFERRED**;
* Twin primes: **NOT INFERRED**.

---

## §35 VERDICT

```
ARISTOTLE_V8_2_GATE1B_CUMULATIVE_SAFE_BANK_PARTIAL

BUILD:                      lake build succeeds (repository-wide)
SORRY:                      none in new files
USER AXIOMS:                none
V8.1 BANK:                  PRESERVED (no file modified)
NEW SAFE ALGEBRA:           20 new modules, all sorry-free
TIER 1 (unconditional):     permutation/product energy, critical-five
                            exponents, kappa4, 2-adic guard, B-non-unit guard,
                            squarefree router, D12 CRT + pushforward,
                            seven-box energy, global zero mode, countermodels
TIER 2 (hypothesis-carrying): finite Kloosterman interface, exact square mass,
                            unit-scale invariance, twisted CRT factorisation,
                            Ramanujan unit baseline, capacity compilers
QK5 MARGINS:                PV Y^-1/2 = X^-1/18; overlap -1/6 = X^-1/54;
                            axis X^-1/9  (all exact ℚ arithmetic)
COUNTERMODELS:              A,B,C,D,E all proved
ANALYTIC INTERFACES:        OPEN, uninhabited (documented, not asserted)
GATE1B:                     NOT CLOSED
FULL TYPE II:               NOT INFERRED
TWIN PRIMES:                NOT INFERRED
```
