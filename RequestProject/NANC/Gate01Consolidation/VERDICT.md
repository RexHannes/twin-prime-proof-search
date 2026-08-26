# ARISTOTLE GATE 0–1 CONSOLIDATION VERDICT

## Build report

```text
LEAN VERSION:            4.28.0
MATHLIB VERSION/COMMIT:  v4.28.0 (8f9d9cff6bd728b17a24e163c9402775d9e6a365)
FILES CREATED:
  RequestProject/NANC/Gate01Consolidation/Centering.lean
  RequestProject/NANC/Gate01Consolidation/NonzeroOrthogonality.lean
  RequestProject/NANC/Gate01Consolidation/ESeparation.lean
  RequestProject/NANC/Gate01Consolidation/CRTCentering.lean
  RequestProject/NANC/Gate01Consolidation/ShiftInverse.lean
  RequestProject/NANC/Gate01Consolidation/PrimeCovariance.lean
  RequestProject/NANC/Gate01Consolidation/ProductModeObstruction.lean
  RequestProject/NANC/Gate01Consolidation/DeterminantIdentity.lean
  RequestProject/NANC/Gate01Consolidation/DirectGaussReassembly.lean
  RequestProject/NANC/Gate01Consolidation/R9Regrouping.lean
  RequestProject/NANC/Gate01Consolidation/ExponentThresholds.lean
  RequestProject/NANC/Gate01Consolidation/AnalyticInterfaces.lean
  RequestProject/NANC/Gate01Consolidation/SourceInterfaces.lean
  RequestProject/NANC/Gate01Consolidation/OverclaimKillTests.lean
  RequestProject/NANC/Gate01Consolidation/StatusLedger.lean
  RequestProject/NANC/Gate01Consolidation/Main.lean
  RequestProject/NANC/Gate01Consolidation/BankStatus.md
  RequestProject/NANC/Gate01Consolidation/VERDICT.md
FILES MODIFIED:
  RequestProject/NANCBank.lean  (one new import)
  LEDGER.md                     (consolidation status table appended)
BUILD:                   lake build PASSED
ERRORS:                  0
WARNINGS:                0 in the new files
SORRY:                   0
ADMIT:                   0
CUSTOM AXIOMS:           0   (only 21 `#print axioms` audit commands and one
                              prose mention of the word)
OPAQUE STUBS:            0
@[implemented_by]:       0
JOB COUNT:               8224
```

`#print axioms` on the representative theorems of the bank reports only
`propext`, `Classical.choice`, `Quot.sound`; the ledger consistency theorems
depend on no axioms at all.

## A. E-SEPARATION
Status: provedFinite.
Theorems: `esep1` (ESEP1), `esep2` (ESEP2),
`nonzeroFreq_independent_of_expected`, with `congrSum`, `fullSum`,
`fourierHat`, `nonzeroFreqTerm`, and `nonzero_orthogonality_shift`.

## B. NONZERO ORTHOGONALITY
Status: provedFinite.
Theorems: `sum_ec_orthogonality`, `sum_ec_nonzero` (NZORTH),
`sum_ec_nonzero_div`, `dvd_add_two_inv_iff` and `zmod_add_two_inv_iff`
(RES_EQ); supporting `ec`, `ec_add`, `ec_eq_one_iff`, `ec_congr`, `ec_natMul`.
Ledger note: `UNCENTERED_N1_IS_NOT_FORCED_BY_NONZERO_ORTHOGONALITY` — only the
identity is formalised; no theorem says the uncentered N1 estimate is false.

## C. CRT CENTERING
Natural: `rho`, `indicator_mul_coprime`, `rho_mul_coprime` (CRT-CENTER);
frequency modes `CRTMode`, `crtMode`, `crtMode_*_iff`; product-frequency
parametrisation `crtFreq`, `crtFreq_bijective`, `crtFreq_rat`, `ec_crt_split`.
Source-density conditional: `rhoSrc`, `DensityMultiplicative` (DENS-MULT, an
explicit uninstantiated hypothesis), `rhoSrc_mul_coprime` (CRT-SRC).

## D. SHIFT-INVERSE
Status: `SHIFT_INVERSE_ALGEBRA = PROVED` (`coprime_shift`, `shift_inverse`,
`shift_phase`); `SHIFT_INVERSE_ANALYTIC_GAIN = OPEN`.
Divisor multiplicity: `shiftRepresentationMultiplicityBound`,
`shift_pairs_subset_divisorsAntidiagonal`.

## E. PRIME COVARIANCE
Kernel: `covKernel`, `covKernel_expand` (KP), `covKernel_off` (KP-OFF; valid
for all `u, v`), `covKernel_diag` (KP-DIAG).
Second moment: `centeredForm`, `sum_normSq_centeredForm` (P2MOM),
`sum_normSq_centeredForm_norm`.
`PRIME_CENTERED_OFF_DIAGONAL_BOUND` remains open analytic.

## F. PRODUCT-MODE OBSTRUCTION
Status: provedFinite. `coordCentering`, `mixedMode`, `sum_coordCentering`,
`sum_sq_coordCentering`, `sum_mixedMode_fst`, `sum_mixedMode_snd`,
`mixedMode_l2` (ANOVA), `zero_projections_not_imply_zero_mixed_mode`.
Scope: refutes the formal implication only.

## G. DETERMINANT IDENTITY
Status: provedFinite (`det_identity`, `det_identity_fixed_shift`).
Analytic route status: `DETERMINANT_PIVOT_STRICT_REDUCTION = NOT PROVED`;
`DETERMINANT_PIVOT = REFORMULATION_ONLY` (ledger metadata, encoded as
`status DeterminantClosureRoute = reformulationOnly`).

## H. DIRECT GAUSS REASSEMBLY
Unit identity: `char_combine` (CHAR-COMB), `gaussReassembly_unit` (GAUSS-CONG),
`gauss_phys` (GAUSS-PHYS), `direct_phys` (DIRECT-PHYS), `ecz`.
Non-unit stratification: `gaussReassembly_nonunit_condition`,
`linearCongruence_solvable_iff`, `linearCongruence_solution_class`,
`card_residue_class_range`.
Status: `DIRECT_GAUSS_CHARACTER_SUM_REMOVED = PROVED FINITE ALGEBRA`;
`DIRECT_PHYSICAL_PHASE_POWER_SAVING = OPEN ANALYTIC`.

## I. R9 BLOCK REGROUPING
2|7: `expTwoSeven = 2/9`, `expTwoSeven_lt_expU`.
4|5: `regroup_prod` (REGROUP-PROD), `regroup_cong` (REGROUP-CONG),
`expU = 4/9`, `expV = 5/9`, `expU_add_expV = 1`; block masses `massOf`,
`massOf_compl`, `exists_block_split` (all splits `1|8 … 8|1`), `prod_split`;
optimality `blockImbalance_min` (BLOCK-PARITY).
Multiplicity convention: Convention A `labelled_slot_unique`,
`labelledBlockRegroupingInjective`; Convention B reuses the project's
`r9BlockConvolutionDecomposition`, plus `constant_does_not_change_exponent`.

## J. 4|5 THRESHOLD
sqrt(Q): `expQ = 13/18`, `expSqrtQ = 13/36` (`expSqrtQ_eq_half_expQ`).
Left margin: `fourFive_left_above_sqrtQ` — `4/9 − 13/36 = 1/12`.
Right margin: `fourFive_right_above_sqrtQ` — `5/9 − 13/36 = 7/36`.
2|7 deficit: `twoSeven_short_below_sqrtQ`, `twoSeven_short_deficit = 5/36`.
Pointwise sqrt(Q) deficit: `weil_deficit` — `13/36 − 5/18 = 1/12` (WEIL-DEF).

## K. ANALYTIC INTERFACES CREATED (never inhabited)
1. `SwitchedCenteredMixedCovarianceBound` (with `switchedMixedCovariance`);
2. `R9FourFiveDispersionBound` (with `fourFiveDispersion`);
3. `DirectPhysicalPhaseBound`.

## L. SOURCE INTERFACES CREATED (never inhabited)
1. `ExpectedDensitySourceInterface` — the exact `E(q)`;
2. `HighP3ExhaustiveRoutingInterface` — global high-`P₃` routing;
3. (retained from the earlier banks, untouched) the switched/direct
   dictionaries and Gate 0 coverage statements.

## M. PROVED FINITE RESULTS
1. ESEP1 / ESEP2 and the independence of the nonzero-frequency term from `E`;
2. complete and nonzero additive orthogonality; RES_EQ;
3. CRT-CENTER and the CRT frequency bijection with matching characters;
4. SHIFTINV and SHIFT_PHASE; shift representation multiplicity;
5. KP, KP-DIAG, KP-OFF and P2MOM;
6. the ANOVA product-mode obstruction;
7. the determinant identity DET;
8. CHAR-COMB, GAUSS-CONG, GAUSS-PHYS, DIRECT-PHYS and the non-unit
   stratification (solvability, solution class, exactly `g` classes);
9. the nine-block mass calculus, REGROUP-PROD / REGROUP-CONG, BLOCK-PARITY,
   Convention A injectivity and Convention B exponent invariance;
10. all completion-threshold and WEIL-DEF exponent arithmetic;
11. the five overclaim kill tests.

## N. PROVED CONDITIONAL RESULTS
1. CRT-SRC (premise DENS-MULT);
2. `centered_progression_bound_of_interfaces`,
   `fourFive_fixedCell_closure_conditional`,
   `direct_family_target_conditional`,
   `prime_second_moment_bound_of_interfaces`,
   `highP3_total_bound_conditional`, `source_weighted_bound_conditional`.

## O. OPEN ANALYTIC
1. the `4|5` q-averaged dispersion;
2. the switched centered mixed covariance;
3. the direct physical-phase bound; the prime-centered off-diagonal bound;
   Gate 1A, Gate 1B.

## P. OPEN SOURCE
1. the exact source expectation `E(q)`;
2. the `j = 3..6` exact switched routing;
3. the global high-`P₃` exhaustion; Gate 0.

## Q. REFORMULATION ONLY / RETIRED
1. the determinant pivot strict reduction (not proved);
2. the determinant closure route (reformulation only);
3. nothing is claimed for `T* ≪ X^{19/18−δ}`, SW-CENTERED-THEOREM,
   positive-measure switched closure, BC/Wright closure, Maynard 8.2 closure,
   the N1 uncentered theorem, the every-`K` resonance barrier, or a
   product-frequency large-sieve power gain.

## R. BUILD
PASSED.

## S. JOB COUNT
8224.

## T. OVERCLAIM AUDIT
PASS.  No theorem named `Gate0Closed` / `Gate1AClosed` / `Gate1BClosed` exists;
no analytic or source interface is inhabited; every implication that uses one
carries `conditional` or `of_interfaces` in its name; the status ledger proves
that no open item is marked proved.

## U. HIGHEST HONEST STATUS
FINITE BANK CONSOLIDATED.
