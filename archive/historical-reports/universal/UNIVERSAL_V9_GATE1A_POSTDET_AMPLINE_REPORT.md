# UNIVERSAL / NANC — GATE 1A v9
## POSTDET / AMPLINE / SIGNED-PARENT SAFE FORMAL EXTENSION

**Verdict: `ARISTOTLE_GATE1A_V9_POSTDET_AMPLINE_BANK_COMPLETE`**

This is a *safe banking run*. Everything banked below is finite algebra,
finite combinatorics, or exact budget arithmetic. No analytic statement was
converted into a theorem, an axiom, an `opaque` declaration, a class field,
or an instance.

---

## A. Regression

Baseline, recorded *before* any edit:

```
git parent commit : 0fc59b1   ("Initial commit")
lake build        : exit 0
jobs              : 8367 → 8379
errors            : 0
```

Trust-token search of the pre-existing tree found no code-level
`sorry` / `admit` / `axiom` / `opaque` / `unsafe` / `native_decide` /
`implemented_by`; the only matches were prose occurrences inside
documentation comments of the existing status/interface files
(`RequestProject/Banking.lean`, `Gate1A/Status.lean`, `Gate1B/Status.lean`,
`UniversalV8/Status.lean` — one prose match each).

Final, after all v9 (and v8.2) work:

```
lake build        : exit 0
jobs              : 8406
errors            : 0
```

## B. Repository / versions

```
Lean toolchain    : leanprover/lean4:v4.28.0
Mathlib commit    : 8f9d9cff6bd728b17a24e163c9402775d9e6a365
Libraries         : RequestProject, Gate04Root, Gate1A, Gate1B, UniversalV8, Universal
                    (all glob-based, so new files are picked up automatically)
New Gate1A v9 dir : RequestProject/NANC/Gate1A/SafeExtensions/
Namespace         : TwinPrimeProject.NANC.Gate1A.V9
```

## C. Existing bank preserved

`git diff --stat 0fc59b1 HEAD` reports

```
27 files changed, 2077 insertions(+), 0 deletions(-)
```

i.e. **every file in the diff is new**. No pre-existing theorem was
modified, restated, renamed or weakened; no existing file was edited at
all — not even to add imports, since the library globs pick up the new
modules.

Reusable material from earlier banks that v9 *depends on* rather than
duplicates:

* `Gate1B.SafeExtensions.physicalOuterCauchy` — reused inside
  `PMLSNormalization.lean` for the outer-`p` Cauchy step (cross-library
  import, exactly as the existing `Gate04Root` imports do).

Absolute mathematical status recorded unchanged:

```
GATE1A DIRECT CLEAN-P3 : OPEN
XQ-AMPLINE-SIGNED1A    : OPEN, NO INHABITANT
FULL TYPE II           : NOT DECLARED
TWIN PRIMES            : NOT DECLARED
```

## D. Complementary divisor (`ComplementaryDivisor.lean`)

Structure `ComplementaryDivisorData` carries signed integers
`ell1 ell2 q1 q2 delta p m s : ℤ` together with `hdelta : delta ≠ 0`,
`hp : p ≠ 0` and

```
relation : ell1*q1 - ell2*q2 = delta*p*(m+s).
```

Banked:

| theorem | content |
|---|---|
| `complementary_deltaP_dvd` | `delta*p ∣ ell1*q1 - ell2*q2` |
| `deltaP_ne_zero` | `delta*p ≠ 0` |
| `complementary_m_eq` | `delta*p*(m+s) = ell1*q1 - ell2*q2`, solved for `m` |
| `complementary_m_ediv` | `m = (ell1*q1 - ell2*q2) / (delta*p) - s` (exact quotient; the division is justified by the divisibility witness, not by `Int.ediv` simplification) |
| `complementary_m_unique` | two `m` satisfying the same frozen data are equal |

**Firewall.** This is a *fibre* theorem: moving `m` has one root over the
frozen data. It is not an analytic saving of any kind.

## E. Double determinant (`DoubleDeterminant.lean`)

With

```
detN     h1 h2 q1 q2       = h1*q2 - h2*q1
detDelta ell1 ell2 h1 h2   = ell1*h1 - ell2*h2
detC     ell1 ell2 q1 q2   = ell1*q1 - ell2*q2
```

the two exact identities are

```
doubleDet_left  :  h1*C + ell2*N = q1*Delta
doubleDet_right :  h2*C + ell1*N = q2*Delta
```

both proved by `ring` after unfolding. From them, with `Delta ≠ 0`, the
cross-multiplied uniqueness statements `doubleDet_q1_unique`,
`doubleDet_q2_unique` and the packaged
`doubleDet_conductorPair_unique` follow: once every other integer datum is
frozen and `Delta ≠ 0`, the pair `(q1,q2)` is determined. No rationals are
used.

## F. N–Delta pushforward (`NDeltaPushforward.lean`)

```
detMap q1 q2 ell1 ell2 (h1,h2) = (h1*q2 - h2*q1, ell1*h1 - ell2*h2)
```

* `detMap_injective_of_crossDet_ne_zero` : if `q1*ell1 - q2*ell2 ≠ 0` then
  `detMap` is injective on `ℤ × ℤ`.
* `injectivePushforward_l2` : for a finite support `S`, weights
  `w : ι → ℂ` and an injective `f`, the pushed-forward ℓ²-mass over the
  image equals `∑_{s∈S} |w s|²`.
* `nDelta_pushforward_l2` : the specialisation to `detMap`.

**Firewall.** No analytic `H`-bound is inserted; if such a bound is ever
wanted it must appear as an explicit theorem hypothesis. This is the exact
finite-safe replacement for the informal
`∑_{N,Δ}|Ξ(N,Δ)|² ≤ (∑|ω₁|²)(∑|ω₂|²)` step.

## G. Reduced Plücker system (`ReducedPlucker.lean`)

Inputs are `C, N, Delta : ℤ`, a positive `g` with explicit quotient
witnesses `C = g*c`, `Delta = g*d`, and an explicit coprimality hypothesis
`IsCoprime g ell2`.

| theorem | content |
|---|---|
| `reducedPlucker_g_dvd_N` | `g ∣ N` |
| `reducedPlucker_left` | `q1*d = h1*c + ell2*n` |
| `reducedPlucker_right` | `q2*d = h2*c + ell1*n` |
| `reducedPlucker_coprime_cd` | `IsCoprime c d` |
| `reducedPlucker_coprime_cn` | `IsCoprime c n` under the stated prime/coprimality hypotheses on `q1,q2` |

All hypotheses are explicit; no "clean sector" tactic hides a condition.
Quotient witnesses are used throughout in preference to `Int.ediv`.

## H. Reduced conductor (`ReducedConductor.lean`)

* `reducedConductor_dvd` : from `C = delta*p*(m+s)` and `C = g*c`,
  `c ∣ delta*p*(m+s)`.
* `reducedConductor_cSharp_dvd` : with an **explicit** hypothesis
  `IsCoprime cSharp delta`, the reduced conductor divides `p*(m+s)` —
  the algebraic content of "the effective conductor comes only from
  `p*(m+s)`".
* `constantReducedConductor_impossible` : the clean size contradiction.
  Hypotheses: `c.natAbs ≠ 1`, `c ∣ 2*k*delta`, `|2*k*delta| < P0`,
  `c ∣ p*(m+s)`, and every prime divisor of `p*(m+s)` is `≥ P0`. Conclusion
  `False`. The proof extracts a prime divisor of `c` with
  `Int.exists_prime_and_dvd` and contradicts the size bound. No `X^o` is
  encoded anywhere.

*Deviation, deliberately recorded.* The prompt's variant with
`u := gcd(|c|, |2*k*delta*n|)` and `cSharp := |c|/u` was dropped in favour
of the divisor-hypothesis form above, because in the `u`-form the
hypothesis on `n` is never load-bearing; keeping it would have produced a
statement with a decorative hypothesis. An in-file comment records this.

**Firewall.** No analytic cancellation is claimed from the conductor
statement.

## I. Post-Cauchy determinant (`PostDeterminant.lean`)

```
postDelta   ell1 ell2 h1 h2 = ell1*h1 - ell2*h2
postDetOmega delta delta' ell1 ell2 ell1' ell2' h1 h1' h2
  = delta' * (ell1*ell2) * postDelta ell1' ell2' h1' h2
  - delta  * (ell1'*ell2') * postDelta ell1 ell2 h1 h2
```

`postDetOmega_factorization` proves the fully expanded BC-style form

```
Omega = delta'*ell1*ell2*ell1'*h1' - delta'*ell1*ell2*ell2'*h2
      - delta*ell1'*ell2'*ell1*h1 + delta*ell1'*ell2'*ell2*h2.
```

Finite algebra only.

## J. Generic postdet zero (`postDet_zero_generic_longDiagonal`)

Conclusion:

```
ell1 = ell1'  ∧  ell2 = ell2'  ∧  delta = delta'  ∧  h1 = h1'.
```

Hypotheses (all explicit, none hidden):

```
Prime ell1, ell2, ell1', ell2';  all positive
ell1 ≠ ell2,  ell1' ≠ ell2'
hnoswap : ell1 ≠ ell2'
h1 ≠ 0,  |h1| < ell2
h2 ≠ 0,  |h2| < ell1,  |h2| < ell1'
delta ≠ 0,  |delta| < ell1,  |delta| < ell2
delta' ≠ 0, |delta'| < ell1'
hsep : |delta| + |delta'| < ell1
Omega = 0
```

**Three hypotheses beyond the prompt's list were needed, and are stated
explicitly rather than assumed away.**

1. `hnoswap : ell1 ≠ ell2'`. Without it the conclusion is *false*: the
   swapped branch `ell1 = ell2', ell2 = ell1'` genuinely admits solutions
   of `Omega = 0`, so the intermediate lemma
   `postDet_zero_amplifier_match` correctly returns a disjunction
   (`ell1 = ell1'` **or** `ell1 = ell2'`) and only the no-swap hypothesis
   selects the long-diagonal branch.
2. `hh1lt : |h1| < ell2`, needed for the reduction modulo `ell2` that
   yields `ell2 = ell2'`.
3. `hsep : |delta| + |delta'| < ell1`, used in place of the prompt's
   "each `< min ell_i`", which is not by itself strong enough to force
   `delta = delta'`.

Non-vacuity was checked on an explicit point: `ell1 = 5`, `ell2 = 3`,
matched primed data, `delta = delta' = h1 = h1' = h2 = 1`.

**Firewall.** Closing the `Omega = 0` branch is *not* control of the
nonzero post-determinant.

## K. Delta-LCM finite router (`DeltaLCMRouter.lean`)

```
HardDeltaPairs J = { (d,d') : 1 ≤ d ∧ 1 ≤ d' ∧ Nat.lcm d d' ≤ J }
```

with `mem_hardDeltaPairs` the membership characterisation and

```
hardDeltaPairs_card_le_divisorSquareSum :
  (HardDeltaPairs J).card ≤ ∑ r ∈ Finset.Icc 1 J, (Nat.divisors r).card ^ 2
```

proved by mapping each pair to `r = lcm(d,d')` and using `d ∣ r`, `d' ∣ r`.
No asymptotic divisor theorem, and in particular **no `J·X^o`** is encoded.

## L. Maximal amplifier budget (`AmplifierBudget.lean`)

For real parameters `H, L, M, Z`:

```
ampLen M Z            = M^2 * Z
amplifierPrefactor L M Z = L*M / (ampLen M Z)^2      (noncomputable)
dTarget H L M Z       = H*L^2*M^3*Z^2
dDiag   H L M Z       = H*L^2*M^3*Z
```

Banked exact identities:

* `amplifierPrefactor_eq` : `amplifierPrefactor = L / (M^3 * Z^2)`;
* `amplifier_budget_general` : `amplifierPrefactor * dTarget = H*L^3`;
* `amplifier_diag_ratio` : `dDiag / dTarget = 1/Z`;
* `amplifier_budget_maximal` (`Z = L/M`) :
  `AmpLen = L*M`, `prefactor = 1/(L*M)`, `DTarget = H*M*L^4`,
  `DDiag = H*M^2*L^3`;
* `amplifier_spare_pays_familyTax_identity` : `(M/L)*(L/M) = 1`.

**Firewall.** A budget identity is *not* an amplifier-family cancellation.

## M. Amplifier affine line (`AmplifierLine.lean`)

```
complementarySolutions_parametrized :
  IsCoprime q1 q2 → q2 ≠ 0 → q1*ell10 - q2*ell20 = C →
  ( q1*ell1 - q2*ell2 = C
      ↔ ∃! t : ℤ, ell1 = ell10 + q2*t ∧ ell2 = ell20 + q1*t )
```

Proof by Bézout/divisibility from `q1(ell1-ell10) = q2(ell2-ell20)` and
`gcd(q1,q2)=1`. Only coprimality is required (plus `q2 ≠ 0` for
*uniqueness* of `t`); no primality.

Also `amplifierLine` (the parametrised pair) and `amplifierLine_solves`.

## N. Delta along the line, Omega along two lines, fibre degree

`AmplifierLine.lean`:

```
deltaAlongLine_affine  : Delta(t)  = Delta0  + N*t,   Delta0 = ell10*h1 - ell20*h2
deltaAlongLine_affine' : primed analogue
```

`AmplifierLinePostDet.lean`:

* `ampProduct`, `ampProduct_quadratic` : `P(t) = ell1(t)*ell2(t)` is an
  explicit degree-≤2 integer polynomial in `t`; likewise `P'(t')`.
* `omegaLine (t,t') = delta' * P(t) * (Delta0' + N'*t') − delta * P'(t') * (Delta0 + N*t)`.
* `postDet_on_amplifierLines` : `omegaLine` agrees with the abstract
  `postDetOmega` after substituting the two affine lines.
* `omegaLinePoly` (noncomputable) with `omegaLinePoly_eval`, and
  `omegaLine_coeff_two` : the `t'^2` coefficient is
  `-delta * q1 * q2 * Delta(t)` in the sign convention obtained by
  expansion.
* `omegaLine_natDegree_le_two` (via `compute_degree`).
* `omegaLine_nonzero` : under `delta ≠ 0`, `q1 ≠ 0`, `q2 ≠ 0`,
  `Delta(t) ≠ 0` the polynomial is nonzero.
* `omegaLine_zeroFiber_card_le_two` : for **any** finite set of `t'`
  (no interval required),
  `#{ t' : omegaLine(t,t') = 0 } ≤ 2`, via Mathlib's polynomial
  root-cardinality machinery.

**Firewall.** Degree-2 zero-fibre sparsity is *not* an operator-norm
contraction; no analytic gain follows.

## O. Analytic interfaces (`AnalyticInterfaces.lean`)

This file contains **zero declarations**. The interfaces

```
XQAmplLineSigned1A
XQPostDetAmpAvg1A
XQBC49SourceTranscription1A
XQAmplLineLowDefectRigidity1A
XQProperAbsoluteNormSplice1A
Gate1ADirectCleanP3Closed
```

are documented in comments only, together with their intended targets

```
per hard (delta,delta') pair :  D_{delta,delta'}^{NZ}  ≤  H*M^2*L^3 * X^o
globally                     :                          ≤  H*M*L^4  * X^o
```

*Recorded deviation.* The prompt suggested "a named `Prop` with no
inhabitant". The repository convention in the earlier banks is
comments-only interface files with zero declarations, which is strictly
safer (a named `Prop` can be picked up by automation or accidentally
instantiated), so that convention was followed and the deviation is
documented in-file. Since `X^o` is not part of the finite bank, the
target is described as an epsilon-parameterised interface in prose, not
as a declaration.

`Gate1ADirectCleanP3Closed` has **no inhabitant**, and no declaration at
all.

## P. Firewalls (overclaim guards)

Recorded in-file (`FamilyIndexGuard.lean`, `SignedParentGuard.lean`,
`Status.lean`) and here:

1. one-root fibre ≠ analytic saving;
2. degree-2 `Omega` zero fibre ≠ operator-norm contraction;
3. postdet zero branch closed ≠ nonzero postdet controlled;
4. amplifier budget identity ≠ amplifier-family cancellation;
5. finite DFT child ≠ `XQ-AMPLINE-SIGNED1A`;
6. Bettin–Chandee phase/proof architecture ≠ Gate source transcription;
7. Wright fixed-factor theorem ≠ arbitrary joint-source theorem;
8. no exact-`Q` / exact-`delta` pigeonhole without explicit cost;
9. no HFIRST gain — identified as an anti-loop in the later Gate1A audit;
10. clean-P3 Gate1A ≠ global Full Type II.

Machine-checked counterguards:

* `familyIndex_counterexample` / `familyIndex_selection_not_lossless` :
  a coherent sum over `N` family indices can have squared norm `N^2` even
  though each slice has norm 1, so fixing one exact family index is not
  lossless.
* `signedParent_child_not_parent` : explicit finite complex `σ_i, K_i`
  with `∑ |σ_i|²|K_i|²` positive while `|∑ σ_i K_i| = 0`; a child kernel
  estimate does not promote to the signed parent.

Optional child (`ReciprocalProductDFT.lean`, status
`OPTIONAL_FINITE_CHILD`): `reciprocalProductKernel` on units mod `c` and
`reciprocalProductKernel_hilbertSchmidt`, a Hilbert–Schmidt/full-space
energy identity only. No interval residue aggregation, no analytic
interval theorem. This module is explicitly *not* `XQ-AMPLINE-SIGNED1A`.

## Q. Axiom audit

`RequestProject/NANC/Gate1A/SafeExtensions/Status.lean` runs
`#print axioms` on 36 public declarations, including all of the ones the
prompt names:

```
complementary_m_unique
doubleDet_left, doubleDet_right
detMap_injective_of_crossDet_ne_zero
nDelta_pushforward_l2
reducedPlucker_g_dvd_N, reducedPlucker_coprime_cd, reducedPlucker_coprime_cn
postDetOmega_factorization
postDet_zero_generic_longDiagonal
hardDeltaPairs_card_le_divisorSquareSum
amplifier_budget_maximal
complementarySolutions_parametrized
deltaAlongLine_affine
postDet_on_amplifierLines
omegaLine_zeroFiber_card_le_two
```

Result: every one depends only on `propext`, `Classical.choice`,
`Quot.sound` (several depend on strictly fewer, and one on none).
**No user axiom anywhere.**

## R. Trust-token audit

Search over all 27 new files for
`sorry`, `admit`, `axiom`, `opaque`, `unsafe`, `native_decide`,
`implemented_by`:

```
code-level occurrences : 0
```

The only matches are prose inside doc comments (`P44PartitionLedger.lean`
"no `native_decide`", `QK5CharacterInterfaces.lean` and
`AnalyticInterfaces.lean` "an `opaque` definition", `FinsetANOVA.lean`
"No `native_decide`"), i.e. firewall text, not code.

Repository-wide `sorry` matches are all pre-existing prose in
Status/Interfaces files and were not touched.

## S. Final status

```
PMLS_NORMALIZATION            : proved (outerP_cauchy, pmls_to_normalizedGateBudget,
                                        gpmls_to_physicalGateBudget)
GENERAL_COMPLEMENTARY_DIVISOR : proved
M_FIBRE_ONE_ROOT              : proved (complementary_m_unique)
DOUBLE_DETERMINANT            : proved
N_DELTA_PUSHFORWARD           : proved
REDUCED_PLUCKER               : proved
REDUCED_CONDUCTOR             : proved
FIRST_DELTA_ZERO              : routed (constantReducedConductor_impossible)
HFIRST                        : failedRoute (anti-loop; nothing banked)
POSTDET_OMEGA                 : proved
GENERIC_POSTDET_ZERO          : proved under explicit hypotheses (3 extra, §J)
DELTA_LCM_FINITE_ROUTER       : proved
MAXIMAL_AMPLIFIER_BUDGET      : proved as exact budget arithmetic
AMPLIFIER_LINE                : proved
DELTA_ALONG_LINE              : proved
AMPLINE_OMEGA_FIBRE2          : proved
OPTIONAL_RECIPROCAL_DFT       : proved as Hilbert–Schmidt child only
XQ_AMPLINE_SIGNED1A           : analyticInterfaceOpen / NO INHABITANT
GATE1A_DIRECT_CLEAN_P3        : OPEN
FULL_TYPE_II                  : NOT DECLARED
TWIN_PRIMES                   : NOT DECLARED
```

**First open analytic theorem:** `XQ-AMPLINE-SIGNED1A`.

**Next mathematical action:** bound the nonzero post-determinant sector
`D_{delta,delta'}^{NZ}` by `H·M²·L³·X^o` for each hard `(delta,delta')`
pair emitted by the finite LCM router.
