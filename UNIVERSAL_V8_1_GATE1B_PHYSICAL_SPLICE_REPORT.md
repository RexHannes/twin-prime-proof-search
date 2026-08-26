# UNIVERSAL v8.1 — GATE 1B PHYSICAL-SPLICE / PCL MIXED-FACE EXTENSION

Safe formalization run.  No new analytic number-theory theorem is proved, and
**Gate 1B is not declared closed**.

```text
LEAN VERSION:   leanprover/lean4:v4.28.0
MATHLIB COMMIT: 8f9d9cff6bd728b17a24e163c9402775d9e6a365 (v4.28.0, as pinned)
```

---

## A. REGRESSION AUDIT

Baseline rebuild (before any new file was added):

```text
lake build            exit code 0
jobs                  8368
errors                0
```

Rebuild after the new modules:

```text
lake build            exit code 0
jobs                  8379   (8368 + 11 new modules)
errors                0
```

Token scan over the whole repository (`rg`, all `.lean` files):

```text
sorry              0   (matches are inside documentation comments only)
admit              0   (idem)
user axiom         0   (no `axiom` declaration anywhere)
opaque             0
native_decide      0
@[implemented_by]  0   (idem)
```

Every previously banked module still builds unchanged.  The commit for this run
touches **no existing proof**: the diff consists of new files plus additional
`#print axioms` lines appended to `Gate1B/SafeExtensions/Status.lean`.  In
particular the following were re-run and are unaffected:

* `UniversalV8` — `DiscreteAbel`, `BoundedVariation`, `Synthesis`, `BlockGram`,
  `DiagonalBaseline`, `Budget`, `DefectCapacity`, `Countermodels`;
* `Universal/SafeAlgebra` — `weightedBlockSchur`, `openChain_two`,
  `closedCycle_trace_invariant`, `closedCycle_sign_telescopes`;
* `Gate1A/SafeAlgebra/BPExponentRepair`;
* `Gate1B/SafeExtensions` — `SourceWeightCollapse`, `PrimitiveConductorRouter`,
  `NearPrimitiveDiagonal`, `Budget`; `Gate1B/SafeAlgebra/NPLDiagonalReduction`.

No conflicting theorem pair was found.

**REGRESSION: PASS.**

---

## B. NEW FILES

| File | Content |
|---|---|
| `Universal/SafeAlgebra/Homogeneity.lean` | quadratic / sesquilinear homogeneity, no-free-floor countermodel |
| `Gate1B/SafeExtensions/PhysicalSecondMoment.lean` | exact outer Cauchy, `A₂`, budget implication |
| `Gate1B/SafeExtensions/MixedFaceScope.lean` | HFMV weighted face decomposition + firewall counterexample |
| `Gate1B/SafeExtensions/PCLMixedFace.lean` | Ramanujan divisor identities and the exact mixed-face → PCL reindexing |
| `Gate1B/SafeExtensions/PCLSquareMass.lean` | finite subset/Euler identity and finite square-mass bound (ℚ) |
| `Gate1B/SafeExtensions/PrimeCenteredSquareMass.lean` | prime-centered square-mass split and bounds |
| `Gate1B/SafeExtensions/LargeUnmatchedRouter.lean` | FUF large-unmatched structural router |
| `Gate1B/SafeAlgebra/AKPhysicalExponentRepair.lean` | exact ℚ exponent ledger (223/144, 224/144, 1/144, 1/288) |
| `Gate1B/SafeExtensions/AKPhysicalBudget.lean` | abstract physical-splice budget (AK estimate is a hypothesis) |
| `Gate1B/SafeExtensions/C2FloorGuard.lean` | retraction guard for the `C₂ ≫ Q log^{-O(1)}` floor |
| `Gate1B/SafeExtensions/AKGMInterfaces.lean` | **COMMENTS ONLY**, zero declarations |
| `Gate1B/SafeExtensions/Status.lean` (extended) | `#print axioms` for every new declaration |

---

## C. NEW THEOREMS

### Homogeneity (`Universal.SafeAlgebra`)

* `quadraticEnergy_smul` : `Energy(λ • c) = ‖λ‖² · Energy(c)` for a finite family
  in any normed space over a normed field.
* `sesquilinear_same_smul` : `⟪λ • x, λ • y⟫ = ‖λ‖² ⟪x, y⟫` (complex inner
  product space).
* `finiteSesquilinearForm_smul` : the same homogeneity for a finite kernel form.
* `zeroEnergy_counterexample`, `noPositiveUniformEnergyFloor`,
  `upperBound_does_not_give_lowerBound`.

### Physical outer Cauchy (`Gate1B.SafeExtensions`)

* `physicalOuterCauchy` : `‖∑_u a_u S_u‖² ≤ (∑_u ‖a_u‖²)(∑_u ‖S_u‖²)`.
* `gate1B_A2` : `A₂ = ∑_u ‖a_u‖²`; `gate1B_outerCauchy`.
* `physicalSecondMoment_imp_amplitude` : `|P|² ≤ A₂E` and `A₂E ≤ X₂δ` give
  `|P|² ≤ X₂δ`.
* `gate1B_physicalSecondMomentBudget` : the two steps chained, with the
  second-moment bound supplied as a hypothesis.

### HFMV face scope (`Gate1B.SafeExtensions`)

* `weightedCenteredFaceDecomposition` (pointwise, from the reused
  `rho_mul_coprime`).
* `rawCentered_eq_mixed_add_unaryD_add_unaryP` :
  `RawCentered = MixedFace + UnaryD + UnaryP` for arbitrary finite weights.
* `mixedFace_ne_raw_without_unary_hypotheses` (counterexample, see D).

### Exact Ramanujan / PCL (`Gate1B.SafeExtensions`)

* `ramanujanSum` (Hölder divisor form), `ramanujanSum_over_divisors` :
  `∑_{h ∣ d} c_h(N) = d · 1_{d ∣ N}`.
* `ramanujanProperDivisors_eq_centeredDivisibility` :
  `∑_{h ∣ d, h > 1} c_h(N) = d ρ_d(N)`; `rho_eq_ramanujan_average`.
* `squarefree_divisor_coprime_quotient`, `moebius_split_squarefree_divisor`.
* `pclPairs`, `mem_pclPairs`, `pclPairs_support`, `sum_pclPairs`,
  `sum_antidiagonal_filter_gt_one`.
* `pclMixedFace_exact`, `betaMixedFace_to_PCL_exact` (see E).

### Finite PCL square mass (ℚ)

* `subsetProductSquareSum_eq_eulerProduct`,
  `pclCoreSquareMass_factorization`, `pclCoreSquareMass_finiteBound`.

### Prime-centered square mass

* `primeCenteredSquareMass_split`, `primeCenteredSquareMass_le`.

### FUF large router

* `eq_one_or_prime_of_all_primeFactors_gt_sqrt`,
  `largeUnmatchedFactor_unique`, `fufLargeRouter_finite`.

### Physical splice budget

* `akPhysicalSplice_of_suppliedBound`, `akPhysicalSpliceBudget`,
  `akPhysicalSplice_closes_of_margin`.

### Rational exponent ledger (ℚ)

* `ak_UV_exponent_sum`, `ak_largeCell_spectralTax_le`,
  `ak_energyOutputExponent`, `ak_physicalTargetExponent`,
  `ak_energyMargin_exact`, `ak_amplitudeMargin_exact`, `ak_exponentLedger`.

### C₂ guard

* `zeroCoefficient_energy_zero`, `noAutomaticC2LowerMass`,
  `c2Floor_not_formal_from_upperBound`.

---

## D. COUNTERMODELS / RETRACTION GUARDS

1. **Mixed face ≠ raw source.**  With `D = {2}`, `P = {3}`, unit weights and
   `N = 1`:  `RawCentered = −1/6` while `MixedFace = +1/6`.  Hence the HFMV
   unary faces are load-bearing and may never be silently dropped
   (`mixedFace_ne_raw_without_unary_hypotheses`).

2. **No free positive energy floor.**  The zero family has zero energy, so no
   constant `c > 0` satisfies `Energy ≥ c · card` uniformly
   (`noPositiveUniformEnergyFloor`).

3. **C₂ floor retraction guard.**  For every `C ≥ 0` and `c > 0` the implication
   "`C₂ ≤ C·Q` ⟹ `C₂ ≥ c·Q`" is false
   (`c2Floor_not_formal_from_upperBound`, `noAutomaticC2LowerMass`).  The
   retracted route through a lower floor `C₂ ≫ Q log^{-O(1)}` is therefore not
   recoverable by formal means; a source-specific lower bound would have to be
   proved separately.  **This is a logical guard only** — nothing asserts that
   the actual Gate source has `C₂ = 0`.

---

## E. PCL MIXED-FACE EXACT DICTIONARY

With `ρ_d(N) = 1_{d ∣ N} − 1/d` (the banked convention),
`c_h(N) = ∑_{e ∣ h, e ∣ N} e μ(h/e)` and `H_h(N) = μ(h) c_h(N)`:

```text
∑_{d ∈ D} μ(d) ∑_{p ∈ P} L_p ρ_d(N) ρ_p(N) W(d,p)
    =  ∑_{(h,s) : hs ∈ D, h > 1}  (μ(s)/s) · (1/h) · H_h(N)
             · ∑_{p ∈ P} L_p W(hs, p) ρ_p(N)
```

* Hypothesis: every `d ∈ D` is positive and squarefree.  Weights `L`, `W` are
  arbitrary; supports `D`, `P` are arbitrary finite sets.
* Support transport is explicit: the index set is `pclPairs D`, and
  `pclPairs_support` proves `h s ∈ D`, `h > 1`, `s > 0`, `gcd(h,s) = 1`,
  `Squarefree h`, `Squarefree s`.
* Ingredients: `d ρ_d(N) = ∑_{h ∣ d, h > 1} c_h(N)` and
  `μ(hs) = μ(h) μ(s)` on squarefree `hs`.
* **SCOPE FIREWALL.**  This is the MIXED CENTERED FACE only.  It does *not*
  state that a raw `β(q)` shell equals the PCL expression; the HFMV unary faces
  are excluded and are provably non-negligible (D.1).  No smoothness or
  analytic claim is attached.

---

## F. PHYSICAL SECOND-MOMENT SPLICE

```text
|P|² = ‖∑_u a_u S_u‖² ≤ A₂ · ∑_u ‖S_u‖²          (physicalOuterCauchy)
       ∑_u ‖S_u‖² ≤ E                            (SUPPLIED)
       A₂ · E ≤ X₂ · δ                           (budget hypothesis)
   ⟹  |P|² ≤ X₂ · δ                              (gate1B_physicalSecondMomentBudget)
```

and abstractly, with the AK estimate as an input:

```text
A₂ ≤ U_mass,  B₂ ≤ V_mass,  U_mass·V_mass ≤ X_mass,
E_AK ≤ spectralFactor · U_mass · B₂             (EXTERNALLY SUPPLIED),
spectralFactor ≤ savingFactor,
savingFactor · X_mass ≤ physicalTarget
   ⟹  A₂ · E_AK ≤ U_mass · physicalTarget       (akPhysicalSpliceBudget)
   ⟹  |P|² ≤ U_mass · physicalTarget            (akPhysicalSplice_closes_of_margin)
```

No `X^{o(1)}` factor is hard-coded, no lower bound on any energy is used, and
the comparison is made directly against the supplied physical target.

---

## G. FUF LARGE STRUCTURAL ROUTER

```text
0 < n < Y²  and  (∀ prime p ∣ n, Y < p)   ⟹   n = 1  or  n prime
```

(`eq_one_or_prime_of_all_primeFactors_gt_sqrt`; squarefreeness is *not* needed,
so the statement already covers the squarefree case).  Gate wrapper: for
`hᵢ = a rᵢ` with `gcd(r₁, r₂) = 1`, `rᵢ < Y²` and all unmatched prime factors
above `Y`, each `hᵢ` equals `a` or `a` times a single prime `> Y`, and two such
primes are distinct.  **Structural only — the analytic large branch is not
closed.**

---

## H. EXACT RATIONAL EXPONENT LEDGER

```text
U exponent            = 4/9
V exponent            = 5/9
U + V                 = 1
lam ≥ 5/9, 0 ≤ theta ≤ 7/64      ⟹   theta (1 − lam) ≤ 7/144
1/2 + 4/9 + 5/9 + 7/144          =   223/144
2 − 4/9                          =   224/144
224/144 − 223/144                =   1/144
(1/144)/2                        =   1/288
```

All verified as exact ℚ arithmetic.  **These are exponent certificates only**:
`E_AK ≤ X^{223/144+o(1)}` is *not* declared as an analytic theorem.

---

## I. COMMENTS-ONLY ANALYTIC INTERFACES

`Gate1B/SafeExtensions/AKGMInterfaces.lean` contains zero declarations and
records: `GM_THEOREM_1_1`, `GM_X012_CONSTRAINT`, `GM_SELF_KERNEL_1`,
`GM_SELF_KERNEL_2`, `AK_GM_X012_INTERFACE45`, `U_TYPED_AK_SELF45_INTEGRATED`,
`POINT_SUPPORTED_FUNCTIONAL_LEGALITY`, `GM_COROLLARY_1_5`,
`AK_A2_PHYSICAL_SPLICE45`, `COND_BV5_SOURCE_FREEZE45`,
`COND_BV4_SOURCE_FREEZE45`, `QSET_BV45`, `COPRIME_VK45`, `E(q)`, `Z_E(q)`,
`KAPPA4`, `SOURCE_FACE_COMPLETENESS`, `FIXED_SWITCHED_REASSEMBLY`, the
`E_AK(L)` estimate, the retracted `C₂` floor, and `GATE1B_CLOSED: DO NOT
DECLARE`.

---

## J. AXIOM AUDIT

`#print axioms` is run in `Gate1B/SafeExtensions/Status.lean` on every new
public declaration (plus the previously banked ones).  Every report is at most

```text
[propext, Classical.choice, Quot.sound]
```

with several reporting fewer.  No user axiom, no `opaque`, no `native_decide`,
no `@[implemented_by]` anywhere in the repository.

---

## K. REMAINING OPEN ANALYTIC NODES

GM Theorem 1.1; the AK-GM-X012 interface; the typed integrated AK self-kernel;
the `X^{o(1)}` PCL square mass; the actual `X^{-1/144}` analytic estimate;
COND-BV4 / COND-BV5; Mertens / Vinogradov–Korobov; `E(q)`, `Z_E(q)`, `kappa4`;
source face completeness; fixed/switched reassembly; and **Gate 1B closure
itself**.  Full Type II and twin primes are not declared anywhere.

---

## L. BUILD RESULT

```text
lake build   exit 0     8379 jobs     0 errors
sorry 0   admit 0   user axiom 0   opaque 0   native_decide 0   @[implemented_by] 0
```
