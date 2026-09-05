# UNIVERSAL VNEXT (V12) — GATE 1B MOVING-MULTIPLIER EXACT ALGEBRA / FAMILY-LIFT COUNTERGUARD / FOUR-CYCLE DISCRIMINANT / CHARACTER-COVARIANCE INTERFACES

**APPEND-ONLY KERNEL REPROOF.  V10 and V11 are untouched.  Version used: V12
(V11 already exists).**

Everything below is kernel-checked Lean.  No `sorry`, no `admit`, no `axiom`,
no `opaque`, no `unsafe`, no `native_decide`, no `@[implemented_by]` occurs in
any new module.

---

## A. Baseline regression

```
lake build (untouched checkout)   PASS   (8563 jobs)
lake build (after V12 edits)      PASS   (0 errors)
```

No pre-existing file was modified: V12 consists exclusively of new modules.

---

## B. Exact prime character expansion

`Gate1B/SafeAlgebra/MovingMultiplierPrime.lean`

* `kloosterman_character_expand` — the exact multiplicative-character
  diagonalisation of the finite Kloosterman sum, in the repository's own
  convention (`AdditiveCharacterSystem`, `MulCharSystem`):

  ```
  ∑_χ  τ(χ)² · conj(χ(ab))  =  |(ZMod q)ˣ| · S(a,b;q)
  ```

  Conjugations are *derived* from the supplied unimodularity/orthogonality
  fields, never hard-coded.

* `movingMultiplier` — the moving-multiplier bilinear form `B_a`.

* `movingMultiplier_bilinear_expand`, `movingMultiplier_bilinear_expand'` —

  ```
  B_a = (1/|(ZMod p)ˣ|) ∑_χ τ(χ)² conj(χ(a)) α̂(χ) β̂(χ)
  ```

Status: **PROVED**.  This settles the item previously recorded as
`CONCRETE QK5 MCHAR DIAGONALIZATION: OPEN` at the abstract-system level.

---

## C. Exact moving-`a` second moment

`Gate1B/SafeAlgebra/MovingMultiplierSecondMoment.lean`

* `movingMultiplier_second_moment_all`

  ```
  ∑_{a mod p} |B_a|²  =  p² · E(α,β) − p · |∑α|² |∑β|²
  ```

* `movingMultiplier_second_moment_units`

  ```
  ∑_{a unit}  |B_a|²  =  p² · E(α,β) − (p+1) · |∑α|² |∑β|²
  ```

Both are exact identities; `E(α,β) = ProductResidueEnergy` is the literal
residue energy.  The unit form is derived by subtracting the exact value at
`a = 0` (`movingMultiplier_zero`), so the constants `p` and `p+1` are *derived*,
not postulated.  Supporting exact facts proved on the way: `gaussSum_mul_conj`
(`|τ(χ)|² = p` for non-principal `χ`), `gaussSum_principal` (`τ = −1`),
`character_dual_parseval_complex/_real`, `sum_hat_sq_eq_card_mul_energy`.

**No asymptotic estimate on `ProductResidueEnergy` is asserted.**

---

## D. Hilbert saturation counterguard (family lift)

`Gate1B/SafeAlgebra/MovingMultiplierCounterguard.lean`

* `movingFamily_l2_duality` — `IsGreatest` form of

  ```
  sup { ‖∑_Θ A(Θ) B(Θ)‖ : ∑_Θ ‖A(Θ)‖² ≤ 1 } = ‖B‖₂,
  ```

  with the saturating vector constructed explicitly as `conj B / ‖B‖₂`.

* `fixedMultiplierSaving_not_familyLift_by_l2_alone` — for **any** abstract
  scalar `c < 1` there is an admissible multiplier with pairing `> c‖B‖₂`.
  The hypothetical saving appears only as the abstract parameter `c`; no
  numerical exponent occurs in the statement.

**COUNTERGUARD B: fixed pointwise operator bounds plus ℓ² multiplier data do
not, by finite Hilbert-space algebra alone, produce a smaller moving-family
norm.**

---

## E. Additive Θ Fourier — COORDINATE TRANSFORM ONLY

`Gate1B/SafeAlgebra/KloostermanMultiplierFourier.lean`

* `kloosterman_theta_fourier_unit`

  ```
  ∑_{Θ mod c} S(tΘ,1;c) e_c(−ξΘ) = c · e_c(t ξ⁻¹)          (ξ a unit)
  ```

* `kloosterman_theta_fourier_nonunit` — the transform vanishes for non-unit `ξ`.

* `add_plancherel` — finite Plancherel: `∑_ξ |f̂(ξ)|² = c ∑_Θ |f(Θ)|²`.

* `kloosterman_theta_square_mass` — exact consequence
  `∑_Θ |S(tΘ,1;c)|² = c · |(ZMod c)ˣ|`.

* `thetaFourier_is_coordinate_change` — **formal status: coordinate transform
  only** (mass is preserved exactly, hence no contraction).  **COUNTERGUARD C.**

---

## F. CRT source Fourier factorisation (CONDITIONAL)

`Gate1B/SafeAlgebra/ThetaSourceFourierFactor.lean`

The repository does not contain the literal CRT residue pushforward for this
source, so the factorisation

```
Â(ξ) = F₁(λ₁ ξ) · conj F₂(λ₂ ξ)
```

is proved as `crt_source_fourier_factor`, a **CONDITIONAL** theorem carrying the
exact CRT hypotheses (the bijection `e : ZMod c ≃ ZMod q₁ × ZMod q₂`, the
rank-one pushforward hypothesis, and the exact phase splitting with the
scalings `λ₁, λ₂`).  `crt_source_fourier_factor_modulus` is the modulus form.
No analytic gain.

---

## G. Multiplicative source-character factor

`Gate1B/SafeAlgebra/ThetaSourceMulCharacter.lean`

* `rankOne_source_character_factor` — for a rank-one source pushforward
  `A(g) = R₁(u₁g) conj R₂(u₂g)` and a CRT unit bijection with exact unit phases,

  ```
  Â(χ) = conj(w χ) · R̂₁(χ₁) · conj R̂₂(χ₂).
  ```

* `rankOne_source_character_factor_modulus` — the unit phase disappears.

* `character_parseval_totient` — `∑_χ |R̂(χ)|² = φ(q) · residueEnergy(R)`.

No covariance is estimated.

---

## H. QK source character covariance interface

`Gate1B/SafeExtensions/QKSourceCharacterCovariance.lean`

* `QKSourceCharacterCovarianceData` — non-vacuous finite record (`q1, q2`,
  source transforms, `h`- and `k`-correlations, Gauss weights, physical
  normalisation with positivity), with an explicit inhabitant `trivialData`
  proving non-vacuity.
* `qkCovariance` — the exact finite covariance value.
* Deterministic identities only: `qkCovariance_sector_split` (routing along an
  arbitrary predicate, e.g. principal vs non-principal),
  `qkCovariance_norm_le` (triangle inequality),
  `qkCovariance_eq_of_movingMultiplier_decomposition` (decomposition hypothesis
  supplied as input).
* `QKSourceCharacterCovarianceBound` — **UNINHABITED** analytic interface, with
  the non-vacuity guard `qkSourceCharacterCovarianceBound_not_vacuous`.

---

## I. Four-cycle trace / determinant / discriminant

`Gate1B/SafeAlgebra/MovingMultiplierFourCycle.lean`, over an arbitrary
commutative ring, with `M_j = [[h_j, −a_{j−1}],[1,0]]` and
`M = M1 · M4 · M3 · M2`:

* `fourCycle_trace`

  ```
  tr(M) = a1a3 − a1h3h4 + a2a4 − a2h1h4 − a3h1h2 − a4h2h3 + h1h2h3h4
  ```

  — **exactly the candidate polynomial, in the stated order.**

* `fourCycle_det` : `det(M) = a1a2a3a4`.

* `fixedPoint_quadratic_disc` : for any 2×2 matrix,
  `(M₁₁ − M₀₀)² + 4 M₀₁M₁₀ = tr² − 4 det` — the fixed-point quadratic
  discriminant identity.

* `fourCycleDisc := tr² − 4 det`, evaluated exactly by `fourCycle_disc_eq`.

* `fourCycle_trace_depends_on_multipliers` — **COUNTERGUARD A**: the trace is
  not a function of the `h`'s alone.

---

## J. Fixed-`a` regression

* `fourCycle_trace_fixed_multiplier`:
  `tr(M)|_{a=1} = h1h2h3h4 − (h1+h3)(h2+h4) + 2`.
* `fourCycle_disc_fixed_multiplier`:
  `Disc|_{a=1} = (h1h2h3h4 − (h1+h3)(h2+h4) + 2)² − 4`.

This is the regression against the published fixed-`a` four-cycle polynomial:
**PASS**.

---

## K. Physical four-multiplier source interface

`Gate1B/SafeExtensions/ShiftMultiplierSource.lean`

* `PhysicalFourMultiplierSource` — fields `allowedTuples`, `sourceWeight`,
  `relation`, `allowed_satisfies_relation`.  **No default "all tuples"
  inhabitant is provided**, and independence of `a1,…,a4` is never asserted.
* `shiftMult4CharacterMoment` — defined through the *proved* `fourCycleDisc`.
* `ShiftMult4CharacterBound` — **UNINHABITED** analytic interface + non-vacuity
  guard.
* `cartesianEnlargement_changes_moment` — the enlargement counterguard recorded
  at the interface.

---

## L. Character-alignment counterguard

`Gate1B/SafeAlgebra/CharacterAlignmentCounterguard.lean`

* `hat_chi_eq` — the transform of the aligned vector `A = χ_d` is a spike.
* `commonCharacterAlignment_saturates_genericMoment` —
  `‖Â(d)‖² = |G| · ∑_g ‖A(g)‖²`: full natural scale, no cancellation.
* `alignedMode_carries_all_parseval_mass`.

**This is a generic countermodel only.**  Nothing claims the actual Full-Nine
source admits such an alignment (**COUNTERGUARD E**).

`Gate1B/SafeAlgebra/FourMultiplierCounterguards.lean` gives the source-independence
firewall (**COUNTERGUARD D**): with `F = a1a3 + a2a4`, the normalised moment over
the full `{0,1}⁴` cube is `8/16` while over the rank-one diagonal source it is
`2/2`; `fourCopies_ne_fourIndependentParameters` and
`rankOneRestriction_changes_moment` are kernel-checked.

---

## M. Weighted multiplicative energy — NOT FAKED

`Gate1B/SafeExtensions/WeightedMultiplicativeEnergyInterface.lean`

* `ProductResidueEnergy` is *reused* from the second-moment module, not
  redefined.
* `productResidueEnergy_nonneg`, `productResidueEnergy_eq_of_second_moment`
  (exact identity) are the only facts proved.
* `WeightedMultiplicativeEnergyInput` — **UNINHABITED** bound interface
  (+ non-vacuity guard).  The inequality
  `E ≤ p^{o(1)} ‖α‖²‖β‖²` is **NOT** asserted anywhere.

---

## N. V10 compatibility

`Gate1B/SafeExtensions/MovingMultiplierConditionalCompilers.lean`

* `qkCovarianceBound_to_shiftedQuotientParent`,
  `qkCovarianceBound_to_qk56FullCovariance`,
  `shiftMult4Bound_to_shiftedQuotientParent` — conditional compilers into the
  existing project-local v11 predicates `ShiftedQuotientParentBound` and
  `QK56FullCovarianceBound`.
* `v12_to_v10AnalyticLeaves` — the bridge into
  `TwinPrimeProject.Gate1BV11.V11AnalyticLeafBundle`, whose four fields are
  exactly the four V10 analytic leaves of `Gate1BClosureInputs`.
  **V10 ANALYTIC LEAF BRIDGE: PROVED (type-correct, no mismatch).**
  V10 is not altered and no fake leaf is created: the bridge consumes the
  uninhabited covariance interfaces.
* Guards `v12LeafBundle_not_automatic`, `shiftedQuotientParent_not_automatic`
  (**COUNTERGUARD F**: a conditional compiler is not a closure).

`Gate1B/SafeExtensions/MovingMultiplierLedgerStatus.lean` records, as **data
only** (booleans in a record, never propositions), the reconciliation status of
`JQ7-QCOMMONSEQ45`, `JQ7-QCHAR7-ALLCONDUCTOR45`, `QK5-XMOD-ALLQ-PROPER45`,
`SAMEQ`; all four questions are `false` at V12.

---

## O. Axiom audit

`Gate1B/SafeExtensions/VNextMovingMultiplierStatus.lean` prints the axioms of
every principal V12 declaration (44 checks).  Every one reports exactly

```
[propext, Classical.choice, Quot.sound]
```

```
SORRY:        NONE
USER AXIOMS:  NONE
UNSAFE:       NONE
```

---

## P. Gate 1B research status

Unchanged and **OPEN**.  V12 adds exact algebra, counterguards and interfaces
only.  Nothing here supplies:

* a moving-multiplier power saving;
* a `p^{o(1)}` weighted multiplicative-energy bound;
* QK56 analytic closure;
* SHIFT-MULT4 analytic closure;
* Gate 1B closure, Ford–Maynard, or twin primes.

---

## FINAL VERDICT

```
ARISTOTLE_VNEXT_GATE1B_MOVING_MULTIPLIER_EXACT_BANK_PARTIAL

REGRESSION:                      PASS
BUILD:                           PASS
SORRY:                           NONE
USER AXIOMS:                     NONE

PRIME CHARACTER EXPANSION:       PROVED (exact, repository convention)
MOVING-a SECOND MOMENT:          PROVED EXACT
                                 all a : p²E − p|∑α|²|∑β|²
                                 unit a: p²E − (p+1)|∑α|²|∑β|²
L2 FAMILY-LIFT COUNTERGUARD:     PROVED (IsGreatest, saturation attained)
THETA ADDITIVE FOURIER:          PROVED EXACT — COORDINATE TRANSFORM ONLY
QK SOURCE CHARACTER FACTORISATION: PROVED CONDITIONAL (exact CRT hypotheses)
FOUR-CYCLE TRACE:                PROVED
FOUR-CYCLE DETERMINANT:          PROVED
FOUR-CYCLE DISCRIMINANT:         PROVED (incl. fixed-point quadratic identity)
FIXED-a SPECIALISATION:          PROVED (regression PASS)

WEIGHTED MULTIPLICATIVE ENERGY:  UNINHABITED
QK ANALYTIC COVARIANCE:          UNINHABITED
SHIFT MULT4 ANALYTIC MOMENT:     UNINHABITED
V10 ANALYTIC LEAF BRIDGE:        PROVED (no type mismatch)

GATE1B:                          OPEN

FIRST FORMAL BLOCKER:
    Gate1B.SafeExtensions.QKSourceCharacterCovarianceBound
    (uninhabited; the exact missing object is an inhabitant of this type)

FIRST RESEARCH ANALYTIC BLOCKER:
    the weighted multiplicative-energy input
    WeightedMultiplicativeEnergyInput — i.e. any proved bound on
    ProductResidueEnergy.  No such bound is claimed here.
```
