# UNIVERSAL V11 · GATE 1B — FORD/PERRON GENERATED GRAMMAR / S2 GENERATED-TWIST INTERFACE / PAIR-MODULUS SOURCE MULTIPLIER / V10 LEAF COMPILER

**Append-only safe reproof / repair bank.**  No V10 (or earlier) file was
modified, deleted or re-proved.  All v11 work lives in eighteen new modules
under `RequestProject/NANC/Gate1B/`.

---

## A. V10 regression

`lake build` was run on the untouched checkout **before any edit**:

```
Build completed successfully (8545 jobs).
```

**REGRESSION: PASS.**  The diff against the pre-run commit consists of new
files only (eighteen Lean modules, this report, and one appended `LEDGER.md`
block).  No V10 module — `V10CanonicalZeroMode`, `V10HistoricalResidual`,
`V10PacketReassembly`, `V10Counterguards`, `V10FullTypeIICompiler`,
`V10Status` — was touched.  `ARISTOTLE_SUMMARY.md` was not edited.

**Existing bank actually discovered and reused** (searched by name and by
statement shape before creating anything):

| looked for | found | reused as |
| --- | --- | --- |
| `Gate1BClosureInputs`, `Gate1BClosed`, `FullTypeIIBound`, packet reassembly | present (`TwinPrimeProject.Gate1BV10`, `TwinPrimeProject.Gate1BDet2`) | leaf field types + `gate1B_closed_of_exact_inputs` applied, never duplicated |
| `FiniteKloosterman` | present (`Gate1B.SafeAlgebra.AdditiveCharacterSystem`, `kloosterman`, `kloosterman_scale`) | pair-modulus kernel |
| `D12ResidueFactor` | present (`d12Pushforward_l1_factor`, `d12Pushforward_l2_factor`) | rank-one source multiplier ℓ¹/ℓ² factorisation |
| `FiniteMultiplicativeCharacters`, `SameQCharacterGram`, `ProductEnergyFiniteFiber`, `BulkSpikeInterpolation` | present | inspected; not needed by the v11 statements, so not re-wrapped |
| finite Abel / summation by parts | present (`UniversalV8.DiscreteAbel`, `Universal.SafeAlgebra.FiniteAbel`) | `defectTransform_backendDualNorm` |
| `Pminus` / `Pplus` / least- or greatest-prime-factor | **ABSENT** | abstract atom type + uninhabited realisation interface |
| `ShiftedQuotientParentBound`, `QK56FullCovarianceBound` | **ABSENT** | defined as new, clearly labelled project-local v11 predicates |
| `FullFMTypeII_OneSixth`, Ford one-sixth theorem | **ABSENT** (already recorded in V10) | not created, not targeted |

---

## B. Ford/Perron generated grammar

`RequestProject/NANC/Gate1B/V11FMPerronGrammar.lean`

* `AtomTag` — the ten semantic tags (`mobius`, `constant`, `boxCutoff`,
  `smoothWeight`, `mellinTwist`, `leastPrimeTwist`, `greatestPrimeTwist`,
  `perfectPowerPullback`, `boundedConvolution`, `finiteLinearCombination`).
* `GenAtom` — the **realisable** atoms.  Every constructor carries only explicit
  numerical parameters; **no atom carries an arbitrary function**.  In
  particular `smoothWeight a b` is the normalised linear window `rampR a b`, not
  an arbitrary weight.
* `semAtom : GenAtom → ℕ → ℂ` — the explicit semantics.  The Mellin twist is
  literally `n ↦ (n : ℂ)^{I t}`.
* `GenAtom.Admissible` and `norm_semAtom_le_one` — every admissible atom is
  1-bounded (proved; the Möbius, window, Mellin and perfect-power cases are all
  discharged).
* `PrimeExtremaAtom` — the **abstract** `P±` atoms, data only.
* `PrimeExtremaRealisation` — the semantic realisation interface for `P⁻`/`P⁺`.
  **No inhabitant is supplied**, because the repository has no least/greatest
  prime-factor function.  `semPrimeExtremaAtom` is relative to a supplied
  realisation, and `norm_semPrimeExtremaAtom_le_one` is proved conditionally on
  one.

---

## C. Generated expression cost

`V11GeneratedExpression.lean`

* `GenExpr` — `atom`, pointwise `mul`, `add`, `smul`, finite Dirichlet `conv`;
  `semExpr`, `GenExpr.Admissible`, `dconv`.
* `cost D` — the deterministic cost, where `D` is a supplied uniform divisor
  bound; convolution is the only constructor that pays a divisor factor.
* Proved: `cost_nonneg`, `norm_product_le`, `norm_finiteSum_le_l1Cost`,
  `convolution_divisorBound`, and the window theorem
  **`norm_semExpr_le_cost`**: on `[0,N]`, with `τ(n) ≤ D` for `n ≤ N`, every
  admissible generated expression satisfies `‖semExpr e n‖ ≤ cost D e`.  All
  hypotheses are explicit and satisfiable.
* `PerronTemplate` — a finite template (`parameterSpace` = the finite index
  type, `coefficientDensity`, `generatedIntegrand`, `l1Cost` with its defining
  inequality).  **No improper integral is defined**, since the repository has no
  infrastructure that would make an honest one available.
* `finite_template_reassembly` and `finite_template_reassembly_of_cost`.

---

## D. Project-local FM-SieveGen predicate

`V11FMSieveGenTypeII.lean`

`FMSieveGenData N` carries: nonempty `E : Finset (Fin N)`, factor ranges
`lo, hi`, physical product range, selected-product Type-II interval, the actual
`w` sequence, and the target/log-budget parameter.  `sieveGenValue` is the
equation-(7.23)-style sum

```
∑_{n ∈ box}  physIndicator · typeIIIndicator · w(∏_j n_j) · ∏_j x_j(n_j).
```

`FMSieveGenTypeIIAtScale d : Prop` — the bound for **arbitrary** 1-bounded
`x_j`.  This is a **new v11 predicate**.  It is not named after, and is not
claimed to be, any published statement.

---

## E. Project-local FM-Perron-generated predicate

`FMPerronGeneratedTypeIIAtScale d : Prop` — the same bound, quantified only
over factor functions carrying an `FMPerronGeneratedUnit` certificate
(generated **and** 1-bounded; 1-boundedness is not automatic for a general
generated expression, so it is carried explicitly).

Non-vacuity is proved: for the explicit `toyData` configuration the value is
`1` and the target is `0`, so both predicates are **false** there
(`fmPerronGeneratedTypeII_toy_fails`, `fmSieveGenTypeII_toy_fails`).

---

## F. Proven logical implication between them

`fmPerronGeneratedTypeII_of_sieveGen : FMSieveGenTypeIIAtScale d →
FMPerronGeneratedTypeIIAtScale d`.  **PROVED.**

The converse is **NOT CLAIMED** anywhere.

---

## G. Ford-paper provenance vs. Lean status

`V11FMProvenance.lean` contains **no declarations** — metadata only.

* **RC1** ("FM-SIEVEGEN-TYPEII is sufficient for the equation-(7.23) step") —
  recorded as a research claim; unformalised (the (7.23) step itself is not
  formalised in this repository).
* **RC2** ("the actual Prop-7.22 proof may be re-run without arbitraryising its
  generated factors") — recorded; **deliberately not encoded as a theorem**.

`FMPerronGrammarCertificate` (for a *supplied* finite family of coefficients)
is defined and usable.  `RealFordGrammarCertificate` — the object that would
carry RC2 — is defined and **left without an inhabitant**: it demands both a
formal representation of the literal proof's coefficients and a
`PrimeExtremaRealisation`.

**REAL FORD GRAMMAR CERTIFICATE: UNINHABITED / REPO DATA ABSENT.**

---

## H. S2 generated-twist interfaces

`V11S2GeneratedTwist.lean`

* `defectTransform s δ w = ∑_{n ∈ s} δ(n) · w(n)`; linearity in both slots and
  the trivial ℓ¹ bound proved.
* `defectTransform_backendDualNorm` — finite summation by parts, obtained by
  **reusing** the banked finite Abel identity; nothing re-proved.
* `S2PureMellinCancellation` — uninhabited interface.
* `S2PrimeExtremaTwistCancellation` — a **separate** uninhabited interface,
  relative to a `PrimeExtremaRealisation`.
* `S2PerronGeneratedCancellation` — the full interface (pure-Mellin field,
  prime-extrema field supplied separately, and cancellation against *every*
  admissible generated weight of cost ≤ 1).  Uninhabited.

The second is never inferred from the first: the only available projections are
the literal field accessors, and the transform-level separation theorem
`pureMellin_transform_does_not_control_extremaTransform` exhibits a finite
defect whose transform against one unimodular family vanishes while the
transform against another has full mass.

No Siegel–Walfisz is assumed, named as an axiom, or otherwise smuggled in.

---

## I. `P⁻`/`P⁺` firewall

`V11PrimeExtremaTwistFirewall.lean`

1. **Coordinate firewall** — `mellinControl_does_not_imply_primeExtremaControl`:
   there is no universal implication from total cancellation against a
   unimodular Mellin coordinate to any bound against a unimodular extrema
   coordinate.  Explicit separating model on `Fin k × Fin 2`
   (`separatingModel_mellinValue_zero` = 0, `separatingModel_extremaValue` = 2k).
2. **Semantic firewall** — relative to **any** supplied realisation:
   `Pminus_four = Pplus_four = Pminus_eight = Pplus_eight = 2` (forced by the
   interface fields), hence the `P±` twist is constant on `{4,8}`
   (`extremaTwist_constant_on_prime_fibre`), while
   `mellinTwist_separates_four_eight` shows the Mellin twist at
   `t = π / log 2` satisfies `8^{it} = −4^{it}`.  Consequently
   `primeExtremaTwist_is_not_a_mellinTwist`: the `P±` weight is a scalar
   multiple of that Mellin weight only for the zero scalar.

---

## J. Pair-modulus source data

`V11PairModSourceMultiplier.lean`

`PairModSourceData c Θ U V` carries the supplied additive character system mod
`c` (reused), `A : Θ → ℂ`, the residues of `Θ`, `u`, `v`, and `α, β`.  Defined:
`kernel` (the Kloosterman sum `S(Θu, v; c)`), `fixedMultiplierValue` and

```
pairModFamilyValue = ∑_Θ A(Θ) ∑_{u,v} α(Θ,u) β(Θ,v) S(Θu, v; c).
```

**No estimate is assumed.**  Only the trivial ℓ¹ bound and the banked
unit-reindexing invariance are recorded.

---

## K. Moving-multiplier counterguard

`V11MultiplierCounterguards.lean`

`fixedMultiplierBounds_do_not_control_movingFamily` — **PROVED**.  The aligned
family on `K` multipliers has

* every fixed-multiplier pairing of modulus `1` (`alignedFamily_fixed_bound`),
* ℓ² multiplier energy exactly `1` (`alignedFamily_l2_energy`),
* family value of modulus `√K` (`alignedFamily_value_norm`).

Additionally `l2Energy_does_not_determine_familyValue`: the anti-aligned family
has the *same* pairings and the *same* multiplier moduli, so the family value is
not a function of the fixed data plus the ℓ² energy.  Family coherence is
load-bearing.

---

## L. Source rank-one multiplier algebra

`V11SourceMultiplierStructure.lean`

`SourceRankOne Θ Γ₁ Γ₂ A` abstracts `A(Θ) = R₁(u₁(Θ)) · conj R₂(u₂(Θ))` along a
supplied bijective pushforward.  `SourceRankOne.l1_factor` and
`SourceRankOne.l2_factor` are exact identities, obtained by **reusing** the
banked D₁₂ pushforward lemmas.

`rankOne_does_not_give_movingFamily_saving` — the aligned family *is* rank-one
and still loses the full `√K`.  **No analytic moving-multiplier saving is
inferred from rank-one structure.**

---

## M. 1/32 and 1/108 capacity arithmetic

`V11PairModCapacity.lean` — **CAPACITY_ONLY**, rational arithmetic only.

```
shiftedFixedMultiplierSaving = 1/32
qkLowerEndpointSaving        = 1/108
worstMargin = min(1/32, 1/108) = 1/108        (worstMargin_eq)
tax < 1/108  ⟹  0 < worstMargin − tax        (tax_below_worst_leaves_margin)
1/18 > 1/108                                  (oneEighteenth_gt_oneOneOhEight)
worstMargin − 1/18 = −5/108 < 0               (sqrtY_familyTax_kills_qk_margin)
```

A `Y^{1/2} = X^{1/18}` family tax therefore kills the worst QK margin.  Nothing
here is an analytic theorem, and no saving is claimed to be achievable.

---

## N. Pair-modulus analytic interface

`V11FMPerronPairModInterface.lean` — `FMPerronPairModSourceMultiplierInput`,
**uninhabited**, with fields: actual source multiplier data; index dictionaries
and `grammar : FMPerronGrammarCertificate` for all coefficient slots;
`rankOne`; `primeExtrema : PrimeExtremaRealisation` together with
`generatedTwistCancellation`; `fixedBackend`; **`movingFamilyCoherence`** (the
genuine analytic estimate, supplied — never derived from `fixedBackend` or from
ℓ² energy); the two parent values with `diagonalPart`/`sharedGPart` routers and
the exact routing identity; `packetCost`; and the two budgets.

Non-circularity: no field is the target proposition.  The budgets constrain the
*bounds*, and the routers are exact identities.  `norm_parentValue_le` is the
one derived inequality.

The package is uninhabited in this project because it demands a
`PrimeExtremaRealisation` (absent) and an S2 generated-twist cancellation.

---

## O. Parent compiler

`V11PairModParentCompiler.lean` defines the **new project-local** predicates

```
ShiftedQuotientParentBound (V) (X) (s)  :=  ‖V‖ ≤ X^(1−s)
QK56FullCovarianceBound   (V) (X) (s)  :=  ∀ k, ‖V k‖ ≤ X^(1−s)
```

(neither name existed in the repository) and proves the two deterministic
implications

```
pairMod_to_shiftedQuotientParent : package → ShiftedQuotientParentBound (parent 0) X (1/32)
pairMod_to_qk56FullCovariance    : package → QK56FullCovarianceBound parent X (1/108)
```

with guards showing neither predicate is automatic.

**PAIRMOD → SHIFTED PARENT: CONDITIONAL COMPILER.**
**PAIRMOD → QK56 PARENT: CONDITIONAL COMPILER.**

---

## P. V10 analytic-leaf bridge

`V11PairModToV10Leaves.lean`

The exact V10 field types are real absolute-value bounds
`|leafValue .highPrime| ≤ leafBudget .highPrime`, etc.  `V11AnalyticLeafBundle`
collects **exactly those four** fields, and

```
pairModPackage_to_v10AnalyticLeaves :
  package → (assignment of each leaf to a pair-modulus parent)
          → (dictionary leafValue l = (parentValue (assign l)).re)
          → (budget pin X^(1−1/108) ≤ leafBudget l)
          → V11AnalyticLeafBundle leafValue leafBudget
```

is **type-correct and proved**.  **No type mismatch arises.**  A full
`Gate1BClosureInputs` is deliberately not constructed: V10 also requires
`zeroFork`, `S1NormalizationPin`, `S2DeltaScalarPin`, the census and the budget.

`V11V10Compatibility.lean` gives the one safe compatibility statement,
`gate1B_closed_of_v11_leaves_and_v10_pins`, which **applies** (never duplicates)
V10's `gate1B_closed_of_exact_inputs` after the user supplies every non-analytic
ingredient.  Guard: `leaves_alone_do_not_close_gate1B`.

**PAIRMOD → V10 FOUR LEAVES: PROVED.**

---

## Q. Generated Type-II reassembly

`V11GeneratedTypeIIReassembly.lean` — `GeneratedTypeIIReassembly` (exact source
packet decomposition, generated certificate for every transformed coefficient,
per-packet analytic bound, nuclear budget) ⟶
`fmPerronGeneratedTypeII_of_reassembly : FMPerronGeneratedTypeIIAtScale d`.

The target is the **v11** predicate.  The old `FullTypeIIBound` is *not*
targeted (no exact dictionary exists), and no Ford one-sixth theorem is defined.
Guard: no such certificate exists for `toyData`.

`V11FMPerronGrammarCompiler.lean` supplies the packet-family compiler
(`generatedPacketFamily_bound`) and the explicit shifted log exponent
(`shifted_log_budget`: `L^C · X·L^{−A} ≤ X·L^{C−A}`).

---

## R. Counterguards

`V11Counterguards.lean` — all six proved.

| | statement | name |
| --- | --- | --- |
| A | a 1-bounded sequence realised by **no** admissible generated atom | `counterguard_A_generatedAtoms_are_not_all_unitBounded` |
| B | pure Mellin control ≠ `P±` control (coordinate and semantic forms) | `counterguard_B_mellin_ne_primeExtrema`, `counterguard_B_semantic` |
| C | fixed-multiplier bounds ≠ moving-family bound | `counterguard_C_fixed_ne_moving` |
| D | ℓ² multiplier energy ≠ coherent cancellation; rank-one gives no saving | `counterguard_D_l2Energy_ne_coherence`, `counterguard_D_rankOne_no_saving` |
| E | the conditional compiler is not a Ford–Maynard theorem | `counterguard_E_compiler_is_not_a_theorem` |
| F | generated analytic leaves ≠ Gate-1B closure | `counterguard_F_leaves_ne_closure` |

---

## S. Axiom audit

`V11Status.lean` runs `#print axioms` on **99** principal v11 declarations.
Every one reports exactly

```
[propext, Classical.choice, Quot.sound]
```

**SORRY: NONE.  USER AXIOMS: NONE.**  `sorry`, `admit`, `axiom`, `opaque`,
`unsafe`, `native_decide`, `@[implemented_by]` occur in no v11 module (the only
occurrences of those words are inside documentation comments that state their
absence).

---

## T. Current Gate 1B status

**GATE1B: OPEN / UNCHANGED.**

The four analytic leaves (HIGHPRIME-MSWITCH, SAMEQ, CROSSMOD, H9) remain open;
v11 adds a *route* to them from a pair-modulus analytic package, but that
package is uninhabited.  The V10 source/zero/normalisation pins are untouched
and still required.  Full Type II is not proved.  Twin primes are not declared
anywhere.

---

## REQUIRED FINAL CLASSIFICATION

```
FM SIEVEGEN PROJECT PREDICATE:      DEFINED
FM PERRON GENERATED GRAMMAR:        DEFINED + PROVED FINITE COST THEOREMS
REAL FORD GRAMMAR CERTIFICATE:      UNINHABITED / REPO DATA ABSENT
FMPERRON GENERATED TYPE-II PREDICATE: DEFINED
SIEVEGEN -> GENERATED:              PROVED
GENERATED -> SIEVEGEN:              NOT CLAIMED
S2 PURE MELLIN:                     INTERFACE (uninhabited) / PROVED FINITE COMPILER
S2 Pminus/Pplus:                    OPEN ANALYTIC INTERFACE
PAIRMOD SOURCE VALUE:               DEFINED
FIXED-vs-MOVING MULTIPLIER FIREWALL: PROVED
SOURCE MULTIPLIER RANK-ONE ALGEBRA: PROVED (exact finite ℓ¹/ℓ² factorisation, reused)
SHIFTED CAPACITY:                   1/32 CAPACITY ONLY
QK CAPACITY:                        1/108 CAPACITY ONLY
WORST MARGIN:                       1/108
PAIRMOD ANALYTIC INPUT:             UNINHABITED
PAIRMOD -> SHIFTED PARENT:          CONDITIONAL COMPILER
PAIRMOD -> QK56 PARENT:             CONDITIONAL COMPILER
PAIRMOD -> V10 FOUR LEAVES:         PROVED
GENERATED TYPE-II REASSEMBLY:       CONDITIONAL COMPILER
GATE1B:                             OPEN
```

---

## FINAL VERDICT

```
V11_FM_PERRON_PAIRMOD_SAFE_BANK_PARTIAL

REGRESSION:  PASS
BUILD:       PASS
SORRY:       NONE
USER AXIOMS: NONE
V10:         PRESERVED

NEW LEAN-PROVED FINITE/ALGEBRA:
  generated-atom unit bounds; ramp window bounds; deterministic expression cost
  on a window; product / ℓ¹-sum / divisor-convolution bounds; finite template
  reassembly; generated-class closure (product, sum, scalar, Dirichlet
  convolution, finite linear combination); SieveGen ⟹ Generated; finite
  summation by parts for the defect transform (reused); P± firewall (coordinate
  and semantic); prime-extrema values at 4 and 8 forced by the interface;
  Mellin separation 8^{it} = −4^{it} at t = π/log 2; moving-multiplier √K loss;
  ℓ²-energy non-determination; rank-one ℓ¹/ℓ² factorisation (reused);
  1/32 · 1/108 · 5/108 capacity arithmetic; counterguards A–F.

NEW CONDITIONAL COMPILERS:
  generatedPacketFamily_bound + shifted_log_budget;
  fmPerronGeneratedTypeII_of_reassembly;
  pairMod_to_shiftedQuotientParent; pairMod_to_qk56FullCovariance;
  pairModPackage_to_v10AnalyticLeaves;
  gate1B_closed_of_v11_leaves_and_v10_pins (applies V10, does not duplicate it).

EXTERNAL ANALYTIC INTERFACES (all uninhabited):
  PrimeExtremaRealisation; S2PureMellinCancellation;
  S2PrimeExtremaTwistCancellation; S2PerronGeneratedCancellation;
  FMPerronPairModSourceMultiplierInput; RealFordGrammarCertificate.

FIRST FORMAL BLOCKER:
  TwinPrimeProject.Gate1BV11.PrimeExtremaRealisation — no least/greatest
  prime-factor function exists in the repository, so no semantic realisation of
  the leastPrimeTwist / greatestPrimeTwist atoms, and hence no
  RealFordGrammarCertificate, can be constructed.

FIRST RESEARCH ANALYTIC BLOCKER:
  FM-PERRON-PAIRMOD-SOURCE-MULT45
  (the movingFamilyCoherence field: a genuine cancellation estimate for the
  moving Θ-family, which the firewalls show cannot come from fixed-multiplier
  bounds, from ℓ² source energy, or from rank-one structure)

GATE1B: OPEN / UNCHANGED
```
