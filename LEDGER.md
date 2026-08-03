# LEDGER — Primitive Form C Localization, Balanced Square-Root Wall, Conditional Parity Routes

This ledger banks the algebraic/modular structure of the primitive two-outer
problem for the balanced Möbius bilinear sum, records the controlled and
degenerate sectors with their exact provisional status, and lays out a clean
dependency graph for the next campaign.

**Status taxonomy** is fixed in `RequestProject/Status.lean` (`Banking.BankStatus`).
Every Lean label below is machine-checked in the module indicated; the build is
clean (`lake build` succeeds, no `sorry`/`admit`/`axiom`/`implemented_by` in the
new modules).

Global nonclaims (unchanged): **no** Primitive Form C, **no** full Form C, **no**
balanced `r=3`, **no** full F3/F1/F2, **no** balanced Type-II, **no** twin
primes, **no** Hardy–Littlewood, **no** parity breaking.

---

## A. Executive table

| Label | Status | Exact content | Dependencies | Nonclaim |
| ----- | ------ | ------------- | ------------ | -------- |
| `TWO_OUTER_LATTICE_IDENTITY` | LEAN_PROVED | `m₂q₁r₁ − m₁q₂r₂ = 2(m₂−m₁)` from `qᵢrᵢ = mᵢn+2` | — | not a counting bound |
| `PRIMITIVE_INNER_LATTICE_COUNT` | LEAN_PROVED | `D₁a₁b₁ − D₂a₂b₂ = h₀`, `Dᵢ,h₀` as in §6 | lattice identity | not the lattice-point count |
| `PRIMITIVE_FORM_C_RESIDUE` | LEAN_PROVED_CORE | `r₁ ≡ 2(m₂−m₁)·overline{m₂q₁} (mod m₁q₂)` | lattice identity, inverse witness | invertibility supplied as witness |
| `PRIMITIVE_FORM_C_R2_RECONSTRUCTION` | LEAN_PROVED_CORE | `m₁q₂·r₂ = m₂q₁r₁ − 2(m₂−m₁)` | lattice identity | integrality only |
| `PRIMITIVE_LATTICE_SOLVABILITY` | LEAN_PROVED | `(∃b₁, A·b₁≡h₀ mod C) ↔ gcd(A,C)∣h₀` | — | not a count |
| `PRIMITIVE_B1_PROGRESSION` | LEAN_PROVED | reduced congruence ↔ `b₁ ≡ h'·overline{A'} (mod C')` | inverse witness | modular only |
| `PRIMITIVE_B2_RECONSTRUCTION` | LEAN_PROVED | `C·b₂ = A·b₁ − h₀` | — | integrality, separate from solvability |
| `PRIMITIVE_RECIPROCITY_SPLIT` | LEAN_PROVED | `e(2jx̄/C)=e(−2jȳ/A)·e(2j/(AC))`, coprime `A,C` | additive character lemmas | modular reciprocity only |
| `PRIMITIVE_ARCHIMEDEAN_PHASE_SMALL` | CONDITIONAL_INTERFACE | scaling: `2/D ≤ 2·X^{−1+ε}` if `D ≥ X^{1−ε}` | — | negligible global error not asserted |
| `PRIMITIVE_PHASE_DETERMINANTS` | PROVISIONAL_REDUCTION | `D_I, D_II` defs + elementary consequences | — | analytic phase formula not asserted |
| `PRIMITIVE_ZERO_MODE_MAIN_TERM_DEFINED` | PROVISIONAL_REDUCTION | `MT_prim` structure (density/progression) | progression | not the global dispersion expected term |
| `PRIMITIVE_B1_POISSON_COMPLETION` | EXTERNALLY_AUDITED | Poisson identity for the `b₁`-progression | smoothness/coprimality | not Lean-formalized |
| `PRIMITIVE_NONZERO_PHASE` | EXTERNALLY_AUDITED | phase `e(2j(m₂−m₁)·overline{m₂q₁a₁}/(m₁q₂a₂))` | Poisson | — |
| `PRIMITIVE_FREQUENCY_RANGE` | EXTERNALLY_AUDITED | `|j| ≪ X^{μ+1/3+ε}` | Poisson | — |
| `P1_GENERIC_DEFICIT` | LEAN_PROVED | `(3μ+2)−(μ+4/3)=2μ+2/3` | — | exponent arithmetic only |
| `BALANCED_P1_DEFICIT` | LEAN_PROVED_CORE | value `2μ+2/3` | — | exponent only |
| `BALANCED_P2_DEFICIT` | LEAN_PROVED_CORE | value `μ+1/3` | — | exponent only |
| `BALANCED_P3_DEFICIT` | LEAN_PROVED_CORE | value `1/12+3μ/4`; identity `(5/12−μ/4)−(1/3−μ)` | — | exponent only |
| `BALANCED_P4_SATURATION` | LEAN_PROVED_CORE | `8/3−δ < 8/3` | — | not "no method can cross" |
| `BALANCED_ADDITIVE_DIVISOR_SURPLUS` | LEAN_PROVED_CORE | value `4μ/3` | — | exponent only |
| `ADDITIVE_DIVISOR_SURPLUS_EXACT_CONDITION` | LEAN_PROVED_CORE | `2μ+2/3 ≤ (2/3+κ)(μ+1) ↔ 4μ/3 ≤ κ(μ+1)` | — | analytic AD theorem is OPEN |
| `ADDITIVE_DIVISOR_SURPLUS_SIMPLE_SUFFICIENT_CONDITION` | LEAN_PROVED_CORE | `μ≤3κ/4 ⇒ 4μ/3≤κ(μ+1)` (sufficient, **not** equivalent) | — | marked sufficient only |
| `ABL_SCALE_MATCH_PENDING_FORMULA_AUDIT` | PROVISIONAL_REDUCTION | `δ_ABL(μ)=1/12−μ/2>0 ↔ μ<1/6`; `1664/10000<1/6` | — | analytic derivation pending transcription |
| `P1_EXACT_DIAGONAL_REPORTED` | PROVISIONAL_REDUCTION | `≪ X^{μ+1+ε}` | — | counting not Lean-proved |
| `P1_DEGENERATE_REPORTED` | PROVISIONAL_REDUCTION | `≪ X^{μ+1+ε}` (`D_II=0,m₁=m₁'`) | — | counting not Lean-proved |
| `P1_NEAR_DEGENERATE_REPORTED` | PROVISIONAL_REDUCTION | `≪ X^{2μ+1+ε}`; `2μ+1<μ+4/3 ↔ μ<1/3` | exponent lemma | counting not Lean-proved |
| `P1_DIVISIBILITY_PINNED_REPORTED` | PROVISIONAL_REDUCTION | `≪ X^{2μ+1/3+ε}`; below target for `μ<1` | exponent lemma | counting not Lean-proved |
| `PRIMITIVE_FORM_C_LOCALIZATION` | PROVISIONAL_REDUCTION | (LOC) bound; conditional exponent `μ+1−δ/2` Lean-proved | `Ξ_gen` bound (hyp) | localization inequality is a hypothesis |
| `CORRELATED_NUMERATOR_KF_FORM_XI` | PROVISIONAL_REDUCTION | generic `D_II≠0` kernel `Ξ_gen` | — | named research object |
| `P1_CORRELATED_NUMERATOR_LOG` | OPEN_INPUT | `|Ξ_gen| ≪_A X^{μ+4/3}(log X)^{−A}` | — | — |
| `P1_CORRELATED_NUMERATOR_POWER` | OPEN_INPUT | `|Ξ_gen| ≪ X^{μ+4/3−δ}` | — | — |
| `BILINEAR_LEVEL_SPECTRAL_LARGE_SIEVE` | OPEN_INPUT | Kloosterman family, level `c=m₁q₂a₂` | — | existence not denied |
| `PRIMITIVE_FOURTH_MOMENT_SAVING` | OPEN_INPUT | `tr((KK*)²) ≪ X^{8/3−δ}` | operator inequalities (Lean) | — |
| `RANK_ONE_WEIGHTED_ABL_QUINTILINEAR` | OPEN_INPUT | rank-one signed-modulus ABL 2.3 remap | — | — |
| `ABL_SIGNED_MODULUS_WEIGHT_MATCH` | OPEN_INPUT | signed `(c,d)` coefficients in ABL 2.3 | — | ABL not claimed to accept them |
| `F1_AGGREGATE_MU_CONVOLUTION_MAIN_TERM` | OPEN_INPUT | aggregate short Möbius `μ^{*j}`, `ζ(s)^{−j}` | — | — |
| `TYPE_III_MINOR_ARC_OPERATOR` | OPEN_INPUT | `qab−mn=2` minor-arc bilinear operator | — | — |
| `FIXED_SHIFT_CONTAGION` | OPEN_INPUT | `h=2` obstruction propagates to nearby shifts | — | not inferred from almost-all-shift |
| `FORD_MAYNARD_PRIME_PRODUCING_SIEVE_FRAMEWORK` | LITERATURE_VERIFIED | Type I/II ⇒ optimal prime bounds framework | arXiv:2407.14368 | numerics not promoted |
| `FORD_MAYNARD_NU_0_1663_SOURCE_AUDIT` | NUMERICAL_SOURCE_PENDING | `ν>0.1663 ⇒ positive lower bound`; `ν≥1/3` | arXiv:2407.14368 | exact thm/table not yet located |
| `ABL_THEOREM_2_3_QUINTILINEAR_INPUT` | LITERATURE_VERIFIED | quintilinear input, vars `C,D,N,R,S`, weight `b_{n,r,s}` | arXiv:2005.13915 | signed `(c,d)` not claimed |
| `SAWIN_SHUSTERMAN_FUNCTION_FIELD` | LITERATURE_VERIFIED_CONTEXT | function-field twin primes | — | not an integer interface |
| `CONDITIONAL_PARITY_BREAK_CHAIN` | CONDITIONAL_INTERFACE | dependency chain to conditional prime LB | all OPEN inputs | no parity break claimed |
| `PRIMITIVE_FORM_C_REDUCED_TO_NEW_INPUT` | PROVISIONAL_REDUCTION | Fable verdict | — | not upgraded |
| `FORM_C_OPEN` / `RESTORATION_OPEN` / `FULL_F1_OPEN` / `F2_OPEN` | OPEN_INPUT | Fable verdicts | — | — |
| `F3_TWO_OUTER_PARTIAL` | PROVISIONAL_REDUCTION | see interpretation below | — | no complete `r=3` fragment |
| `NEW_EXACT_WALL` | PROVISIONAL_REDUCTION | tested canonical-route deficits | — | not universal impossibility |
| `ABSOLUTE_BD_REFUTED` … `PARITY_BROKEN_REFUTED_AS_STATUS` | REFUTED | see §E | — | last three: unsupported claims, not false conjectures |

**`F3_TWO_OUTER_PARTIAL` interpretation:** exact primitive geometry; exact main
term at the local Poisson level; exact completion and reciprocity; some reported
controlled P1 strata; localization to `Ξ_gen`; **no** newly controlled complete
`r=3` fragment.

---

## B. Primitive Form C graph

```text
lattice identity            [LEAN_PROVED]
  -> primitive residue       [LEAN_PROVED_CORE]
  -> exact b1 progression    [LEAN_PROVED]
  -> zero-mode main term     [PROVISIONAL_REDUCTION]
  -> Poisson phase           [EXTERNALLY_AUDITED]
  -> reciprocity             [LEAN_PROVED]
  -> P1 determinants         [PROVISIONAL_REDUCTION]
  -> controlled reported strata  [PROVISIONAL_REDUCTION]
  -> Xi_gen                  [OPEN]
  -> primitive Form C        [OPEN]
```

---

## C. Literature parity graph

```text
Ford–Maynard framework        [LITERATURE VERIFIED]   (arXiv:2407.14368)
Ford–Maynard numerical threshold [SOURCE PENDING]     (nu > 0.1663 ; nu >= 1/3)

ABL Theorem 2.3               [LITERATURE VERIFIED]    (arXiv:2005.13915)
ABL signed modulus match      [OPEN]
ABL scale substitution        [PROVISIONAL]            (delta_ABL = 1/12 - mu/2)

weighted ABL + full reassembly + verified sieve threshold
  -> conditional parity-breaking lower bound   [CONDITIONAL]
```

---

## D. Alternative routes

* `F1_AGGREGATE_MU_CONVOLUTION_MAIN_TERM` — aggregate short Möbius variables
  before absolute values, coefficient `μ^{*j}`, Dirichlet series `ζ(s)^{−j}`.
  [OPEN_INPUT]
* `TYPE_III_MINOR_ARC_OPERATOR` — for `qab−mn=2`, minor-arc bilinear operator
  exploiting the rank-one `mn`-side and three-variable `qab`-side. [OPEN_INPUT]
* `FIXED_SHIFT_CONTAGION` — inverse theorem propagating an `h=2` Type-II
  obstruction to nearby shifts; not inferred from almost-all-shift results.
  [OPEN_INPUT]
* F2 hybrid `m`–`q` Kloosterman large sieve. [OPEN_INPUT]

---

## E. Refuted / superseded

`ABSOLUTE_BD_REFUTED`, `ABSTRACT_POISSON_DIAGONAL_FALSE`,
`FALSE_MPAIR_ONE_OVER_G_REFUTED`, `UNRESTRICTED_Q_MESOSCOPIC_FALSE`,
`FULL_ROUTED_PIECE_POWER_SAVING_REFUTED_AS_STATED`,
`TWO_OUTER_SINGLE_OUTER_AUTOEXTENSION_REFUTED`, `FORM_C_PROVED_REFUTED_AS_STATUS`,
`BALANCED_R3_PROVED_REFUTED_AS_STATUS`, `PARITY_BROKEN_REFUTED_AS_STATUS`.

The last three mean the **claims are unsupported**, not that the mathematical
conjectures are false.

---

## F. Retained single-outer ledger (unchanged)

`CW_MU_CONDUCTOR_WINDOW_BANKED`, `F3_R2_BD_REDUCTION`, `F3_R2_MAIN_TERM_KILLED`,
`LOW_MID_CONDUCTORS_CONTROLLED`, `ACTUAL_KF_DIAGONAL_PROVED`,
`KF_OFFDIAG_CROSSCOPRIME_PROVED`, `RESIDUAL_COLLAPSE_PROVED`,
`COMPLETE_DOUBLE_CROSS_PHASE_FACTORIZED`, `ONE_MODULUS_FOURIER_SEPARATION`,
`FOURIER_LOSS_DM_SQRT`, `RATIO_SPLIT_WRIGHT_WEDGE_PROVED`,
`ACTUAL_KF_WEDGE_122_162`, `F3_FIXED_DEPTH_ROUTABLE_SECTOR_PROVED`,
`LONG_MOBIUS_F1_MIGRATION_ROUTABLE_PROVED`.

**Current strongest banked unconditional high-conductor theorem:**
`122μ + 162θ < 1 ⟹ 𝒦 ≪ (X²/N)·X^{−η}` (region recorded in
`FrontierStatus.highConductorRegion`). A complete routed piece has arbitrary
logarithmic saving; only the high-conductor component has fixed power saving.

---

## G. Dependency DAG (labels)

```text
TWO_OUTER_LATTICE_IDENTITY
 ├─ PRIMITIVE_INNER_LATTICE_COUNT
 │   └─ PRIMITIVE_LATTICE_SOLVABILITY ─ PRIMITIVE_B1_PROGRESSION ─ PRIMITIVE_B2_RECONSTRUCTION
 ├─ PRIMITIVE_FORM_C_RESIDUE
 └─ PRIMITIVE_FORM_C_R2_RECONSTRUCTION
        └─ PRIMITIVE_ZERO_MODE_MAIN_TERM_DEFINED
               └─ PRIMITIVE_B1_POISSON_COMPLETION ─ PRIMITIVE_NONZERO_PHASE ─ PRIMITIVE_FREQUENCY_RANGE
                      └─ PRIMITIVE_RECIPROCITY_SPLIT (+ PRIMITIVE_ARCHIMEDEAN_PHASE_SMALL)
                             └─ PRIMITIVE_PHASE_DETERMINANTS
                                    └─ {P1_EXACT_DIAGONAL, P1_DEGENERATE, P1_NEAR_DEGENERATE, P1_DIVISIBILITY_PINNED}
                                           └─ CORRELATED_NUMERATOR_KF_FORM_XI (Ξ_gen)
                                                  └─ {P1_CORRELATED_NUMERATOR_LOG|POWER}  [OPEN]
                                                         └─ PRIMITIVE_FORM_C_LOCALIZATION (conditional exponent μ+1−δ/2)
                                                                └─ primitive Form C  [OPEN]

RANK_ONE_WEIGHTED_ABL_QUINTILINEAR [OPEN]
 └─ Type II through ν [CONDITIONAL]
      └─ F1/F2/F3 reassembly [OPEN]
           └─ FORD_MAYNARD Type I/II hypotheses [OPEN]
                └─ positive prime-producing lower bound [CONDITIONAL ON VERIFIED THRESHOLD]
```

---

## H. Deliverable lists (§29.5)

* **Lean-proved:** `TWO_OUTER_LATTICE_IDENTITY`, `PRIMITIVE_INNER_LATTICE_COUNT`,
  `PRIMITIVE_LATTICE_SOLVABILITY`, `PRIMITIVE_B1_PROGRESSION`,
  `PRIMITIVE_B2_RECONSTRUCTION`, `PRIMITIVE_RECIPROCITY_SPLIT`,
  `P1_GENERIC_DEFICIT`, all exponent comparisons/identities, operator
  Cauchy–Schwarz, and (as `_CORE`) the residue/reconstruction, calibration,
  ABL algebra, localization/fourth-moment conditional implications.
* **Externally audited:** `PRIMITIVE_B1_POISSON_COMPLETION`,
  `PRIMITIVE_NONZERO_PHASE`, `PRIMITIVE_FREQUENCY_RANGE`.
* **Literature-verified:** `FORD_MAYNARD_PRIME_PRODUCING_SIEVE_FRAMEWORK`,
  `ABL_THEOREM_2_3_QUINTILINEAR_INPUT`;
  context: `SAWIN_SHUSTERMAN_FUNCTION_FIELD`.
* **Provisional reductions:** `PRIMITIVE_PHASE_DETERMINANTS`,
  `PRIMITIVE_ZERO_MODE_MAIN_TERM_DEFINED`, all `P1_*_REPORTED`,
  `PRIMITIVE_FORM_C_LOCALIZATION`, `CORRELATED_NUMERATOR_KF_FORM_XI`,
  `ABL_SCALE_MATCH_PENDING_FORMULA_AUDIT`, Fable verdicts.
* **Numerical-source-pending:** `FORD_MAYNARD_NU_0_1663_SOURCE_AUDIT`.
* **Conditional interfaces:** `PRIMITIVE_ARCHIMEDEAN_PHASE_SMALL`,
  `CONDITIONAL_PARITY_BREAK_CHAIN`.
* **Open inputs:** `P1_CORRELATED_NUMERATOR_LOG/POWER`,
  `BILINEAR_LEVEL_SPECTRAL_LARGE_SIEVE`, `PRIMITIVE_FOURTH_MOMENT_SAVING`,
  `RANK_ONE_WEIGHTED_ABL_QUINTILINEAR`, `ABL_SIGNED_MODULUS_WEIGHT_MATCH`,
  `F1_AGGREGATE_MU_CONVOLUTION_MAIN_TERM`, `TYPE_III_MINOR_ARC_OPERATOR`,
  `FIXED_SHIFT_CONTAGION`, `FORM_C_OPEN`, `RESTORATION_OPEN`, `FULL_F1_OPEN`,
  `F2_OPEN`.
* **Refuted/superseded:** see §E.

---

## I. Audit note — Ford–Maynard numerical thresholds

Primary source: Kevin Ford and James Maynard, *On the theory of prime producing
sieves*, arXiv:2407.14368.

Banked as `LITERATURE_VERIFIED` (framework only): nonnegative sequences
satisfying specified Type I and Type II estimates admit optimal prime upper and
lower bounds determined by a general sieve framework.

**Not promoted.** The numerical claims
`ν > 0.1663 ⇒ positive prime lower bound` and `ν ≥ 1/3` are recorded as
`NUMERICAL_SOURCE_PENDING`. In the present environment external browsing / the
paper source files were **not available**, so the exact theorem, proposition,
table, numerical certificate, or source-code output backing these thresholds has
**not** been located, and the parameter definitions `(γ, θ, ν)` have not been
matched to the current Type I/II normalization. These thresholds must not be
upgraded until an exact source is cited and the normalization is verified. In
particular no prime-producing significance is attached to `0.1664`.

---

## J. Audit note — ABL scale substitution

Primary source: Edgar Assing, Valentin Blomer, Junxian Li, *Uniform Titchmarsh
divisor problems*, arXiv:2005.13915.

`ABL_THEOREM_2_3_QUINTILINEAR_INPUT` banked as `LITERATURE_VERIFIED`: variables
`C,D,N,R,S`; arbitrary coefficient sequence `b_{n,r,s}`; smooth compactly
supported five-variable weight; an additional parameter `a` not subject to a
restrictive upper bound; proof via Kuznetsov and a spectral large sieve. It is
**not** claimed to accept arbitrary signed coefficients in its `(c,d)` variables
(`ABL_SIGNED_MODULUS_WEIGHT_MATCH` = OPEN_INPUT).

Proposed scale substitution `C=D=X^{2/3}`, `N_ABL=X^{1/3+μ}`, `R=S=X^μ` gives a
reported predicted exponent `11/12 + 3μ/2` against target `1+μ`, hence formal
saving `δ_ABL(μ)=1/12−μ/2`. **Only the algebra** `δ_ABL(μ)>0 ↔ μ<1/6` and
`1664/10000 < 1/6` is Lean-proved (`ABLScaleArithmetic`). The analytic
derivation is `PROVISIONAL_REDUCTION` until the full displayed Theorem 2.3
formula is transcribed and each term substituted
(`ABL_SCALE_MATCH_PENDING_FORMULA_AUDIT`).

---

## K. Lean module map

`RequestProject/`: `Status.lean`, `PrimitiveLattice.lean`, `PrimitiveResidue.lean`,
`PrimitiveProgression.lean`, `ReciprocalIdentity.lean`,
`DispersionDeterminants.lean`, `DeficitArithmetic.lean`,
`AdditiveDivisorCalibration.lean`, `ABLScaleArithmetic.lean`,
`ParityDependencyGraph.lean`, `FrontierStatus.lean`, `Banking.lean`.

Build: `lake build` (from the project root) — completes successfully.

---

# PART II — Audited Prime Short-Window Update (Kloosterman / trace-function frontier)

This part banks the audited prime-model short-window campaign. The exact
finite-field identities and all linear-algebra/exponent arithmetic are
**machine-checked in Lean with no `sorry`/`admit`/`axiom`/`implemented_by`**;
analytic theorems are recorded as literature interfaces or open inputs (never
axioms). Key theorems reduce to only `propext`, `Classical.choice`, `Quot.sound`.

**Global nonclaims (this part):** no arbitrary-λ short-window control; no
Möbius-vector short-window control; no quadrilinear `hm v̄ w̄` theorem; no
composite-modulus lift; no balanced `r=3`; no full Type II; no parity breaking;
no twin primes; no Hardy–Littlewood.

## II.A Exact theorem table (Lean-proved)

| Label | Status | Exact content | Module |
| ----- | ------ | ------------- | ------ |
| `KLOOSTERMAN_COMPLETE_ORTHOGONALITY` | LEAN_PROVED | `∑_m S(a,m)·conj S(b,m) = p(p·1_{a=b} − 1)` | `KloostermanOrthogonality` |
| `Q_SHEAR_COMPLETE_PERIOD_ENERGY` | LEAN_PROVED | `∑_m |F_p(m)|² = p(p‖λ‖₂² − |∑λ|²)` | `KloostermanOrthogonality` |
| `PRIME_SHORT_WINDOW_FOURIER_IDENTITY` | LEAN_PROVED | `C_p(ℓ)=p∑_{q,q'}λ_q λ̄_{q'}[e_p(−κ(q⁻¹+q'⁻¹))S(κq'⁻¹,κq⁻¹)−1]`, `κ=uℓ⁻¹`, `ℓ≠0` | `PrimeShortWindowFourier` |
| `twisted_orthogonality` | LEAN_PROVED | `∑_m S(a,m)conj S(b,m)e_p(ℓm)=p(e_p(−(a+b)ℓ⁻¹)S(aℓ⁻¹,bℓ⁻¹)−1)` | `PrimeShortWindowFourier` |
| `NORMALIZED_KLOOSTERMAN_TRACE_CONVERSION` (`kloosterman_eq_sqrt_mul_kl2`) | LEAN_PROVED | `S(a,b;p)=p^{1/2}Kl₂(ab;p)`, `a≠0` | `PrimeShortWindowFourier` |
| `SHORT_WINDOW_FOURIER_NORMALIZATION` | LEAN_PROVED | `∑_m W(m)|F|² = p⁻¹∑_ℓ Ŵ(ℓ)C_p(ℓ)` | `PrimeShortWindowFourier` |
| `SHORT_WINDOW_SINGULAR_VALUE_LOWER_BOUND` | LEAN_PROVED | `‖A‖_op ≥ ‖A‖_HS/√rank`; `hs²≥cp², rank≤Q ⟹ op ≥ √c·p/√Q` | `SingularValueLowerBound` |
| `PRIME_INVERSE_KLOOSTERMAN_SAVING_1_224` | LEAN_PROVED_CORE | `δ(l)=(l−7)/(8l²)` maximized at `l=14`, `δ(14)=1/224` | `FKMSExponentArithmetic` |
| `PRIME_FACTORIZED_TRACE_SAVING_1_16` | CONDITIONAL_INTERFACE | `1/16 < 1/6`: `p^{−1/16}` misses `Q^{−1/2}≤p^{−1/6}` | `FKMSExponentArithmetic` |
| `FACTORABILITY_SUBSET_SUM_POLYTOPE` | LEAN_PROVED | subset-sum set; block `≥1/(3k)`; `1/6,1/8,1/12` not automatic; `k=1` indivisible | `FactorabilityPolytope` |
| `FORD_MAYNARD_POSITIVITY_WINDOW` | LITERATURE_VERIFIED | window ordering `0.1616 < 0.1663 < 1/3`; certified interval `[0.1616,0.1663]` | `FordMaynardThresholds` |

Supporting Lean-proved lemmas: `ep_orthogonality`, `ep_conj`, `ep_primitive`,
`units_char_sum`, `kloosterman_conj`, `kloosterman_symm`, `kloosterman_reindex`,
`finite_fourier_inversion`, `twisted_reduction`, `twisted_ycollapse`,
`twisted_bij_sum`, `twisted_value_id`, `twisted_RHS_reform`.

## II.B Literature-source interfaces

| Label | Status | Recorded shape |
| ----- | ------ | -------------- |
| `FKMS_INVERSE_MONOMIAL_BILINEAR` | LITERATURE_VERIFIED | `InverseMonomialBilinear` struct: exponents `b,c≠0`, moment `l`, saving field |
| `FKMS_INVERSE_MONOMIAL_TRILINEAR` | LITERATURE_VERIFIED | `InverseMonomialTrilinear` struct: `q=vw`, `V=p^{1/4}`, `l=2`, saving field |
| `FORD_MAYNARD_POSITIVITY_WINDOW` | LITERATURE_VERIFIED | `FordMaynardWindow` struct at `(γ,θ)=(1/2,0)` |

Numerical thresholds are banked as an interval `[0.1616,0.1663]`; `0.1663` is
**not** claimed as the exact positivity threshold.

## II.C Provisional / conditional application table

| Label | Status | Meaning |
| ----- | ------ | ------- |
| `ARBITRARY_LAMBDA_FROM_FOURIER` | CONDITIONAL_INTERFACE | Fourier-mode control on `0<|ℓ|≪Qp^ε` ⟹ arbitrary-vector short-window bound |
| `ARBITRARY_LAMBDA_SW_SPECTRALLY_CRITICAL_INTERIOR` | EXTERNALLY_AUDITED | `Q≤p^{1/2−δ}` ⟹ target spectrally critical (op-norm at rank scale) |
| `ARBITRARY_LAMBDA_SW_ENDPOINT` | PROVISIONAL | `Q≍p^{1/2}` endpoint criticality |
| `PRIME_FACTORIZED_TRACE_SAVING_1_16` | CONDITIONAL_INTERFACE | needs actual three-factor coefficient decomposition |

## II.D Open analytic inputs

| Label | Status | Recorded shape |
| ----- | ------ | -------------- |
| `MOBIUS_VECTOR_SHORT_WINDOW` | OPEN_INPUT | `MobiusVectorShortWindow` struct (weaker than arbitrary-λ) |
| `AUTOCORRELATION_PRESERVING_JOINT_QH` | OPEN_INPUT | `AutocorrelationPreservingJointQH` struct; `h=r₂−r₁`, `h=0` separate |
| `MOBIUS_KILLS_TOP_SINGULAR_VECTOR` | OPEN_INPUT | not a theorem |

## II.E Superseded / rejected routes (route, not conjecture)

| Label | Status |
| ----- | ------ |
| `GENERIC_WEIGHTED_ABL` | SUPERSEDED_ROUTE |
| `ONE_SIDED_WEIGHTED_ABL` | SUPERSEDED_ROUTE |
| `PER_Q_ABL` | REFUTED_ROUTE |
| `ALL_MODULI_INTERVAL_AFTER_INVERSION` | REFUTED |
| `AUTOMATIC_ONE_SIXTH_FACTORIZATION` | REFUTED |
| `KNOWN_QUADRILINEAR_HMVBARWBAR` | SOURCE_NOT_FOUND |

## II.F Dependency DAG

```text
complete-period orthogonality (LEAN_PROVED)
  -> prime Fourier identity (LEAN_PROVED)
  -> short-window trace form / normalization (LEAN_PROVED)

FKMS bilinear/trilinear interfaces (LITERATURE_VERIFIED)
  -> structured prime subcases only (CONDITIONAL_INTERFACE)

actual block vector β
  -> factorability polytope (LEAN_PROVED)
  -> Möbius-vector short window [OPEN]

rank-one α autocorrelation
  + Möbius-vector factorization
  -> joint (q,h) trace theorem [OPEN]
  -> prime-model Type-II fragment
  -> composite lift
  -> balanced r=3
  -> F1/F2/F3 reassembly
  -> Ford–Maynard interface (LITERATURE_VERIFIED)
```

## II.G Strongest banked theorem and exact open frontier

- **Strongest banked (unconditional, Lean-proved):** the
  `PRIME_SHORT_WINDOW_FOURIER_IDENTITY` — the exact complete-period expansion of
  the short-window energy Fourier modes into inverse-product Kloosterman trace
  values, together with `KLOOSTERMAN_COMPLETE_ORTHOGONALITY` and the spectral
  lower bound.
- **Exact open frontier:** `ARBITRARY_LAMBDA_SHORT_WINDOW` is spectrally
  critical (`SHORT_WINDOW_SINGULAR_VALUE_LOWER_BOUND` shows the operator target
  sits exactly at the rank lower-bound scale `√(Hp)`); the missing input is an
  operator-norm bound at that scale, i.e. either `ARBITRARY_LAMBDA_FROM_FOURIER`
  (Fourier-mode control) or the trace-function bilinear/trilinear inputs applied
  to a genuinely factored coefficient. `MOBIUS_VECTOR_SHORT_WINDOW` and
  `AUTOCORRELATION_PRESERVING_JOINT_QH` remain open.
