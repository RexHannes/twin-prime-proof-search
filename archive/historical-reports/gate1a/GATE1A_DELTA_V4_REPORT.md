# ARISTOTLE — GATE 1A DELTA v4 — FINAL REPORT

All Lean artifacts for this addendum live in `Gate1A/Delta4/` (14 modules),
inside the existing `Gate1A` lake library.  Nothing previously banked was
deleted, weakened, or replaced.

Soundness invariants held throughout:

* no `sorry`, no `admit`, no `axiom` declaration, no `opaque`,
  no `@[implemented_by]`, no `native_decide` anywhere in `Gate1A/Delta4/`;
* every genuinely unproved analytic input is an **explicit hypothesis /
  structure field**, never an assumption smuggled in as an axiom;
* the §28 unconditional theorem is **not** created.

---

## §30 REQUIRED FINAL REPORT

### AUTHORITATIVE SOURCE

`Gate1A/Delta4/RootSource.lean`.  The canonical physical root data is carried
by the structure `RootData` with the literal fields

```
m' = m + k r,     m w₀ ≡ -2 (mod r),     0 ≤ w₀ < r,     r α = m w₀ + 2.
```

No guessed source shape is imported; the `α`-range and the root collapse are
*derived* from these fields.

### ALPHA RANGE

`alpha_range` — PROVED.  From the `RootData` fields alone,

```
0 ≤ α    and    α < m + 2/r    (in ℚ).
```

`alpha_is_integer` records the integrality step.  The Archimedean consequence
is `archimedean_alpha_bound`:

```
H |α| / (p q m)  ≤  3 · H / L²      on the support p, q ≥ L, m ≥ 1, r ≥ 1.
```

The constant is the *explicit* `3`, not an unquantified `X^{o(1)}`.

### ROOT-COLLAPSE

`root_phase_m_component_cancels` — PROVED, exactly:

```
r α = m w₀ + 2,   r β = (m + k r) w₀ + 2   ⟹   (m + k r) α − m β = 2k.
```

Corollaries `root_phase_m_component_cancels_zmod` (in `ZMod n`, any modulus)
and `root_phase_m_component_cancels_exp` (at the level of `e(x) = exp(2πix)`)
are banked.  The identity is exact modular arithmetic — no Archimedean
approximation replaces a modular phase anywhere.

### OPTION A

RETAINED, not re-derived.  The previously banked quotient/Poisson work is
untouched in `Gate1A/QuotientRecombination.lean`, `Gate1A/QuotientKernel.lean`,
`Gate1A/SineDecomposition.lean`, `Gate1A/ThetaPhase.lean` and
`Gate1A/SourceInterfaces.lean`, together with the parameter-smooth
Schwartz-family statement and the counterexample showing that uniform
row-wise Schwartz control does **not** imply bounded source nuclear
transport (`Gate1A/NuclearCountermodels.lean`).  `h = 0` remains firewalled
and is never absorbed into the quotient theorem.

### FLAT PROFILE

`Gate1A/Delta4/FlatProfile.lean`.  The perturbation algebra for

```
Φ_y(x) = Φ_flat(x) · ∏ (near-1 factors)
```

is proved in a normed commutative ring:

* `norm_prod_sub_one_le`, `one_add_pow_le` — the elementary product estimates;
* `phase_factor_close_to_one` — for a removed Archimedean phase with
  `|c_y| ≤ C U⁻¹` (source-α phase, θ phase, exact sine linear phase, TLSR
  phase);
* `amplitude_factor_close_to_one` — the sine amplitude correction
  `1 + O(U⁻² x²)`;
* `flat_profile_remainder_le_Uinv` — the assembled statement

```
‖Φ_y − Φ_flat‖ ≤ (2^n − 1) ‖Φ_flat‖ · U⁻¹ ,
```

`n` being the number of near-1 factors (five here).  Only *Archimedean*
factors are removed; the hard modular phases are never touched.

### FLAT ERROR

`ε = U⁻¹` is treated at amplitude/operator level and is never compared
directly to `H/M`.  `error_absorbed_root_scale` (in `FlatProfile.lean`) is the
abstract root-error theorem: `main ≤ √δ · B`, `err ≤ ε · B`, `ε ≤ √δ`
⟹ `(main + err)² ≤ 4 δ B²`.

### ERROR ROOT MARGINS

`Gate1A/Delta4/Scale.lean`, exponent arithmetic over `ℚ` on the polytope
`a ≥ 5/18`, `b ≥ 1/3`, `a + b ≤ 5/8`:

* `uInv_over_sqrt_saving_eq_sqrt_M_over_D`:  `U⁻¹ / √(H/M) = √(M/D)`;
* `error_root_capacity`: `U⁻¹ ≤ √(H/M)` with a **uniform** margin `1/48`;
* vertex margins `error_root_margin_V1/V2/V3`:

```
V1 = (5/18, 1/3)    →  1/36
V2 = (5/18, 25/72)  →  1/36
V3 = (7/24, 1/3)    →  1/48
```

Scale identities `D H = L²`, `R K = M`, `M² H = R L²`, `M K = L²/H` are
`scale_DH`, `scale_RK`, `scale_MsqH`, `scale_MK`.

### TWO-SIDED S2

**RETRACTED.**  `Gate1A/Delta4/S2Upper.lean` banks the finite countermodels

* `l1_control_not_l2_equivalence`,
* `no_two_sided_S2_constant` — there is **no** constant `K` with
  `∑|g|² ≤ K ∑|f|²` for all finite vectors of equal `ℓ¹` mass.

No statement of the form "source norm ≍ transported norm" is used anywhere in
the Gate closure.

### S2-UPPER

`one_sided_source_transport_l2` — PROVED by Minkowski, in the *original*
index space `ℓ²(E)`:

```
C = Σ_λ c_λ C_λ + Err,   Σ_λ |c_λ| ≤ C₀,   ‖C_λ‖ ≤ B
⟹ ‖C‖ ≤ C₀ B + ‖Err‖.
```

`one_sided_source_transport_l2_pi` is the coordinatewise variant.  The order
rule is respected: the mode decomposition is performed **before** the TF4
expansion, the outer four-cycle and the projective energy expansion — the
theorem is stated on the source index set `E`, so no cross terms are Cauchy'd
after a TF4 step.

`Gate1A/Delta4/RankOne.lean` supplies the compatibility needed for that
order: `smooth_pq_separation_preserves_rankOne` (exact separable expansion
`F(u,v,x) = Σ_λ c_λ(x) A_λ(u) B_λ(v)` acts as `b_p ↦ b_p A_λ(L/p)`,
`d_q ↦ d_q B_λ(L/q)`, so each mode stays rank-one in the prime variables) and
`rankOne_nuclear_bound` for the absolute summability.

### PB Z-COORDINATE

`Gate1A/Delta4/PBAxis.lean`.  With `P₀ = p₁p₂`, `Q = q₁q₂`,
`Z := Q a + P₀ n`:

* `pb_phase_eq_Z_over` — the exact identity
  `a/(r P₀) + n/(r Q) = Z/(r P₀ Q)`;
* `pb_phase_factors_through_Z`, `pbRowWeight_depends_only_on_Z_n` — the PB
  smooth row weight depends on the pair `(Z, n)` only, in the shape
  `MK/(r P₀ Q) · V̂(M Z/(r P₀ Q), K n/Q)`.

The *analytic* lattice bound for the actual sheared lattice is **not** proved
and is carried as the explicit interface field `correctedPBAnalytic`.

### Z=0 ⇒ a=n=0

`Z_zero_forces_a_zero_n_zero` — PROVED, via `Z_zero_divisibility`
(`gcd(P₀,Q)=1` and `Q a + P₀ n = 0` give `P₀ ∣ a`, `Q ∣ n`) plus the
truncations `|a| < P₀`, `|n| < Q`, which is exactly what the support bound
`|a|, |n| ≤ M H X^{o(1)}` together with `M H / L² = M/D < 1` provides
(`MH_over_Lsq_eq_M_over_D`, `MH_over_Lsq_lt_one`, margin `1/24`).

Hostile guard `Z_zero_needs_both_truncations`: **one** truncation is not
enough — `P₀ = 3`, `Q = 5`, `(a,n) = (3,−5)` sits on `Z = 0` with `|a| < Q`
and `a ≠ 0`.

### L=0 ⇒ h1=h2=0

`L_zero_forces_h1_h2_zero` — PROVED, via `L_zero_dvd_h1`
(`p₂q₂h₁ = p₁q₁h₂` with four pairwise distinct primes gives `p₁q₁ ∣ h₁`) and
the truncation `|h₁| < p₁q₁`, which follows from `|h_i| ≪ H X^{o(1)}` and
`H/L² < 1` (`H_over_Lsq_lt_one`, margin `3/8`).  So `L = 0` maps exactly onto
the `h = 0` firewall.

Hostile guard `L_zero_needs_distinct_primes`: without pairwise distinctness
the conclusion fails (`p₁=p₂=2`, `q₁=q₂=3`, `h₁=h₂=1`).

### Z=0, r∤L

`Gate1A/Delta4/OuterAxis.lean`.  `outer_axis_local_factor` proves the **full
corrected dictionary** for a primitive additive character mod a prime `r`:

```
S_r(0, L) =  −1      if r ∤ L,
             r − 1   if r ∣ L.
```

On the regular branch (`r ∤ L`) the factor is exactly `−1`;
`outer_regular_axis_contraction` and `outer_axis_plancherel` (reusing the
banked `Gate1A/Kloosterman.lean` Plancherel identity) show the restriction to
the one-zero axis is a contraction in the normalized local Hilbert norm, so
that branch is at most its natural axis mass.  The four inner factors are
`inner_axis_local_factor_neg_one`, stated **with the hypothesis `p ∤ h`**
(see the hostile-audit note below).

### Z=0, r|L

Treated as a **true local zero / rank-conductor-loss** branch, never as a
generic projective point.

* `outer_axis_not_always_minus_one` — formally refutes the retracted claim
  that all five local factors are always `−1`: for `r ≥ 3` with `r ∣ L` the
  outer factor is `r − 1 ≠ −1`.
* `outer_true_zero_is_rank_loss` — the local pair is `(Z,L) ≡ (0,0) mod r`.
* `outer_true_zero_divisor_bound` — divisor sparsity: for fixed nonzero `L`,
  the number of prime `r ∣ L` is at most `2^ω(|L|) ≤ |L|`, i.e. `X^{o(1)}`
  in the gate range.

This branch is a routing entry with a proved map, not a comment.

### GENERIC S3

`Gate1A/Delta4/Projective.lean`.

**Correction found by hostile audit.**  The addendum's identity
`P = Σ_{w≠0} ‖C_w‖²` with `C_w = Σ_{Z L = w} A_Z ⊗ conj B_L` is *not* the
collision relation `Z₁L₂ = Z₂L₁`: `product_class_ne_ratio_class` exhibits
integer states with `Z₁L₂ = Z₂L₁` but different products, and states with
equal products but `Z₁L₂ ≠ Z₂L₁`.  The correct grouping is by the projective
**ratio** class, and with that grouping the identity is exact
(`class_energy_identity`, `ratioClass_eq_iff_cross`, `norm_sum_sq_expand`).

`generic_projective_pushforward_bound` then gives, with class multiplicity
`≤ τ`:

```
Σ_classes ‖C_class‖²  ≤  τ · (Σ_Z ‖A_Z‖²)(Σ_L ‖B_L‖²)-type mass.
```

Character splitting is `character_tuple_splits` / `character_multiplicative`:
row characters (`χ_r(Z)`, `χ_{p_i}(a)`, `χ_{q_i}(n)`) go into `A_Z`, graph
characters (`χ_r(L)`, `χ_{p_i}(h_i)`, `χ_{q_i}(h_i)`) into `B_L`, and the
character tuple is retained as a direct-sum label.  No auxiliary label
depends simultaneously on row and graph variables.

### PRIME-QUADRUPLE NO-TAX

`projective_sum_over_prime_quadruples_no_extra_tax` — PROVED: from
`P_pvec ≤ C_X · D_pvec` for every ordered quadruple, `Σ_pvec P_pvec ≤ C_X ·
Σ_pvec D_pvec`.  Orthogonality of quadruples is **not** assumed, and no extra
`L⁴` is introduced.  `quadruple_comparator_is_sum` checks from the definitions
that `Σ_pvec D_pvec` is literally the banked TF4 diagonal comparator.

### OUTER R^-1

`Gate1A/Delta4/Curvature.lean`.  With `Δ_out = Z₁L₂ − Z₂L₁`:

* `deltaOut_indep_of_moving_prime` — once all non-`r` coordinates are fixed,
  `Δ_out` is an integer independent of the moving prime `r`;
* `outer_collision_forces_r_dvd_deltaOut` — `Δ_out ≠ 0` plus an outer local
  collision forces `r ∣ Δ_out`;
* `curvature_divisor_multiplicity`, `family_saving_from_multiplicity` —
  combining the common flat source class, one-sided S2 and finite divisor
  multiplicity gives the family-energy saving `T_nonzero ≤ R^{−1+o(1)}
  T_natural`.

No arbitrary-moving-coefficient theorem is used.

### FACE CASCADE

`Gate1A/Delta4/FaceCascade.lean`.
`clean_block_bound_without_face_savings` (and its explicit five-term form
`clean_block_bound_five_sectors`) derives the whole clean full-conductor block
bound from the five §25 sector bounds **only** — no `p₁,p₂,q₁,q₂`
divisor-family input appears anywhere in the hypotheses.  Hence

```
P_Q_FACE_CASCADE : NON_LOAD_BEARING_FOR_MAIN_CLEAN_BLOCK
```

recorded as `pqFaceCascadeStatus` / `pq_face_cascade_non_load_bearing`.
The old face lemmas are **kept** as fallback bank; nothing was deleted.

The label is honest about its scope: it says the *derivation* needs no face
input.  It does not assert that all five sector bounds are already
unconditional here — sectors B–E are proved in the abstract forms above and
the remaining analytic input is carried by `Delta4OpenInterfaces`.

### EXCEPTION ROUTING

`Gate1A/Delta4/Interfaces.lean`, `routingStatus` — a *total* function on the
eleven required items, with no bare word "frozen".  `routingStatus_total` and
`routingStatus_open_items` certify the table:

| item | status |
|---|---|
| `h = 0` | OPEN (the map `L = 0 ↦ h₁=h₂=0` is proved; the firewall **bound** is not) |
| same `q` | OPEN |
| repeated prime | OPEN |
| cross-role `p = q` | OPEN |
| nonunit | OPEN |
| principal character | OPEN |
| proper conductor | OPEN |
| local one-zero axis | PROVED MAP (`outer_regular_axis_contraction`) |
| true local zero | PROVED MAP (`outer_true_zero_is_rank_loss`, `outer_true_zero_divisor_bound`) |
| PB alias | OPEN |
| balanced-lift boundary | OPEN |

Two proved maps, nine open.

### ROOT DEPTH

`Gate1A/Delta4/RootDepth.lean` and `Scale.lean`.

* `four_cycle_input` reuses the banked `Gate1A/FourCycle.lean` matrix bound
  `‖A_r‖_op² ≤ Σ_{m,m'} ‖T_{r,m} T*_{r,m'}‖²_HS` (note `hsNormSq` is the
  *squared* HS norm);
* `single_cauchy_over_r` — exactly one Cauchy over `r`:
  `Σ_r ‖A_r‖_op ≤ √R · √(Σ_r T4_r)`;
* `root_depth_assembly` — the assembled statement, with no second root;
* `root_depth_capacity` — `M R^{−1/2} ≤ H` in exponents, uniform margin
  `1/12`; vertex margins `root_depth_margin_V1/V2/V3`:

```
V1 = 1/12,   V2 = 1/9,   V3 = 5/48.
```

`both_root_margins_positive` records that the error root (§8) and the depth
root (§24) are the only two square roots taken and are simultaneously
affordable on the whole polytope — the explicit answer to hostile item 7.

### FINAL NORMALIZED TARGET

```
Σ_{r,k,m} |C̃_{r,k,m}|²  ≤  M H L⁴ · X^{o(1)}
```

`normalizedTarget` in `Gate1A/Delta4/Interfaces.lean`; concluded by
`gate1a_of_final_interfaces`, conditional on the explicit open interfaces.

### FINAL PHYSICAL TARGET

```
Σ_e |C_e|²  ≤  M L⁴ / H · X^{o(1)}  =  M D² H · X^{o(1)}
```

`physicalTarget`, with the exact conversions `physical_eq_normalized_div_Hsq`
(`physical = normalized / H²`) and `physicalTarget_eq_MDsqH` (using
`D H = L²`).  Both conclusions are delivered by the same theorem.

### LAKE BUILD

Succeeds.  `Build completed successfully (8318 jobs)` on the full default
target set (all libraries, including all previously banked material).

Token scan of `Gate1A/Delta4/`: `sorry` 0, `admit` 0, `axiom` declarations 0,
`opaque` 0, `native_decide` 0, `@[implemented_by]` 0.  (The single textual
hit is the word `axiom` inside a documentation comment.)

### #PRINT AXIOMS

`Gate1A/Delta4/Status.lean` runs `#print axioms` on **every** principal Δv4
theorem (≈ 70 declarations).  Every one reports at most

```
[propext, Classical.choice, Quot.sound]
```

and many report `does not depend on any axioms`.  No non-standard axiom
appears anywhere.

### FIRST REMAINING UNPROVED INTERFACE

**Flat-profile source legality** — the identification of the authoritative
Fourier source profile `C̃_{r,k,m}` with the schematic flat-main form
`Φ_flat · (five near-1 factors)`.  The perturbation algebra downstream of
that identification is fully proved (`flat_profile_remainder_le_Uinv`); what
is missing is the analytic legality of the identification itself.  It is
carried as the field `Delta4OpenInterfaces.flatProfileSourceLegality`.

The other explicit interfaces, in order: `correctedPBAnalytic` (the PB
lattice bound for the true sheared lattice), `hZeroFirewallBound`,
`exceptionalSectorsBound` (the nine `open_` table rows), `sourceCoherence`.

### FINAL GATE STATUS

```
GATE1A_CLOSURE_FORMALISED_CONDITIONAL_ON_EXPLICIT_INTERFACES
```

**Not** `GATE1A_DIRECT_GENERIC_CLOSED_UNDER_FROZEN_CLEAN_BANK`: §28 forbids
the unconditional theorem while any listed item remains an assumption, and
five interfaces plus nine exceptional rows remain assumptions.  There is
deliberately no declaration named
`gate1a_direct_generic_closed_under_frozen_clean_bank` in the project;
`delta4_closure_is_conditional` records this in Lean.

---

## §31 HOSTILE FALSIFICATION — findings

1. **`Z = 0` axis tested against `r ∣ L`.**  The retracted claim fails, as
   suspected: `outer_axis_not_always_minus_one` proves the outer factor is
   `r − 1`, not `−1`.  Repaired by the two-branch dictionary
   `outer_axis_local_factor` and the separate rank-loss route.
2. **"`q_i ∤ h_i` on quotient support".**  *Not proved.*  It is carried as an
   explicit hypothesis of `inner_axis_local_factor_neg_one`.  Reported as an
   assumption, not as a theorem.
3. **`L = 0 ⇒ h₁ = h₂ = 0` under the actual truncation.**  Survives, but only
   with pairwise distinct primes: `L_zero_needs_distinct_primes` shows the
   statement is false without that hypothesis, so the hypothesis is stated
   explicitly rather than left implicit in "clean".
4. **Prime-quadruple comparator normalization.**  Survives:
   `quadruple_comparator_is_sum` checks from the definitions that the
   comparator is the banked TF4 diagonal, with no second `L⁴`.
5. **Accidental `ℓ¹` collapse of Hilbert direct-sum coordinates.**  The
   direct-sum labels (character tuple, auxiliary modes) are kept as genuine
   coordinates in `Projective.lean`; the only `ℓ¹` input is the mode
   coefficient sum `Σ|c_λ| ≤ C₀` in S2-UPPER, which is a hypothesis on
   scalars, not on Hilbert coordinates.
6. **Mode decomposition after TF4.**  Avoided by construction: S2-UPPER is
   stated on the source index set `E`, before any four-cycle expansion.
7. **Hidden second square root.**  Audited: `both_root_margins_positive` and
   `single_cauchy_over_r` pin down exactly two roots (error root, depth root),
   both with positive margin.
8. **A true local zero remaining full conductor.**  Blocked: the `r ∣ L`
   branch is routed to rank-loss / divisor sparsity, and
   `outer_axis_not_always_minus_one` prevents it being folded into the
   regular axis.
9. **An auxiliary label depending on both row and graph variables.**  The
   character split `character_tuple_splits` places each factor in exactly one
   of `A_Z`, `B_L`; the rank-one separation theorem keeps `p/q` smooth modes
   in the prime source variables only.
10. **A modular inverse misclassified as smooth Archimedean.**  The flat
    profile removes only the four Archimedean phases plus the sine amplitude;
    the root-collapse identity is proved as an exact modular identity, and
    `root_phase_m_component_cancels_zmod` states it in `ZMod n`.

Additional finding not on the list: the §20 product-grouping identity is
false as written (item **GENERIC S3** above); the theorem is banked in the
corrected ratio-grouping form.

---

## Relation to the earlier banking task

The earlier Type-II / F3(r=2) KF tiny wedge banking work is **unchanged** by
this addendum.  Its status codes, dependency DAG and verdicts stay exactly as
recorded in `LEDGER.md`, `BankStatus.md`, `DEPENDENCY_GRAPH.md`,
`UNCONDITIONAL_STATUS.md` and `GATE1A_REPORT.md`; nothing here upgrades any
`PROVISIONAL_NEW` entry to `SAFE_BANKED`, and no parity, twin-prime,
Hardy–Littlewood or full TII-core claim is made.
