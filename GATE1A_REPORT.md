# Gate-1A — Complete Leanification / Hostile Formal Bank

**Controlling final label:**

```
GATE1A_FIXED_QUOTIENT_CORE_FORMALISED
```

(equivalently, in the vocabulary of the first prompt,
`GATE1A_FINITE_CORE_FORMALIZED_SOURCE_INTERFACES_OPEN` together with
`GATE1A_CONDITIONAL_CLOSURE_FORMALIZED`.)

The mathematical status is unchanged by this run:

```
GATE1A_DIRECT_GENERIC_OPEN
```

There is **no** theorem `gate1a_direct_generic_closed` and **no** theorem
equivalent to `GATE1A_DIRECT_GENERIC_CLOSED_UNDER_FROZEN_SOURCE_BANK`.
The source interfaces are hypotheses, not results.

---

## H. Toolchain

* Lean `v4.28.0` (`lean-toolchain`).
* Mathlib pinned by `lake-manifest.json`, rev `8f9d9cff6bd728b17a24e163c9402775d9e6a365`.
* Library `Gate1A` (`lakefile.toml`, `globs = ["Gate1A.+"]`), a default target.

## G. `lake build` result

```
Build completed successfully (8304 jobs).
```

`rg -n "sorry|admit|^axiom |native_decide" Gate1A/` returns only occurrences
inside prose comments (the words "sorry" and "axiom" used to record the
soundness policy, and the English word "admits"). There is no `sorry`, no
`admit`, no `axiom`/`constant` declaration, and no `native_decide` in the
project.

---

## A. Theorem dependency DAG

Arrows point from a module to the modules it depends on.

```
Exponents ──────────────┐
   ▲                    │
   │                    ▼
ErrorAlgebra        PoissonBruhat
   ▲                    ▲
   └──────┬─────────────┘
          │
SourceInterfaces ◄── Exponents
          ▲
          │
ConditionalClosure ◄── SourceInterfaces, ErrorAlgebra, Exponents,
                       PoissonBruhat, RankFloor, FourCycle, HardSupport

MovingFamily ──► (Mathlib inner-product spaces)
   ▲
Countermodels           (§10 / §11 finite refutations)

NuclearCountermodels    (A5 / A10 finite refutations)

Kloosterman ──► (Mathlib AddChar / ZMod)
CRTSign     ──► (Mathlib ZMod.chineseRemainder, Int.ModEq)
CenteredIncidence ──► Kloosterman-style AddChar orthogonality
QuotientKernel ──► (Mathlib Complex.exp geometric series)
SineDecomposition ──► QuotientKernel-style exponentials, Mathlib Real.sin
QuotientRecombination ──► SchwartzMap.tsum_eq_tsum_fourier, SineDecomposition
ProjectivePacket ──► (Mathlib Finset / ℂ)
NormedTransport ──► MovingFamily, ProjectivePacket, EuclideanSpace
FourCycle ──► (Mathlib Matrix, trace)
RankFloor ──► FourCycle, Matrix.IsHermitian.spectral_theorem
Projectors ──► (Mathlib Matrix.PosSemidef)
ThetaPhase ──► (Mathlib Complex norm)
HardSupport ──► (Mathlib Int/Nat.Prime)

Status ──► every module above
```

Logical dependency of the three public closure theorems:

```
gate1a_fixed_quotient_core            (UNCONDITIONAL)
   ├── gate1a_reqExp_neg
   ├── gate1a_outer_capacity
   ├── gate1a_face_capacity
   ├── ErrorAlgebra.route_A_theta_retained_admissible
   ├── ErrorAlgebra.route_B_theta_discarded_admissible
   ├── gate1a_projective_exp_neg
   ├── PoissonBruhat.pb_normalisation_one
   └── PoissonBruhat.pb_normalisation_two

gate1a_of_S1_S2_S3                    (CONDITIONAL on S1, S2, S3, margins)
   └── gate1a_conditional_closure

gate1a_direct_generic_of_interfaces   (CONDITIONAL on §17 source interfaces
gate1a_candidate_closed_of_...            + analytic interfaces + margins)
   └── gate1a_conditional_closure
```

---

## B. Fully kernel-checked theorems

All of the following are proved with no `sorry` and no project axiom.

### Exponent / vertex ledger (§2) — `Gate1A/Exponents.lean`

Definitions `mExp = 1/3`, `hExp a b = a + 2b − 2/3`, `kExp a = 1/3 − a`,
`dExp a`, `reqExp a b = a + 2b − 1`, `uInvExp a b = a + b − 2/3`,
`epsExp a b = 2a + 2b − 4/3`, `projExp a b = 2 − 3a − 4b`;
`structure Polytope a b` (`a ≥ 5/18`, `b ≥ 1/3`, `a + b ≤ 5/8`);
`V1 = (5/18, 1/3)`, `V2 = (5/18, 25/72)`, `V3 = (7/24, 1/3)` with membership.

* `gate1a_DH_eq_Lsq`, `gate1a_RK_eq_M`, `gate1a_MsqH_eq_RLsq`,
  `gate1a_H_over_M`, `gate1a_eps_eq_two_uInv`, `gate1a_proj_two_forms`
* `gate1a_outer_capacity`, `gate1a_outer_capacity'`  (A: `−a/2 ≤ a+2b−1`, i.e. `(3/2)a + 2b ≥ 1`)
* `gate1a_face_capacity`, `gate1a_face_capacity'`  (B: `−b/2 ≤ a+2b−1`, i.e. `a + (5/2)b ≥ 1`)
* `gate1a_u2_error_capacity`  (C: `epsExp ≤ reqExp/2` on the whole polytope)
* `gate1a_u2_margin_v1/v2/v3` = `1/12`, `5/72`, `1/16`
* `gate1a_outer_margin_v1/v2/v3` = `1/12`, `1/9`, `5/48`
* `gate1a_face_margin_v1/v2/v3` = `1/9`, `7/48`, `1/8`
* `gate1a_projective_exp_v1/v2/v3` = `−1/6`, `−2/9`, `−5/24`
* `gate1a_projective_exp_neg`, `gate1a_reqExp_neg`, `gate1a_polytope_nonempty`

### Finite Kloosterman layer (§3) — `Gate1A/Kloosterman.lean`

Convention-free: `psi : AddChar (ZMod q) ℂ` arbitrary, nondegeneracy carried
explicitly as `psi.IsPrimitive`. `kloosterman psi U V = ∑_{x ∈ (ZMod q)ˣ} psi (U x + V x⁻¹)`.

* `sum_units_eq`
* `kloosterman_neg_neg`  (K1, sign involution)
* `kloosterman_zero_zero : = (q : ℂ) − 1`, `kloosterman_axis_left`,
  `kloosterman_axis_right`  (K2; both axis values `= −1`)
* `kloosterman_local_correlation`  (K3, `∑_V S(U,V) conj S(U',V) = q² 1_{U=U'} − q`),
  derived from additive-character orthogonality, **not** assumed.

### Cross-q side-2 sign (§4) — `Gate1A/CRTSign.lean`

* `crt_frequency_relation_int` — `t ≡ t₁q₂ − t₂q₁ (mod q₁q₂)`
* `crt_side1_inverse` — `t₁ ≡ t q₂⁻¹ (mod q₁)`
* `crt_side2_inverse_negative` — `t₂ ≡ −t q₁⁻¹ (mod q₂)`  **← the load-bearing minus sign, kernel-checked**
* `crtSide2Equiv`, `crtSide2Equiv_fst`, `crtSide2Equiv_snd`,
  `cross_q_side2_negative` — the CRT bijection reconstructing the cross sum as
  `Y_{q₁}(t·unit₁) · conj Y_{q₂}(−t·unit₂)`
* `old_plus_plus_cross_q_false` — an explicit witness refuting the old
  plus/plus form (**depends on no axioms at all**)

### One-q centred all-mode incidence (§5) — `Gate1A/CenteredIncidence.lean`

* `dualLift_term`, `dualLift_zero_mode` (the `b = 0` Ramanujan mode, handled
  explicitly, not silently omitted), `dual_lift_incidence`
* `centered_dual_lift_incidence` — the all-mode identity
  `Z_q(k) = H ∑_s A_q(s) (1_{q | (m+rk)s − 2} − 1/q)`, containing principal,
  nonprincipal and `b = 0` modes uniformly.

### Quotient kernel (§6) — `Gate1A/QuotientKernel.lean`

* `E`, `E_add`, `E_zero`, `E_pow`, `E_eq_one_iff`, `E_int`, `betaKernel_of_dvd`
* `quotient_kernel_zero_mode` — `β°_j(0) = 0` (the `h = 0` firewall)
* `quotient_kernel_exact_nonzero` — the exact geometric-series formula for `h ≠ 0`,
  with explicit denominator-nonvanishing hypotheses.

### Exact sine decomposition (§7) — `Gate1A/SineDecomposition.lean`

* `two_I_sin`, `one_sub_exp`
* `sine_ratio_exact` — the exact phase × `sin(πh/q) / (pr sin(πh/pqr))` form,
  the linear `h/q` term retained exactly as phase, denominators explicitly nonzero
* `abs_sin_sub_self_le` — explicit calculus inequality `|sin x − x| ≤ |x|³/4` for `|x| ≤ 1`
* `sine_ratio_quadratic_error` — **quadratic**, not linear, amplitude error.
  No Taylor prose is invoked.

### Schwartz / Poisson quotient recombination (§8) — `Gate1A/QuotientRecombination.lean`

* `exact_poisson` — genuinely derived from Mathlib's
  `SchwartzMap.tsum_eq_tsum_fourier`, in Mathlib's own Fourier normalisation
* `quotient_recombination_of_dictionary` — the `θ`-retaining recombination
  identity, given the exact affine Fourier dictionary as a hypothesis
* `structure QuotientRecombinationEstimate` (`exactPoisson`, `aliasBound`,
  `wrapBound`, `quadraticAmplitudeBound`) and `total_close_to_main`, the proved
  downstream finite implication.

### Moving-family lemma (§9) — `Gate1A/MovingFamily.lean`

Hilbert-valued (`InnerProductSpace ℂ E`), dependent fibre types `Xi : P → Type`.

* `norm_sum_sq_le_diag_add_offdiag`, `fibre_energy_le`
* `moving_family_energy_le` — `E ≤ ∑_{p,x} a(p,x)² + D (∑_x A(x))²`
* `TAbs`, `coherenceNumerator`, `offdiag_energy_le_D_mul_coherence`

### Countermodels (§10, §11) — `Gate1A/Countermodels.lean`

* `blockPr_collision_card_le_one` — every distinct pair collides for ≤ 1 family element
* `moving_blocks_counterexample` — yet `E = S·N²`: bounded pair-collision
  multiplicity does **not** give a family-size saving for moving support
* `moving_blocks_diagonal`
* `common_envelope_energy` (`= S·N·(N−1)`), `common_envelope_diagonal` (`= S²·N`)
* `common_envelope_not_diagonal_saving`, `absolute_scale_vs_diagonal_scale_example`
  (`T_abs = S·(S·N)²`), `common_envelope_refutes_diagonal_saving`

### Nuclear-scale countermodels (A5, A10) — `Gate1A/NuclearCountermodels.lean`

* `uniform_row_smoothness_not_nuclear_transport` — uniform row smoothness does
  **not** yield a nuclear transport bound (identity matrix; every
  ℓ²-normalised rank-one decomposition costs nuclear ℓ¹ mass ≥ s)
* `scalar_l1_mass_not_operator_norm` — scalar ℓ¹ mass is not the operator norm

### Projective crossed convolution (§12) — `Gate1A/ProjectivePacket.lean`

* `projective_crossed_convolution` — `P = ∑_w ‖C_w‖²`, with the inner-product
  conjugation order **repaired** to Mathlib's convention (conjugate-linear in
  the first argument); the statement was changed, not the proof forced
* `projective_energy_le_of_factorMultiplicity` — `∑_w ‖C_w‖² ≤ τ (∑_z‖A_z‖²)(∑_l‖B_l‖²)`
  from a finite factor-multiplicity hypothesis (no divisor theorem used)

### Outer four-cycle (§13) — `Gate1A/FourCycle.lean`

* `hsNormSq`, `hsNormSq_eq_trace`, `gram`, `gram_conjTranspose`
* `outer_four_cycle_trace`, `outer_four_cycle_matrix` — proved as an **exact
  identity** `‖A‖_HS² = ∑_{m,m'} ‖T_m T_{m'}ᴴ‖_HS²` (stronger than the required `≤`)
* `mulVec_normSq_le`, `outer_four_cycle_operator` — the operator-norm corollary

### Root-depth error accounting (§14, A18/A19) — `Gate1A/ErrorAlgebra.lean`

* `square_norm_add_error` — `‖Main + Err‖² ≤ (√δ + ε)² B²`; the cross term is
  accounted for exactly (the error is **not** squared twice)
* `error_absorbed_of_le_sqrtSaving` — `ε ≤ √δ ⟹ ‖Main + Err‖² ≤ 4 δ B²`
* `route_A_theta_retained_admissible` — **Route A: θ EXACTLY RETAINED**, true
  amplitude error `ε = U⁻²`, admissible on the whole polytope
* `route_B_theta_discarded_admissible` — **Route B: θ DISCARDED WITH U⁻¹**,
  also admissible
* `polytope_a_le_third`, `route_A_stronger_than_route_B`

### Effective rank floor (§15) — `Gate1A/RankFloor.lean`

* `rank_floor_from_pointwise_hs` — Layer A, Cauchy–Schwarz
* `trace_sq_eq_sum_eigenvalues_sq`, `sq_sum_le_card_support_mul_sum_sq`
* `rank_floor_hs_of_rank_le` — **Layer B genuinely PROVED** (not left as an
  interface): for a complex matrix of rank ≤ K, `‖T‖_HS⁴ ≤ K ‖T Tᴴ‖_HS²`, via
  the spectral theorem for the Hermitian PSD matrix `T Tᴴ`
* `rank_floor_symbolic_new` — Layer C, the symbolic recombined-dimension floor
  `(tr A_r)²/N_new ≤ c · D_r / H`. The *value* of `N_new` is not claimed here;
  it lives in the source-interface layer (`recombinedDomain`).

### Hard-support finite exclusion (§16) — `Gate1A/HardSupport.lean`

* `at_most_one_moving_r_bad`, `bad_set_subsingleton`, `moving_r_bad_of_nu_zero_independent`.
  Covers exactly the listed unit conditions; no claim that all source hard
  indicators are classified.

### Normed transport and nuclear pushforward (§18, §19, A14, A15) — `Gate1A/NormedTransport.lean`

* `l2_sum_le` (Minkowski in `EuclideanSpace ℂ ι`), `nuclearMass`, `transported`,
  `envelope`, `envelope_nonneg`, `transported_norm_le`, `sum_envelope_eq_nuclearMass`
* `normed_transported_curvature` — the **corrected** theorem: the normalisation
  hypothesis `S · Nuclear² ≤ B_nat` is explicit, and the conclusion is
  `nonzeroCurvatureEnergy ≤ (D/S) B_nat`. `B_nat` is never silently replaced by
  a diagonal norm.
* `nuclear_projective_pushforward_bound` — `projectiveEnergy ≤ τ · N_diag` from
  `projective_crossed_convolution` + Minkowski/Cauchy. Fully proved and abstract.

### Theta phase, projectors, Poisson–Bruhat

* `Gate1A/ThetaPhase.lean` (A7): `theta_phase_separated`,
  `theta_phase_nuclear_cost`, `theta_phase_tail_bound`, `theta_phase_tail_bound_simple`
* `Gate1A/Projectors.lean` (A12): `IsProjector`, `IsProjector.posSemidef`,
  `centered`, `centered_isProjector`, `centered_posSemidef`, `subProjector_le`,
  `centered_le`, `centered_mul_sub`
* `Gate1A/PoissonBruhat.lean` (A9): `pb_normalisation_one`,
  `pb_normalisation_two` (the corrected normalisation), `pb_normalisations_equivalent`

### Closure theorems (§20, A20) — `Gate1A/ConditionalClosure.lean`

* `gate1a_fixed_quotient_core` — **unconditional**, an 8-part conjunction of
  the finite-core facts at an arbitrary polytope point;
  `gate1a_fixed_quotient_core_nonvacuous` shows the polytope is nonempty.
* `gate1a_conditional_closure` — the abstract finite closure.
* `gate1a_of_S1_S2_S3` — conditional on S1/S2/S3 and the numerical margins.
* `gate1a_direct_generic_of_interfaces` and
  `gate1a_candidate_closed_of_fixed_quotient_interfaces` — conditional on the
  full §17 source interfaces and the analytic interfaces.

---

## C. Explicit remaining interface hypotheses

All are `Prop`-valued `structure` fields in `Gate1A/SourceInterfaces.lean`.
**No term of any of these structures is ever constructed in this project.**

`Gate1ASourceInterfaces`:

| field | content |
|---|---|
| `postNuLiteral` | literal post-ν coefficient obeys the Gate normalisation `S·nuc² ≤ B_nat` |
| `side2CoordinateDictionary` | curvature branch genuinely routed through the kernel-checked **negative** side-2 cross formula |
| `phiFlatCensus` | every remaining factor accounted for; total equals the recorded amplitude error |
| `transformOrder` | quotient recombination and the all-mode `t/ν` transforms commute (source-preserving order) |
| `normedTransport` | the Gate-normalised transport bound for the *actual* source |
| `projectivePushforward` | actual row/graph nuclear decomposition at *diagonal* scale |
| `rankLossRouting` | literal routing of the `r`-local true-zero vector / proper-conductor sectors |
| `recombinedDomain` | the exact finite recombined source-domain size |

`Gate1AAnalyticInterfaces`: `pbSchwartzLatticeL1`,
`pbPrefactorTimesLatticeL1`, `pbSourceOperatorBound`, `thetaPhaseTailAdmissible`.

`QuotientRecombination.QuotientRecombinationEstimate`: `exactPoisson`,
`aliasBound`, `wrapBound`, `quadraticAmplitudeBound` — plus the affine Fourier
dictionary hypothesis `hDict` of `quotient_recombination_of_dictionary`.

Addendum branch interfaces: `S1FiveFaceIntertwiner`, `S2TF4Normalisation`,
`S3ProjectivePushforward`; and `Gate1ANumericalMargins` (not open — it is a
condition on explicit parameters, discharged by arithmetic at any concrete
instantiation).

---

## D. Retracted / repaired informal claims discovered during formalization

1. **RETRACTED — the old plus/plus cross-`q` side-2 form.** The correct CRT
   relation forces `t₂ ≡ −t q₁⁻¹ (mod q₂)`. Refuted by the explicit witness
   `CRTSign.old_plus_plus_cross_q_false`, which itself depends on no axioms.
   Banked: `OLD_PLUS_PLUS_CROSS_Q = false / superseded`,
   `SIDE2_NEGATIVE_ARGUMENT = theorem`.
2. **REPAIRED — inner-product conjugation order in the projective packet.**
   The displayed ordering was wrong under Mathlib's convention (conjugate-linear
   in the *first* argument). The Lean statement of
   `projective_crossed_convolution` was corrected; the proof was not forced.
3. **REPAIRED — `moving_family_energy_le` needs `0 ≤ D` explicitly.** The
   codegree bound alone does not give nonnegativity of `D` when `X` is a
   singleton, so `0 ≤ D` is a genuine hypothesis.
4. **UPGRADED — §15 Layer B.** The rank/Schatten inequality
   `‖T‖_HS⁴ ≤ K ‖T Tᴴ‖_HS²` was expected to become an interface. It is instead
   fully proved (`rank_floor_hs_of_rank_le`) and is **not** an interface.
5. **STRENGTHENED — §13 outer four-cycle.** Proved as an exact identity, not
   merely the requested inequality.
6. **CORRECTED — root-depth accounting.** The rule "square the error" is not
   used. `square_norm_add_error` retains the cross term exactly; the usable
   consequence needs `ε ≤ √δ`, i.e. the recombination error must be compared
   against `√(H/M)` at the amplitude/operator level.
7. **SEPARATED — ℓ¹ nuclear scale vs. diagonal ℓ² scale.** `B_nat` and `B_diag`
   are distinct packet fields and are never identified; the two countermodels
   in `NuclearCountermodels.lean` are the formal reason.
8. **BLOCKED — `N_old ≈ 2L²U` after quotient recombination.** The recombined
   domain size is not derived; it is the interface field `recombinedDomain`.
   `rank_floor_symbolic_new` is stated symbolically so that no domain size is
   smuggled in.
9. **CONDITIONAL — the A9 Schwartz-lattice ℓ¹ bound and the affine Fourier
   dictionary.** Naive box counting is not sufficient; these remain interfaces.

Hostile tests (§22) explicitly discharged: conjugation order (item 2);
`q₁/q₂` inverse placement and side-2 sign (items 1, `crt_side1_inverse` vs
`crt_side2_inverse_negative`); `h = 0` firewall (`quotient_kernel_zero_mode`);
integer `j` versus `q`-periodic (`betaKernel` is defined on `ℤ` with an explicit
`betaKernel_of_dvd`); division by zero in the sine ratio (explicit nonvanishing
hypotheses); `b = 0`/principal mode not omitted (`dualLift_zero_mode` feeding
`centered_dual_lift_incidence`); finite support (everything finite is over
`Finset`/`Fintype`, and the only infinite sums are Mathlib `tsum`s of Schwartz
functions); ℓ¹ vs ℓ² scales (item 7); `N_old` reuse (item 8); error squared
twice (item 6); scalar-vs-Hilbert-valued (`MovingFamily` and `NormedTransport`
are Hilbert-valued throughout); fixed vs moving prime family (the countermodels
in §10/§11 are exactly the refutation of that generalisation).

---

## E. Exact first unproved mathematical interface

```
Gate1A.SourceInterfaces.Gate1ASourceInterfaces.postNuLiteral
```

i.e. the literal derivation of the post-ν source coefficient from the
authoritative pre-square source, together with the statement that its nuclear
ℓ¹ mass `nuc` satisfies the Gate normalisation `S · nuc² ≤ B_nat`.

Immediately after it, and independent of it:

```
Gate1A.QuotientRecombination.quotient_recombination_of_dictionary  -- hypothesis hDict
```

the exact affine Fourier dictionary converting Mathlib's Fourier normalisation
into the source's `e_q(·)` convention for the sheared lattice.

---

## F. `#print axioms` for every principal public theorem

Every principal theorem depends on at most `[propext, Classical.choice,
Quot.sound]`, which are Mathlib's standard axioms. **No new project axioms.**

```
Gate1A.gate1a_outer_capacity                                    [propext, Classical.choice, Quot.sound]
Gate1A.gate1a_face_capacity                                     [propext, Classical.choice, Quot.sound]
Gate1A.gate1a_u2_error_capacity                                 [propext, Classical.choice, Quot.sound]
Gate1A.gate1a_projective_exp_v1                                 [propext, Classical.choice, Quot.sound]
Gate1A.moving_family_energy_le                                  [propext, Classical.choice, Quot.sound]
Gate1A.Countermodel.moving_blocks_counterexample                [propext, Classical.choice, Quot.sound]
Gate1A.Countermodel.common_envelope_not_diagonal_saving         [propext, Classical.choice, Quot.sound]
Gate1A.Countermodel.absolute_scale_vs_diagonal_scale_example    [propext, Classical.choice, Quot.sound]
Gate1A.Kloosterman.kloosterman_neg_neg                          [propext, Classical.choice, Quot.sound]
Gate1A.Kloosterman.kloosterman_local_correlation                [propext, Classical.choice, Quot.sound]
Gate1A.CRTSign.cross_q_side2_negative                           [propext, Classical.choice, Quot.sound]
Gate1A.CRTSign.old_plus_plus_cross_q_false                      does not depend on any axioms
Gate1A.CenteredIncidence.centered_dual_lift_incidence           [propext, Classical.choice, Quot.sound]
Gate1A.QuotientKernel.quotient_kernel_exact_nonzero             [propext, Classical.choice, Quot.sound]
Gate1A.QuotientKernel.quotient_kernel_zero_mode                 [propext, Classical.choice, Quot.sound]
Gate1A.SineDecomposition.sine_ratio_exact                       [propext, Classical.choice, Quot.sound]
Gate1A.SineDecomposition.sine_ratio_quadratic_error             [propext, Classical.choice, Quot.sound]
Gate1A.ProjectivePacket.projective_crossed_convolution          [propext, Classical.choice, Quot.sound]
Gate1A.ProjectivePacket.projective_energy_le_of_factorMultiplicity
                                                                [propext, Classical.choice, Quot.sound]
Gate1A.FourCycle.outer_four_cycle_matrix                        [propext, Classical.choice, Quot.sound]
Gate1A.FourCycle.outer_four_cycle_operator                      [propext, Classical.choice, Quot.sound]
Gate1A.ErrorAlgebra.square_norm_add_error                       [propext, Classical.choice, Quot.sound]
Gate1A.ErrorAlgebra.error_absorbed_of_le_sqrtSaving             [propext, Classical.choice, Quot.sound]
Gate1A.RankFloor.rank_floor_from_pointwise_hs                   [propext, Classical.choice, Quot.sound]
Gate1A.RankFloor.rank_floor_hs_of_rank_le                       [propext, Classical.choice, Quot.sound]
Gate1A.HardSupport.at_most_one_moving_r_bad                     [propext, Classical.choice, Quot.sound]
Gate1A.NuclearCountermodels.uniform_row_smoothness_not_nuclear_transport
                                                                [propext, Classical.choice, Quot.sound]
Gate1A.NuclearCountermodels.scalar_l1_mass_not_operator_norm    [propext, Classical.choice, Quot.sound]
Gate1A.ThetaPhase.theta_phase_nuclear_cost                      [propext, Classical.choice, Quot.sound]
Gate1A.ThetaPhase.theta_phase_tail_bound_simple                 [propext, Classical.choice, Quot.sound]
Gate1A.Projectors.centered_posSemidef                           [propext, Classical.choice, Quot.sound]
Gate1A.PoissonBruhat.pb_normalisation_two                       [propext, Classical.choice, Quot.sound]
Gate1A.NormedTransport.normed_transported_curvature             [propext, Classical.choice, Quot.sound]
Gate1A.NormedTransport.nuclear_projective_pushforward_bound     [propext, Classical.choice, Quot.sound]
Gate1A.QuotientRecombination.exact_poisson                      [propext, Classical.choice, Quot.sound]
Gate1A.QuotientRecombination.quotient_recombination_of_dictionary
                                                                [propext, Classical.choice, Quot.sound]
Gate1A.QuotientRecombination.total_close_to_main                [propext, Classical.choice, Quot.sound]
Gate1A.ConditionalClosure.gate1a_conditional_closure            [propext, Classical.choice, Quot.sound]
Gate1A.ConditionalClosure.gate1a_direct_generic_of_interfaces   [propext, Classical.choice, Quot.sound]
Gate1A.ConditionalClosure.gate1a_candidate_closed_of_fixed_quotient_interfaces
                                                                [propext, Classical.choice, Quot.sound]
Gate1A.ConditionalClosure.gate1a_of_S1_S2_S3                    [propext, Classical.choice, Quot.sound]
Gate1A.ConditionalClosure.gate1a_fixed_quotient_core            [propext, Classical.choice, Quot.sound]
```

`Gate1A/Status.lean` reproduces these `#check`/`#print axioms` commands
grouped by the status codes PROVED / PROVED_AFTER_REPAIR /
CONDITIONAL_INTERFACE / OPEN_NOT_ASSUMED / RETRACTED.

---

## Scope disclaimer

Nothing here should be used to infer Gate 0, Gate 1B, full Type II,
Hardy–Littlewood, twin primes, or any parity-breaking statement.
