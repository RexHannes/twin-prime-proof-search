# GATE 1B — C4SHIFT CONSOLIDATED SAFE BANK REPORT

Append-only consolidation from the Ramanujan-reciprocal bank through the current
C4Shift `q`-Fourier frontier.  No historical module was edited or deleted.

New modules (all append-only):

| module | phase |
|---|---|
| `Gate1B/RamRecPostReduction.lean` | A — post-Ramanujan exact algebra |
| `Gate1B/RatioDiagonalPhysicalisation.lean` | B — ratio-fibre physicalisation |
| `Gate1B/ALineBetaU2Pushforward.lean` | C — A-line, `(q,v)` pushforward, dual operator |
| `Gate1B/C4ShiftQFourierPushforward.lean` | D — C4Shift Fourier frontier |
| `Gate1B/CurrentStatusGate1BC4Shift.lean` | status layer |
| `Gate1B/AxiomAuditGate1BC4Shift.lean` | axiom audit |

---

## FORMALLY PROVED IN LEAN

All statements below are kernel-proved, `sorry`-free, in the modules above.

### Phase A — `TwinPrimeProject.CurrentProgramme.RamRecPostReduction`

* `coprime_divisor_of_coprime_mul`, `coprime_cofactor_of_coprime_mul` —
  from `N = r n`, `gcd(N,M) = 1` we get `gcd(r,M) = 1` and `gcd(n,M) = 1`.
  **No `gcd(r,n) = 1` hypothesis.**
* `inverse_N_eq_inverse_r_mul_inverse_n_mod_M` — in `ZMod M`,
  `(N : ZMod M)⁻¹ = (r : ZMod M)⁻¹ * (n : ZMod M)⁻¹`.
* `phaseQ`, `phaseChar`, `Phi`, `phase_post_reduction` — the reciprocal phase
  `Φ(m,r,n,x) = m r⁻¹ n⁻¹ / M + x ℓ / r`, represented in the repository's
  additive-character type.
* `phaseChar_eq_iff`, `collision_denominators_eq`,
  `collision_residual_congruences`, `collision_ratio_congruence`,
  `phase_collision_classification` — the exact phase-collision classification:
  equality of characters forces `r₁ = r₂`, `x₁ ≡ x₂ (mod r₁)` and
  `m₁ n₂ ≡ m₂ n₁ (mod M)`.  **The analytic spacing estimate is not imported.**
* `ratioCoord` — the structured ratio coordinate `λ = m n⁻¹ mod M`.
* `ratio_fibre_cauchy` — the fixed-`M` ratio-fibre Cauchy inequality
  `∑_λ |∑_{n ≤ T, m ≡ λ n} b(m,n)|² ≤ T ∑_{m,n} |b(m,n)|²`, under explicit
  finite-support hypotheses.  **Natural scale only; no negative-log saving is
  encoded anywhere.**

### Phase B — `…RatioPhysicalisation`

* `fibre_parametrisation`, `fibre_orthogonality`,
  `fibre_orthogonality_of_not_dvd` — the exact full-fibre Fourier orthogonality
  `∑_{m mod ℓM, m ≡ λn (M)} e_{ℓM}(mz) = ℓ · 1_{ℓ ∣ z} · e_M(λ n (z/ℓ))`, with
  the quotient formed only after divisibility is proved (no ambiguous integer
  division).
* `physical_s_congruence` — `z = 0 mod ℓ` ↔ `N s ≡ −2 (mod ℓ)` for
  `z = s + 2N⁻¹`.
* `exists_K`, `fibre_phase_reduction`, `Rfibre_formula` — the `K = (Ns+2)/ℓ`
  variable (defined only after `ℓ ∣ Ns+2` is proved) and the exact
  `M`-character formula for `R_full(λ)`, conditional on the abstract `ρ` input.
* `Gfibre_hoelder` — the rough λ-Fourier normal form, using the already-banked
  Ramanujan character.
* `sum_lambda_orthogonality`, `shell_congruence` — λ-orthogonality and the
  resulting `ℓ y ≡ N s + 2 (mod M)`.
* `local_coefficient`, `double_divisor_reindex` — the near-full divisor algebra
  `d/N · μ(j) = μ(j)/(n j)` for `d = r/j`, `N = r n`.
* `physical_shell` — the exact physical shell `ℓ y − N s = 2`, conditional on
  the uninhabited no-wrap interface.
* `W_infty_eq_one` — the local weight reassembly
  `∑_{n ∣ N} (1/n) ∑_{j ∣ N/n} μ(j)/j = 1`.
* `W_trunc_error_le` — the exact finite pointwise truncation bound.
* `crosspairD`, `crosspairD_argument_spec` — the physical crosspair normal form
  as a compiler theorem from the exact interfaces (no analytic estimate).

### Phase C — `…ALinePushforward`

* `aline_exists_A0`, `aline_A0_unique` — unique residue `A₀ mod ℓ` solving
  `u s A₀ ≡ −2 (mod ℓ)`.
* `aline_y_param`, `aline_q_param` — `y_t = y₀ + u s t`,
  `q_{t,h} = y₀ + u(st+h)`.
* `ell_y_congr_two_mod_u`, `y_congr_reciprocal`, `yCanon`, `yCanon_congr`,
  `exists_nu`, `q_param_canonical` — the reciprocal residue
  `y ≡ 2 ℓ⁻¹ (mod u)`, the canonical `y_{u,ℓ}` and
  `q_{t,h} = y_{u,ℓ} + u(ν + st + h)`.
* `line_shift` — `q₂ − q₁ = u g` with `g = s r + Δ`.
* `pushforward_dvd`, `pushforward_congr` — `u ∣ v` and `ℓ q ≡ 2 (mod u)`.
* `ell_unique_in_window` — at most one physical `ℓ` in the interval, from an
  explicit finite interval-width hypothesis.
* `fibre_card_le_divisors` — **the fixed `(q,v)` multiplicity is divisor-type**:
  the fibre injects into `{u : u ∣ v, u in the U-range}`.
* `Vsharp_pushforward` — the exact change-of-variables identity.
* `fourier_inversion` — exact finite Fourier inversion for `V♯`.
* `dual_cauchy_interface`, `dual_cauchy_of_betaU2` — the purely functional
  operator inequality, and its conditional consequence.

### Phase D — `…C4ShiftQFourier`

* `eR`, `eR_add`, `eR_conj`, `ezExp_eq_eR`, `eR_add5` — the real-frequency
  additive character and the dictionary to the repository's `ezExp`.
* `sum_indicator_fibre`, `sum_prod5`, `sum5_factor` — exact finite
  reindexing/factorisation lemmas.
* **`GammaTilde_factorisation`** — the load-bearing double-Fourier
  factorisation
  `Γ̃_{u,ℓ}(α,η) = K(α−η) · conj K(−η) · ∑_s e(−α ν_s) C_s(s(α−η)) conj C_s(−sη)`.
  Every sign is kernel-checked.
* `GammaTilde_eq_sum_GammaHat` — recovery of `Γ̃` from `Γ̂` in `η`.
* `Hhat_exact_pushforward` — the exact `Ĥ_j(θ,v)` pushforward formula.
* `topBand_conditional_compiler` — a **conditional** structural compiler only:
  *if* the C4Shift socket and the β-U² input are inhabited, *then* the abstract
  top-band conclusion holds.  Gate1B is **not** closed by it.

---

## SOURCE-CONDITIONAL / UNINHABITED

The following structures are declared and are **never constructed** anywhere in
the repository:

| interface | content |
|---|---|
| `RatioPhysicalisation.RatioPhysicalRangeInput` | physical range `|s| < ℓ` |
| `RatioPhysicalisation.RatioNoWrapInput` | `|k − n j s| < M` |
| `ALinePushforward.BetaU2Input` | β-U² analytic bound |
| `C4ShiftQFourier.TopBandKernelInput` | identification `K = m_top` |
| `C4ShiftQFourier.C4ShiftQFourierPushforwardInput` | `‖Ĥ_j‖_{L¹_θ ℓ²_v} ≤ naturalBound` |
| `C4ShiftQFourier.C4ShiftPushforwardU2TransferInput` | stronger `∑_{q,v}|H|² ≤ naturalSquaredBound` |

---

## RESEARCH-LEVEL STATUS ONLY

Recorded as metadata; **not** formalised, **not** used in any Lean proof:

* large cofactor branch — RESEARCH CLOSED;
* `m_M = 0` cell — RESEARCH POWER CLOSED;
* hybrid `M × r` off-diagonal — RESEARCH POWER CLOSED;
* `t`-diagonal — RESEARCH POWER CLOSED `X^(−1/12+o(1))`;
* small β shift — RESEARCH POWER CLOSED `X^(−5/36+o(1))`;
* research natural bound for the current socket: `Y^(3/4) log^C X`.

---

## SUPERSEDED BUT NOT FALSE

* `DETLINE-ADDMIN-RAMANUJAN-RECIPROCAL-CROSSPAIR45` — superseded as controlling
  frontier; not false (its own historical layer is unchanged).
* `DETLINE-RAMREC-NEARFULL-RATIO-PHASEGAP45` — superseded / strictly reduced.
* `DETLINE-RAMREC-RATIO-DIAGONAL-DEFECT-BETA45` — historical child; superseded /
  strictly reduced.
* `BETAU2-RECIPROCAL-RESIDUE-RESTRICTION45` — strictly reduced.
* old `sqrt(U/R)` incidence tax — superseded as intrinsic obstruction, replaced
  by the divisor-type fibre bound `fibre_card_le_divisors`.

The Lean theorem `LedgerC4Shift.superseded_rows_are_not_false` records formally
that `supersededAsControllingFrontier ≠ falseRoute`.

---

## CURRENT FIRST RESIDUAL

`C4SHIFT-QFOURIER-PUSHFORWARD45` — ANALYTIC OPEN / UNINHABITED.

Stronger sufficient child `C4SHIFT-PUSHFORWARD-U2-TRANSFER45` — ANALYTIC OPEN /
UNINHABITED, explicitly marked *stronger than source-minimal*.

Downstream all OPEN: `TOPBAND-BETA-BROADMINOR-DETLINE45`,
`TOPBAND-RECURSIVE-MAJOR-TREE-PAIRING45`, `TOPBAND-BROAD-MAJOR-TREE-MATCH45`
(NOT RUN / SOURCE OPEN), `SHIFTED-MAM-TOPBAND45`, `RANKONE-ENDPOINT-ALLK45`,
`PURE5`, `GATE1B`.

---

## TARGETED BUILD RESULTS

| target | result |
|---|---|
| `Gate1B.RamRecPostReduction` | success |
| `Gate1B.RatioDiagonalPhysicalisation` | success |
| `Gate1B.ALineBetaU2Pushforward` | success |
| `Gate1B.C4ShiftQFourierPushforward` | success (8038 jobs) |
| `Gate1B.CurrentStatusGate1BC4Shift` | success |
| `Gate1B.AxiomAuditGate1BC4Shift` | success |

## GLOBAL BUILD RESULT

`lake build` still fails **only** because of the known, pre-existing and
unrelated blocker: the missing module `RequestProject.FixedCertificateAlgebra`
(imported by legacy files).  As instructed, it was **not** repaired.  All
targeted builds above are clean.

## AXIOM AUDIT

`Gate1B/AxiomAuditGate1BC4Shift.lean` prints axioms for every principal new
declaration.  Observed axiom sets are only

* `[propext]`,
* `[propext, Quot.sound]`,
* `[propext, Classical.choice, Quot.sound]`.

No `sorryAx`, no custom axiom, no proof escape.

Token scan of the new files (`sorry`, `admit`, `axiom`, `opaque`, `unsafe`,
`native_decide`, `implemented_by`): the only occurrences are inside prose
docstrings describing the safety policy itself; there are no such declarations
or tactics.

## COMMIT HASHES

* `a949d17` — Phase A;
* `1955443` — Phase B;
* `fd44b02` — Phase C;
* `b72a53a` — Phase D;
* status/audit/report commit — see `git log` (appended after this file).

## PUSH STATUS

All commits pushed to `origin`.

---

GATE1B OPEN.

FIRST EXACT RESEARCH RESIDUAL:
C4SHIFT-QFOURIER-PUSHFORWARD45.
