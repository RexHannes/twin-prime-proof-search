# GATE 1B — C4SHIFT LEAFWISE MAJOR / ONE-MINOR SAFE BANK REPORT

Append-only consolidation delta. No historical module was edited or deleted.

New modules:

* `Gate1B/C4ShiftLeafwiseOneMinor.lean`
* `Gate1B/CurrentStatusGate1BC4ShiftLeafwise.lean`
* `Gate1B/AxiomAuditGate1BC4ShiftLeafwise.lean`

---

## 1. FORMALLY PROVED IN LEAN

All statements below are kernel-proved, `sorry`-free, in
`Gate1B/C4ShiftLeafwiseOneMinor.lean`
(namespace `TwinPrimeProject.CurrentProgramme.C4ShiftLeafwise`).

### §B — deterministic major-arc ownership

| declaration | content |
|---|---|
| `farey_separation` | `a₁/q₁ ≠ a₂/q₂` (as `a₁q₂ ≠ a₂q₁`) with `q₁,q₂ > 0` implies `1/(q₁q₂) ≤ |a₁/q₁ − a₂/q₂|`. Exact; no asymptotics. |
| `major_arc_ownership_unique` | If `ω` lies within `1/(2Q₀²)` of two fractions with denominators `≤ Q₀`, then `a₁q₂ = a₂q₁`. Hence **arc ownership is a function of `ω`, not a choice**. |

### §C — character diagonalisation of the major-arc phase

| declaration | content |
|---|---|
| `gaussSumChar` | `G_{q,a}(χ) = ∑_{x ∈ (ZMod q)ˣ} e_q(−a·x) · conj χ(x)`. |
| `conj_char_apply` | On units, `conj χ(x) = χ(x⁻¹)` (via `‖χ(x)‖ = 1`). |
| `major_char_diagonal` | `(1/φ(q)) ∑_χ G_{q,a}(χ) χ(X) χ(Z) = e_q(−a·XZ)` for units `X,Z`. **No primitivity assumption**; conjugations audited. |

The character-orthogonality input is Mathlib's
`DirichletCharacter.sum_char_inv_mul_char_eq`, used under the explicit
hypothesis `[HasEnoughRootsOfUnity ℂ (Monoid.exponent (ZMod q)ˣ)]`.

### §D — unit / non-unit reduction

| declaration | content |
|---|---|
| `nonunit_reduction` | `e_{dq'}(−a·(d·m)) = e_{q'}(−a·m)`, `d ≠ 0`. Exact descent to the reduced modulus. |
| `gcd_partition` | Complete residue sum fibred exactly over `d = gcd(x,q)`, `d ∈ q.divisors`. |

The *analytic* claim that the non-unit cells cost only `log^{O(1)}` is
**research metadata only** and is not formalised.

### §E — multiplicative four-fold factorisation

| declaration | content |
|---|---|
| `char_fourfold_factor` | `χ(x₁x₂x₃x₄) = χ(x₁)χ(x₂)χ(x₃)χ(x₄)`. |
| `fourProduct_2plus2'` | The legal 2+2 grouping, restated from the AP-Fourier layer. |

The **additive** Fourier factorisation refuted earlier
(`C4ShiftAPFourier.c4_additive_factorisation_false`) is **not** revived.

### §F — leafwise source classification with deterministic first defect

| declaration | content |
|---|---|
| `firstDefectIndex` | `i₀(j) = j + 1`. |
| `leaf_five_pure` | `j = 5` is the pure model leaf `λ₁λ₂λ₃λ₄`. |
| `leaf_first_defect` | For `j ≤ 4` the leaf contains `δ_{j+1}` with the explicit residual product. |

### §H — the one-minor projector and the exact `Γ♯` split

| declaration | content |
|---|---|
| `P1m` | `P₁ₘ(ω₁,ω₂) = 1 − M₄(ω₁)M₄(ω₂)`. |
| `P1m_eq_one_iff` | With a `{0,1}`-valued major projector, `P₁ₘ = 1` exactly on the three one-minor cells. |
| `P1m_eq_zero_iff` | `P₁ₘ = 0` exactly on the double-major cell. |
| `GammaOneMinorSharp`, `GammaDoubleMajorSharp` | Sharp sources with the projector inserted **at tuple level**. |
| `gammaSharp_one_minor_split` | `Γ♯ = Γ^{1m,♯} + Γ^{2M,♯}`, a pure linearity identity. |

The routing is inserted at tuple level — a post-summed `Γ` is **never**
multiplied by an `r`-indicator.

### §I — `(h,K)` AP-index normal form on the odd clean sector

| declaration | content |
|---|---|
| `hK_inversion` | `k₁ = v(K+h)`, `k₂ = v(K−h)` when `2v = 1` in `ZMod ℓ`. |
| `apindex_phase_normalform` | `k₁A₁ − k₂A₂ + 2hw = vK(A₁−A₂) + vh(A₁+A₂+4w)`. |
| `full_sum_support` | A non-vanishing complete `ℓ`-sum forces the congruence in its argument. |
| `full_hK_sums_force_A` | `ℓ ∣ A₁−A₂` and `ℓ ∣ A₁+A₂+4w` with `ℓ ∣ 2v−1` force `A₁ ≡ A₂ ≡ −2w (mod ℓ)`. |

Stated for the **unrestricted** sums only. It is **not** claimed that the
restricted one-minor sums collapse. The 2-adic sector is routed separately
(see `C4ShiftNormRepair.hKmap_not_injective_two`).

### §J — `ℓ`-normalisation firewall (restated)

`ell_normalisation_no_saving'` : `ℓ^{-2}·#{(k₁,k₂) mod ℓ} = 1`. No saving is
available from the AP-index normalisation alone.

### Status-layer honesty theorems

`statusRows_no_closed`, `broad_major_tree_match_not_closed`,
`LedgerC4ShiftLeafwise.no_closed_rows`, `ledger_is_honest`, `gate1B_open`,
`parent_open`, `first_analytic_residual`, `parallel_local_residual`,
`previous_layer_preserved`, `analytic_rows_not_kernel_proved` — all kernel
proved.

---

## 2. SOURCE-CONDITIONAL / UNINHABITED

Both structures are declared and **never constructed** anywhere in the
repository.

| socket | intended analytic content |
|---|---|
| `C4ShiftOneMinorPushedEnergyInput` | `∫_θ [ ∑_v \|Ĥ^{1m}(θ,v)\|² ]^{1/2} ≤ naturalBound`, research scaling `Y^{3/4} log^C X`, in the repository's discrete-Haar form. |
| `C4ShiftOneMinorAPIndexRestrictionInput` | the equivalent restricted AP-index estimate `∑_ℓ ℓ^{-2} ∑_{k₁,k₂} ‖restricted‖ ≤ naturalBound`. |

Inherited, still uninhabited from earlier layers:
`C4ShiftQFourierPushforwardInput`, `C4ShiftPushforwardU2TransferInput`,
`TopBandKernelInput`, `BetaU2Input`, `GammaSharpRangeInput`,
`FourProductMinorEnergyInput`, `RatioNoWrapInput`.

---

## 3. RESEARCH-LEVEL STATUS ONLY (not Lean evidence)

* `FOURPRODUCT-POINTWISE-MINOR45` — research PASS / log-corrected; **not false**,
  **not formalised**.
* `C4SHIFT-DEFECT-SMALLMOD-CHAR45` — research pass candidate for nonprincipal;
  principal cell routes to the local profile.
* `C4SHIFT-J5-MAJOR-LOCALMODEL45` — structural pass; physical canonical match
  source open.
* non-unit cells costing only `log^{O(1)}` — research metadata.

---

## 4. SUPERSEDED BUT NOT FALSE

* `DETLINE-ADDMIN-RAMANUJAN-RECIPROCAL-CROSSPAIR45`
* `DETLINE-RAMREC-NEARFULL-RATIO-PHASEGAP45`
* `DETLINE-RAMREC-RATIO-DIAGONAL-DEFECT-BETA45`
* `BETAU2-RECIPROCAL-RESIDUE-RESTRICTION45`
* `C4SHIFT-ONE-FOURPRODUCT-MINOR45` — old research *closure* retracted
  (recorded permanently); the underlying pointwise estimate is **not** marked
  false.

Recorded as an invalid implication (not merely superseded):

* `C4SHIFT-ONE-MINOR-POINTWISE45` / `ONE-FOURPRODUCT-MINOR-NORM-PROMOTION45` —
  the pointwise → `L¹_θ ℓ²_v` promotion is **invalid**
  (`C4ShiftNormRepair.pointwise_substitution_nonclosing`).
* `DOUBLEMAJOR-AS-SOLE-RESIDUAL` — retracted.

---

## 5. CURRENT FIRST RESIDUAL

* **Parent analytic frontier:** `C4SHIFT-QFOURIER-PUSHFORWARD45` — analytic
  open / uninhabited.
* **First exact analytic residual of this delta:**
  `C4SHIFT-ONE-MINOR-PUSHED-ENERGY45` — analytic open / uninhabited.
* **Parallel local residual:** `TOPBAND-BROAD-MAJOR-TREE-MATCH45` — source
  open, not run.

Downstream, all open: `TOPBAND-BETA-BROADMINOR-DETLINE45`,
`TOPBAND-RECURSIVE-MAJOR-TREE-PAIRING45`, `SHIFTED-MAM-TOPBAND45`,
`RANKONE-ENDPOINT-ALLK45`, `PURE5`, `GATE1B`.

---

## 6. TARGETED BUILD RESULTS

| target | result |
|---|---|
| `lake build Gate1B.C4ShiftLeafwiseOneMinor` | **success** (8041 jobs) |
| `lake build Gate1B.CurrentStatusGate1BC4ShiftLeafwise` | **success** (8080 jobs) |
| `lake build Gate1B.AxiomAuditGate1BC4ShiftLeafwise` | **success** (8081 jobs) |

Zero errors, zero warnings on the new modules.

## 7. GLOBAL BUILD RESULT

`lake build` still fails, and fails **only** because of the pre-existing,
unrelated missing module `RequestProject.FixedCertificateAlgebra`
(`error: no such file or directory`). Per the task policy this blocker was
**not** repaired. It is independent of every module in this delta.

## 8. AXIOM AUDIT

`Gate1B/AxiomAuditGate1BC4ShiftLeafwise.lean` runs `#print axioms` on all 33
principal new declarations. Results:

* every declaration reports either *"does not depend on any axioms"* or a
  subset of `[propext, Classical.choice, Quot.sound]`;
* `sorryAx` occurrences in the audit log: **0**;
* no custom axiom, no proof escape.

Token grep over the new files
(`sorry`, `admit`, `axiom`, `opaque`, `unsafe`, `native_decide`,
`implemented_by`) — in `Gate1B/C4ShiftLeafwiseOneMinor.lean`: **no matches**.
The two status/audit modules contain the word `axiom` only inside
`#print axioms` commands and prose, which is the audit mechanism itself.

## 9. COMMIT HASHES

| commit | content |
|---|---|
| `ec112d6` | leafwise major / one-minor exact algebra module |
| (this commit) | status layer, axiom audit, this report |

Earlier layers of the same programme: `be95638`, `22d87d1`, `eb1cb82`,
`b680ce0`, `07ad099`, `b72a53a`, `fd44b02`, `1955443`, `a949d17`.

## 10. PUSH STATUS

All commits pushed to `origin/HEAD`.

---

GATE1B OPEN.

FIRST EXACT ANALYTIC RESIDUAL:
C4SHIFT-ONE-MINOR-PUSHED-ENERGY45.

PARALLEL LOCAL RESIDUAL:
TOPBAND-BROAD-MAJOR-TREE-MATCH45.
