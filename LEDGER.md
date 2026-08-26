# Shifted Möbius Type-II / F3 Master Ledger (consolidated)

**Current final verdict: `RECIPROCAL_TENSOR_PARTIAL_BANKING`.**

The earlier `FULL_UPDATE_BANKED_AND_LEANIFIED` verdict applies only to the prior
F3 routing update summarized below; it is superseded as the project-level verdict
by this conservative Ford/F1/F2 update.

This is a theorem-banking, status-consolidation, dependency-formalization, and
Lean-verification result. It is **not** a new proof of TII-core, full F3, full F1,
F2, balanced Type-II, twin primes, or parity. No parity breakthrough is claimed.

The Lean project builds with **no `sorry`, `admit`, `axiom`, or `implemented_by`**.
All deep analytic inputs are represented by explicit hypotheses / structure fields
(`RequestProject/DependencyInterfaces.lean`, `F1Migration.lean`), never by axioms.

This revision (NANC master update) banks the **fixed-depth F3 routable theorem**,
the **routable-sector F1 migration theorem**, corrects the **full-piece power
saving overclaim** (high-conductor kernel power saving vs full routed piece *log*
saving), and isolates the **two-outer-variable kernel** as the exact next open
input. Earlier conditional statuses on the diagonal / double-cross / KF wedge
remain `SUPERSEDED_BY_LATER_AUDIT`.

---

## 0. Original problem

Let `B(α,β) = Σ_{m∼M} Σ_{n∼N} α_m β_n μ(mn+2)` with `MN ≍ X`,
`X^κ ≤ M,N ≤ X^{1-κ}`, `|α_m| ≤ τ(m)^A`, `|β_n| ≤ τ(n)^A`. Target (open):
`B(α,β) ≪_{A,B,κ} X (log X)^{-B}` (**TII-core**). Exponent notation throughout:
`M = X^μ`, `N = X^{1-μ}`, `Q = X^{1/2+θ}`.

---

## 1. Status taxonomy

`LEAN_PROVED` · `LEAN_PROVED_CORE` (algebraic/modular/parameter core machine-checked,
deep estimate a theorem parameter) · `EXTERNALLY_AUDITED` · `LITERATURE_VERIFIED` ·
`CONDITIONAL_INTERFACE` (derived from an explicit imported interface — a theorem
parameter / structure field, never a global axiom) · `PROVISIONAL_REDUCTION` ·
`OPEN_INPUT` · `REFUTED` · `SUPERSEDED` · `SOURCE_PENDING`.

The Lean mirror of this taxonomy is `ShiftedMobiusBank.ProofStatus` in
`RequestProject/Status.lean`; the machine-readable ledger is
`ShiftedMobiusBank.ledger`.

---

## A. Executive status table

| Label | Status | Latest verdict | Supersedes |
|---|---|---|---|
| `CW_MU_CONDUCTOR_WINDOW_BANKED` | EXTERNALLY_AUDITED | Genuine μ-block window; no all-ones branch | — |
| `F3_R2_BD_REDUCTION` | EXTERNALLY_AUDITED | Reduction to BD-form; signed, factorable, divisor-bounded `λ_q` | — |
| `F3_R2_MAIN_TERM_KILLED` | EXTERNALLY_AUDITED | `Σ_q λ_q MT(q) ≪ X L^{-B}` | `F3_R2_MAIN_TERM_BANKED` |
| `LOW_MID_CONDUCTORS_CONTROLLED` | EXTERNALLY_AUDITED | `r_χ ≤ X^{1/2}L^{-C}` controlled | — |
| `ABSOLUTE_BD_REFUTED` | REFUTED | Never take absolute values in `q` before low-conductor extraction | — |
| `ACTUAL_KF_DIAGONAL_PROVED` | EXTERNALLY_AUDITED | `D_Δ ≪_ε X^{1+ε}` via divisor multiplicity | `ACTUAL_KF_DIAGONAL_PROVISIONAL` (was CONDITIONAL) |
| `ABSTRACT_POISSON_DIAGONAL_FALSE` | REFUTED | Resonant `c_h` breaks abstract Poisson diagonal | `POISSON_DIAGONAL_ABSTRACT_FAILS` |
| `KF_OFFDIAG_CROSSCOPRIME_PROVED` | EXTERNALLY_AUDITED | Bettin–Chandee; power saving when `148μ+158θ<1` | `KF_TINY_OFFDIAG_CROSSCOPRIME_PROVED` |
| `DOUBLE_CROSS_PRIMEPOWER_EXTRACTION` | EXTERNALLY_AUDITED + LEAN_PROVED_CORE | Residual coprimality `(A,Dm₁m₂)=(B,Dm₁m₂)=(s₁,s₂)=1` machine-checked | part of `DOUBLE_CROSS_GCD_PROVISIONAL` |
| `RESIDUAL_COLLAPSE_PROVED` | EXTERNALLY_AUDITED + LEAN_PROVED_CORE | CRT reconstruction of `c mod D` (unique) machine-checked | — |
| `COMPLETE_DOUBLE_CROSS_PHASE_FACTORIZED` | EXTERNALLY_AUDITED | Three-factor phase congruence (§6.3) | — |
| `ONE_MODULUS_FOURIER_SEPARATION` | EXTERNALLY_AUDITED | One multiplicative Fourier expansion mod `K=Dm₂` | — |
| `FOURIER_LOSS_DM_SQRT` | EXTERNALLY_AUDITED | Parseval loss `(DM)^{1/2+o(1)}` | — |
| `FALSE_MPAIR_ONE_OVER_G_REFUTED` | REFUTED | The `1/g` pair count is false; correct count `≪ M²X^ε/(rad s₁·rad s₂)` | — |
| `ACTUAL_KF_TINY_WEDGE_CORRECTED` | EXTERNALLY_AUDITED | `206μ+274θ<1 ⇒ 𝒦 ≪ (X²/N)X^{-η}`; subsumed by widened wedge | `ACTUAL_KF_TINY_WEDGE_PROVISIONAL` |
| `RATIO_SPLIT_WRIGHT_WEDGE_PROVED` | EXTERNALLY_AUDITED | `122μ+162θ<1 ⇒ 𝒦 ≪ (X²/N)X^{-η}` (high-conductor kernel) | `ACTUAL_KF_TINY_WEDGE_CORRECTED` |
| `ACTUAL_KF_WEDGE_122_162` | EXTERNALLY_AUDITED | The widened wedge inequality itself | — |
| `F3_R2_HIGH_CONDUCTOR_POWER_SAVING` | EXTERNALLY_AUDITED | r=2 high-conductor kernel `≪ X^{1-η}` | — |
| `F3_R2_PARTIALLY_KILLED_WIDENED` | EXTERNALLY_AUDITED | `𝒫_{d₂} ≪ X^{1-η/2+o(1)}` (high-conductor component) | `F3_R2_PARTIALLY_KILLED` |
| **`F3_FIXED_DEPTH_ROUTABLE_SECTOR_PROVED`** | **EXTERNALLY_AUDITED + LEAN_PROVED_CORE** | For fixed `r`, admissible Möbius block + routable smooth block ⇒ `𝒫_r ≪ X(log X)^{-B}`; high-conductor component has power saving | `F3_FIXED_DEPTH_ROUTING` (was OPEN) |
| `HIGH_CONDUCTOR_COMPONENT_POWER_SAVING` | EXTERNALLY_AUDITED | high-conductor component `≪ X^{1-η}` | — |
| `FULL_ROUTED_PIECE_LOG_SAVING` | EXTERNALLY_AUDITED | complete routed piece `≪ X(log X)^{-B}` (log saving only) | — |
| `FULL_ROUTED_PIECE_POWER_SAVING_REFUTED_AS_STATED` | REFUTED | The whole routed piece does **not** enjoy fixed power saving as earlier stated | — |
| `GLOBAL_ORIENTATION_WRIGHT_WIDENING_FAILED` | REFUTED | Global-orientation Wright widening blocked (ratio-split orientation used instead) | — |
| `MESOSCOPIC_MOBIUS_LEMMA_ADMISSIBLE_Q` | EXTERNALLY_AUDITED | Cancellation for admissible `q` above `Y_mes = exp(C·L₂^{5/3}L₃^{1/3})` | — |
| `UNRESTRICTED_Q_MESOSCOPIC_FALSE` | REFUTED | Primorial modulus leaves prime sum `≍ 1/log Y` | — |
| **`LONG_MOBIUS_F1_MIGRATION_ROUTABLE_PROVED`** | **EXTERNALLY_AUDITED + LEAN_PROVED_CORE** | Routable long-Möbius F1 piece migrates into fixed-depth F3 ⇒ `𝓕 ≪ X(log X)^{-B}` | `LONG_MOBIUS_F1_MIGRATION_THEOREM` (was OPEN) |
| `MESOSCOPIC_LEMMA_ALONE_DOES_NOT_SOLVE_F1` | REFUTED | The analytic mesoscopic lemma alone does not solve F1 | — |
| `FULL_F1_MIGRATION_OPEN` | OPEN_INPUT | Premise "all long-Möbius F1 pieces migrate" not proved | — |
| `F1_ULTRASHORT_CORE_REDUCTION` | PROVISIONAL_REDUCTION | Not banked as proved | — |
| `F1_ULTRASHORT_AGGREGATE_MAIN_TERM` / `_OFFDIAGONAL` | OPEN_INPUT | — | — |
| **`TWO_OUTER_VARIABLE_F3_KERNEL`** | **OPEN_INPUT** | Exact next wall: `𝒫^{(2)} = Σ_q λ_q Σ α_m β_n Δ_{W₁,W₂}((mn+2)/q)` | — |
| `F3_SINGLE_OUTER_UNROUTABLE_CORE` | OPEN_INPUT | Fragments with `w_i ≤ w*(μ)` for every smooth block (e.g. balanced `X^{1/3}` triple) | — |
| `HYBRID_MQ_KLOOSTERMAN_LARGE_SIEVE` | OPEN_INPUT | Coupled hybrid m-q Kloosterman/large-sieve; F2/balanced endpoint | — |
| `BALANCED_TII_CORE` | OPEN_INPUT | — | — |
| `PARITY_OPEN` | OPEN_INPUT | — | — |

### Machine-checked (LEAN_PROVED) algebra/parameter/routing theorems (this project)

| Lean theorem | File | Content |
|---|---|---|
| `wedge_containment_206_implies_122` | `Wedge122162.lean` | §13.2 old wedge ⊂ new wedge (converse not stated) |
| `splitting_parameter_122_162`, `fixed_factor_identity/le` | `Wedge122162.lean` | §12.2/§13.3 full σ chain, `2σ+2μ ≤ 1/5` |
| `oldWedge_sigma_feasible_iff` | `Wedge206274.lean` | old splitting parameter feasibility (preserved) |
| `wright_term_one/two`, `wright_cube/seventh_mono` | `WrightExponentAudit.lean` | §12.4 Wright rpow inequalities |
| `sectors_exhaustive`, `sector_partition_exhaustive_disjoint` | `SectorPartition.lean` | exhaustive+disjoint sector partition |
| `double_cross_residual_coprime`, `crt_residual_collapse_core` | `DoubleCrossArithmetic.lean` | §6/§13 residual coprimality + CRT collapse |
| `mesoscopic_finite_product_bound` | `MesoscopicParameters.lean` | §13.6 `∏ Yᵢ ≤ Y_mes^K` |
| **`routing_threshold_equiv`, `newWedge_iff_wStar`, `wStar_mono`** | `RoutingThreshold.lean` | §13.1 `122μ+162(½−w)<1 ⟺ w > w*(μ)=(40+61μ)/81` |
| **`maj_mul`, `maj_finset_prod`, `maj_fixed_depth`** | `FixedDepthConvolution.lean` | §13.4 discrete coefficient-majorant; fixed-depth divisor bound `τ^{depth}` |
| **`routing_reindex`, `routing_reindex_apply`, `routedCoeff_divBounded`** | `FixedDepthRouting.lean` | §13.5 exact routing reindexing `γ·∏ψ = λ^{(j)}·ψ_j`; `|λ^{(j)}| ≤ τ^r` |
| **`long_mobius_f1_migration_routable`, `ultrashort_product_bound`, `F1RoutableHyp.wedge_holds`** | `F1Migration.lean` | §7/§13.6 routable F1 migration interface; ultra-short product |
| **`f3_fixed_depth_kernel_power_saving`, `f3_fixed_depth_routable_full_piece`** | `DependencyInterfaces.lean` | §14 routed-F3 interface, kernel vs full-piece split |
| **`status_distinctions_consistent`** | `DependencyInterfaces.lean` | §13.7 routable ⇸ full (dependency distinction) |
| `ratio_split_wright_wedge`, `mesoscopic_mobius_admissible` | `DependencyInterfaces.lean` | §8.5/§9 conditional interfaces (admissible-`q` only) |

---

## B. Theorem-strength distinction (§4 correction — must be honest)

* **High-conductor component** (under `122μ+162θ<1`): the *conductor-extracted
  high-conductor kernel* has **power saving**, `≪ X^{1-η}`
  (`HIGH_CONDUCTOR_COMPONENT_POWER_SAVING`, Lean field
  `RoutedF3Interface.kernelPowerSaving`).
* **Complete routed piece** (after adding main term, low, and middle conductors,
  and the conductor-window branch): only **log saving**, `≪ X(log X)^{-B}`
  (`FULL_ROUTED_PIECE_LOG_SAVING`, Lean field
  `RoutedF3Interface.fullPieceLogSaving`).
* Any earlier unqualified statement `𝒫_r ≪ X^{1-η}` for the *whole* mesoscopic
  routed piece is `FULL_ROUTED_PIECE_POWER_SAVING_REFUTED_AS_STATED`.

In Lean the two are **separate structure fields** with separate providers; there is
deliberately **no** provider `kernelPowerSaving → fullPieceLogSaving`, so
high-conductor power saving does not automatically imply full-piece power saving.
This correction does not weaken TII-core, which requires arbitrary log saving.

---

## C. Current routable threshold (§6, §13.1)

Selecting a smooth block `W_j = X^{w_j+o(1)}` gives residual conductor
`Q_j = X/W_j = X^{1/2+θ_j}`, `θ_j = 1/2 − w_j`. Then
```
122μ + 162θ_j < 1   ⟺   w_j > w*(μ),   w*(μ) = (40 + 61μ)/81.
```
Machine-checked as `routing_threshold_equiv`. Endpoint qualification:
* `Q_j > X^{1/2}` (i.e. `w_j < 1/2`): ratio-split Wright theorem;
* `Q_j < X^{1/2}` by a fixed power (`w_j > 1/2`): conductor-window theorem;
* exact no-margin square-root endpoint is separately classified.

At `μ = 0`, `w*(0) = 40/81 < 1/2` (`wStar_zero_lt_half`).

## D. Unroutable examples (`OPEN`)

A fixed-depth fragment is **single-block-unroutable** if `w_i ≤ w*(μ)` for every
smooth residual block. Balanced example: `W₁,W₂,W₃ ≍ X^{1/3}` is unroutable for
small `μ` (since `1/3 < 40/81 = w*(0)`). Recorded as
`F3_SINGLE_OUTER_UNROUTABLE_CORE` (OPEN_INPUT).

## E. F1 partial migration theorem (§7, §8)

`LONG_MOBIUS_F1_MIGRATION_ROUTABLE_PROVED`: if an F1 piece has (1) one Möbius block
with `Y_i ≥ Y_mes` and (2) one smooth block with `w > w*(μ)+δ`, it routes into the
fixed-depth F3 theorem and satisfies `𝓕 ≪ X(log X)^{-B}`. The Möbius cancellation
is used exactly once, before any destructive absolute value; no nonprincipal
character acts on the Möbius block. Lean: `long_mobius_f1_migration_routable`
(the routing hypothesis `w > w*(μ)+δ` forces the wedge via
`F1RoutableHyp.wedge_holds`). **Not** banked: `F1_ULTRASHORT_CORE_REDUCTION_PROVED`;
`FULL_F1_MIGRATION_OPEN` remains open (premise "all pieces migrate" unproved).

## F. Exact next analytic wall (§9)

`TWO_OUTER_VARIABLE_F3_KERNEL` (OPEN_INPUT). With
`Δ_{W₁,W₂}(r) = Σ_{ab=r} ψ₁(a/W₁)ψ₂(b/W₂)`, the next target is
```
𝒫^{(2)} = Σ_q λ_q Σ_{m∼M,n∼N, mn≡−2 (q)} α_m β_n Δ_{W₁,W₂}((mn+2)/q).
```
This is the exact missing theorem for (1) balanced fixed-depth fragments,
(2) unroutable long-Möbius F1 pieces, (3) a larger part of full F3. It is **not**
the balanced F2 hybrid m-q kernel.

---

## G. Dependency DAG

```text
ratio-split Wright kernel (122μ+162θ<1)
  → r=2 high-conductor power saving          [F3_R2_HIGH_CONDUCTOR_POWER_SAVING]
  → fixed-depth single-outer high-conductor transfer
  → fixed-depth routable full-piece log saving  [F3_FIXED_DEPTH_ROUTABLE_SECTOR_PROVED]
  → routable long-Möbius F1 migration        [LONG_MOBIUS_F1_MIGRATION_ROUTABLE_PROVED]

two-outer-variable kernel [OPEN]             [TWO_OUTER_VARIABLE_F3_KERNEL]
  → balanced/unroutable fixed-depth F3
  → unroutable long-Möbius F1 migration
  → larger full-F3 sector

hybrid m-q kernel [OPEN]                      [HYBRID_MQ_KLOOSTERMAN_LARGE_SIEVE]
  → F2 endpoint
  → balanced TII
  → parity
```
A Mermaid version is in `DEPENDENCY_GRAPH.md`.

## H. Refuted / corrected statements

1. `ABSOLUTE_BD_REFUTED`;
2. `ABSTRACT_POISSON_DIAGONAL_FALSE`;
3. `FALSE_MPAIR_ONE_OVER_G_REFUTED`;
4. `UNRESTRICTED_Q_MESOSCOPIC_FALSE`;
5. `GLOBAL_ORIENTATION_WRIGHT_WIDENING_FAILED`;
6. `FULL_ROUTED_PIECE_POWER_SAVING_REFUTED_AS_STATED`;
7. `MESOSCOPIC_LEMMA_ALONE_DOES_NOT_SOLVE_F1`.

## I. Superseded prior conclusions (`SUPERSEDED_BY_LATER_AUDIT`)

* diagonal / double-cross / KF wedge "CONDITIONAL" → now audited/proved-core
  (`ACTUAL_KF_DIAGONAL_PROVED`, `DOUBLE_CROSS_PRIMEPOWER_EXTRACTION` +
  `RESIDUAL_COLLAPSE_PROVED`, `RATIO_SPLIT_WRIGHT_WEDGE_PROVED`);
* `F3_R2_PARTIALLY_KILLED` not-claimed → `F3_R2_PARTIALLY_KILLED_WIDENED`;
* `F3_FIXED_DEPTH_ROUTING` OPEN → `F3_FIXED_DEPTH_ROUTABLE_SECTOR_PROVED`;
* `LONG_MOBIUS_F1_MIGRATION_THEOREM` OPEN → `LONG_MOBIUS_F1_MIGRATION_ROUTABLE_PROVED`.
The historical Lean interface layer is preserved in `Banking.lean` under
`namespace Superseded`.

---

## J. Final ledger

* **Current strongest safe (Lean-proved-core + externally-audited) theorem:**
  `F3_FIXED_DEPTH_ROUTABLE_SECTOR_PROVED` — for fixed `r`, an admissible Möbius
  block plus a routable smooth block (`w > w*(μ)`) gives `𝒫_r ≪ X(log X)^{-B}`,
  with power saving in the high-conductor component. Its routing threshold,
  reindexing, divisor-bound, and full-vs-kernel distinction are machine-checked.
* **Strongest fully Lean-proved content:** parameter/wedge algebra, routing
  threshold equivalence, fixed-depth convolution coefficient-majorant + divisor
  bound, exact routing reindexing, Wright exponents, sector partition, double-cross
  residual coprimality + CRT collapse, finite-product bound, and the honest
  status distinctions (`status_distinctions_consistent`).
* **Exact next open frontier:** `TWO_OUTER_VARIABLE_F3_KERNEL`. Also open:
  `F3_SINGLE_OUTER_UNROUTABLE_CORE`, `FULL_F1_MIGRATION_OPEN`,
  `HYBRID_MQ_KLOOSTERMAN_LARGE_SIEVE`, `BALANCED_TII_CORE`, `PARITY_OPEN`. No
  parity breakthrough is claimed.

---

# Ford / F1 Centering / F2 Double-Mellin Conservative Update

## 1. Executive summary

This update adds machine-checked finite cores for the outer hierarchy, F1 global
centering, complex Dirichlet-character orthogonality, and reciprocal-tensor
exponent arithmetic. The supplied materials do **not** contain the promised exact
Sol/Fable corrections or source locations. Consequently, no Ford positivity
statement, exact F2 double-Mellin formula, principal-sector result, structured RCT
subcase, or RCT large sieve is promoted beyond its evidenced status.

## 2. Files modified

New Lean modules: `FordMaynardInterface.lean`, `OuterHierarchyArithmetic.lean`,
`F1GlobalCentering.lean`, `CharacterExpansion.lean`,
`F2DoubleMellinStatus.lean`, `ReciprocalTensorExponents.lean`,
`F2SectorLedger.lean`, and `FullTypeIIStatus.lean`. Updated `Banking.lean`,
`Status.lean`, `LEDGER.md`, and `DEPENDENCY_GRAPH.md`.

## 3. Build result

The complete project builds successfully (`8049` jobs). The outer-average proof
is included, and the Lean sources contain no proof placeholders or global analytic
axioms. Representative axiom checks are recorded in the final verification.

## 4. Ford interface

`FORD_MAYNARD_POSITIVITY_INTERFACE`: **SOURCE_PENDING** for the literature
statement. The task text supplies neither the exact definitions of
`γ, θ, ν, C⁻(γ,θ,ν)` nor exact source locations, so recording invented formulas as
`LITERATURE_VERIFIED` would be an unsafe upgrade. The six project conditions
(Type I, uniform Type II, comparison sequence, local densities, fixed shift, and
arbitrary divisor-bounded rank-one coefficients) are separately encoded by
`FordProjectTransferenceConditions`; the assembly theorem is only a
**CONDITIONAL_INTERFACE**.

## 5. Outer hierarchy

`OUTER_BLOCK_AVERAGE_LEMMA`: **LEAN_PROVED**. For antitone weights on `Fin d`
with total sum one, the first `k` weights sum to at least `k/d`.
`kMin d w* = ⌊d w*⌋₊+1` and its minimality are machine-checked.
`w*(μ)=(40+61μ)/81` is encoded over `ℚ`, including `81w*=40+61μ`.
`FINITE_OUTER_LEVEL_ARITHMETIC`: **LEAN_PROVED_CORE**; no Ford-specific numerical
`μ` was supplied, so no numerical level table is fabricated.

## 6. F1 centering

`F1_GLOBAL_CENTERING_IDENTITY`: **LEAN_PROVED_CORE**. For a finite family
`piece_P = MT_P + OD_P`, with `a=Σ piece_P`, `b=Σ MT_P`, and `w=a-b`, Lean proves
`w=Σ OD_P`.

## 7. Comparison-sequence status

`F1_COMPARISON_SEQUENCE_AXIOMS`: **OPEN_INPUT**. Positivity, total mass, local
densities, prime sum, and independence from test coefficients have not been
supplied as verified results.

## 8. Finite character identity

The complete Gauss-sum identity is **EXTERNALLY_AUDITED** only at the prose level.
Its exact finite orthogonality core is **LEAN_PROVED_CORE** using complex
Dirichlet characters:
`Σχ χ(a) = φ(p)` for `a=1`, otherwise zero, and
`Σχ χ(a⁻¹)χ(b) = φ(p)` for unit `a=b`, otherwise zero.
No global axiom is introduced.

## 9. Double-Mellin formula

`F2_DOUBLE_MELLIN_PRIME_UNIT`: **SOURCE_PENDING**. The exact “Sol-corrected
prime/unit formula” is absent from the supplied project and prompt. Lean therefore
contains only an explicit conditional reduction interface, not a fabricated
formula and not Full F2.

## 10. Excluded strata

Recorded separately in `F2ExcludedStrata`: principal characters, nonunits,
`p=r`, prime powers, repeated primes, and gcd strata. None is silently included
in the prime/unit NN interface.

## 11. Moment interfaces

The analytic moment estimates `Σ|A_p(χ)|² ≪ R^(3+ε)` and
`Σ|C_{p,r}(χ,ψ)|² ≪ R^(5+ε)` remain external inputs. Lean banks only their exact
exponent consequence.

## 12. R^(9/2) derivation

`NAIVE_RECIPROCAL_TENSOR_EXPONENT`: **LEAN_PROVED_CORE**:
`-1 + 3 + 5/2 = 9/2` over `ℚ`.

## 13. R^(3/2) gap

`RECIPROCAL_TENSOR_GAP_THREE_HALVES`: **LEAN_PROVED**:
`9/2 - 3 = 3/2` over `ℚ`.

## 14. Principal-sector ledger

| Node | Status |
|---|---|
| `F2_PP_MAIN` | SOURCE_PENDING |
| `F2_PN_SINGLE_SPECTRAL` | SOURCE_PENDING |
| `F2_NP_SINGLE_SPECTRAL` | SOURCE_PENDING |
| `F2_NN_RECIPROCAL_TENSOR` | OPEN_INPUT |

The PP/PN/NP premises are explicit and separate from NN in Lean.

## 15. RCT status

`RECIPROCAL_CHARACTER_TENSOR_LARGE_SIEVE`: **OPEN_INPUT**. No corrected theorem
statement, Fable proof, Sol verification, or countermodel was included. Required
arrows are retained: RCT → prime/unit F2 NN → composite/gcd reassembly → Full F2.

## 16. Structured subcases

Smooth `α`, smooth `c_h`, prime modulus, semiprime modulus, quadratic characters,
averaged shift, and well-factorable `λ` are all **SOURCE_PENDING** because no
Fable statuses were supplied. `StructuredTensorSubcase` records, for each future
result, whether it preserves fixed shift, arbitrary coefficients, rank one, and
composite moduli. Its Boolean `fordReady` requires all four flags and theorem
availability; none is currently labelled Ford-ready.

## 17. F1/F2/F3 dependency graph

```text
F1 global centering [LEAN_PROVED_CORE]
  -> comparison-sequence axioms [OPEN_INPUT]
  -> F1 aggregate off-diagonal [OPEN_INPUT]
       -> RCT / F3 operators [OPEN_INPUT / partial bank]

F2 prime/unit double Mellin [SOURCE_PENDING]
  -> PP/PN/NP reassembly [SOURCE_PENDING]
  -> NN RCT [OPEN_INPUT]
  -> nonunit/composite/gcd strata [OPEN_INPUT]
  -> Full F2 [OPEN_INPUT]

F3 one-outer routable [EXTERNALLY_AUDITED + LEAN_PROVED_CORE]
  -> two-outer [OPEN_INPUT]
  -> three-outer [SOURCE_PENDING]
  -> four-outer [SOURCE_PENDING]
  -> conductor/composite/gcd reassembly [OPEN_INPUT]
  -> Full F3 [OPEN_INPUT]

Full F1 + Full F2 + Full F3
  -> uniform project Type II [OPEN_INPUT]
  -> Ford transference [CONDITIONAL_INTERFACE]
  -> positivity gate [SOURCE_PENDING]
```

## 18. Strongest banked theorem

For this update, the strongest complete new theorem is
`OUTER_BLOCK_AVERAGE_LEMMA`; the strongest new decomposition core is
`F1_GLOBAL_CENTERING_IDENTITY`. The prior project's strongest analytic bank,
`F3_FIXED_DEPTH_ROUTABLE_SECTOR_PROVED`, remains externally audited with
Lean-proved routing cores.

## 19. Exact open frontier

The immediate documentation frontier is receipt of the exact Sol-verified Ford
definitions/source locations and corrected prime/unit double-Mellin formula, plus
Fable/Sol statuses for RCT and structured subcases. The mathematical frontier is
`RECIPROCAL_CHARACTER_TENSOR_LARGE_SIEVE`, followed by composite/nonunit/gcd
reassembly; comparison-sequence axioms and the two-outer F3 kernel remain open.

## 20. Explicit nonclaims

No claim is made of Full F1, Full F2, Full F3, full Type II, Ford–Maynard
positivity, parity breaking, twin primes, or Hardy–Littlewood. The shifted Möbius
Type-II object is not identified with Ford's hypothesis. No structured result is
called Ford-ready.

## 21. Final verdict

`RECIPROCAL_TENSOR_PARTIAL_BANKING`

---

# Residue-Aware Twin-Prime Comparison Model — Conservative Ledger

## Executive status table

| Component | Status |
|---|---|
| Definitions (`a`, `P₀`, `V₀`, residue-aware `b`, `w`) | `LEAN_PROVED_CORE` |
| Nonnegativity, support, parity vanishing | `LEAN_PROVED` |
| Mertens-dependent pointwise estimate | `CONDITIONAL_INTERFACE` |
| Exact local congruence branches | `LEAN_PROVED` |
| Finite local density algebra and hostile local cases | `LEAN_PROVED` |
| Totient factor split | `CONDITIONAL_INTERFACE` |
| Large-prime divisor count and reciprocal tail | `LEAN_PROVED` |
| Finite twin-prime Euler product | `LEAN_PROVED` |
| Infinite-product convergence | `OPEN_INPUT` |
| Exact weighted twin-count decomposition | `CONDITIONAL_INTERFACE` |
| Prime-power contamination estimate | `OPEN_INPUT` |
| Exact K=3 Heath–Brown source/range | `SOURCE_PENDING` |
| Prime mass, Ford (b.1), Ford (b.2), Type I, transference | `OPEN_INPUT` |
| Centered shifted-prime Type II and global centering | `OPEN_INPUT` |
| Old constant comparison model | `REFUTED` |
| Claimed shifted-Möbius/Ford-Type-II identification | `SUPERSEDED` |

`V0 z` is defined with the mandatory factor `1/2`.  No interval asymptotic is
inferred from the finite local-density identity.

## Dependency DAG

```text
Weighted twin-prime detector a_n
  -> weighted/unweighted counting relation

Residue-aware candidate b_n
  -> elementary properties [LEAN_PROVED]
  -> local congruence rules [LEAN_PROVED]
  -> finite local-density factor [LEAN_PROVED]
  -> large-prime tail [LEAN_PROVED]
  -> finite twin-prime Euler product [LEAN_PROVED]

Residue-aware candidate b_n
  -> prime mass [OPEN_INPUT]
  -> Ford (b.1) [OPEN_INPUT]
  -> Ford (b.2) [OPEN_INPUT]
  -> Ford Type I [OPEN_INPUT]
  -> Ford transference [OPEN_INPUT]

a_n - b_n
  -> exact HB/sieve global centering [OPEN_INPUT]
  -> centered shifted-prime Type II [OPEN_INPUT]
  -> Ford–Maynard positivity [CONDITIONAL_INTERFACE]
  -> twin-prime lower bound [CONDITIONAL_INTERFACE]

Old constant b_n
  -> REFUTED

Shifted Möbius object
  -> independent research programme
  -> not presently connected to Ford Type II
```

## Exact frontier and nonclaims

The frontier is analytic: prime mass, Ford (b.1)/(b.2), Type I, centered Type II,
global centering, transference, infinite-product convergence, and the exact sourced
K=3 Heath–Brown identity.  Nothing in this ledger proves Ford applicability,
Ford Type I or II, Full F1/F2/F3, parity breaking, twin-prime infinitude, or
Hardy–Littlewood.  The residue-aware candidate is not called a Ford comparison
sequence.

---

# Residue-Aware Ford Type-I Delta Update

## Status promotion

`RESIDUE_AWARE_FORD_TYPE_I` is promoted from `OPEN_INPUT` to
`EXTERNALLY_AUDITED`, with secondary label `PROVED_MODULO_CLASSICAL_BV`.
The exact audited range is every fixed exponent `γ < 1/2`: for fixed
`A,B ≥ 0` and `0 < ε < 1/2`, the divisor-weighted maximal interval discrepancy
for `w_{mn}=a_{mn}-b_{mn}`, summed over `m ≤ x^(1/2-ε)`, is
`O_{A,B,ε}(x (log x)^(-B))`. This is an externally audited analytic theorem,
not a Lean-kernel proof. The clean endpoint `γ=1/2` remains
`FORD_TYPE_I_EXACT_HALF_ENDPOINT — OPEN_INPUT`.

## Type-I component ledger

| Component | Status |
|---|---|
| finite local-density core | `LEAN_PROVED` (preserved) |
| `DIVISOR_WEIGHTED_MAXIMAL_BV` | `EXTERNALLY_AUDITED` |
| `INTERVAL_UNIFORM_RESIDUE_SIEVE` | `EXTERNALLY_AUDITED` |
| `TYPE_I_LARGE_PRIME_TAIL` | `EXTERNALLY_AUDITED` |
| `TYPE_I_EVEN_MODULUS_BRANCH` | `EXTERNALLY_AUDITED` |
| `RESIDUE_AWARE_FORD_TYPE_I` | `EXTERNALLY_AUDITED` |
| `FORD_TYPE_I_EXACT_HALF_ENDPOINT` | `OPEN_INPUT` |

The maximal-BV component uses classical maximal-prefix/maximal-residue
Bombieri--Vinogradov, divisor moments, Cauchy--Schwarz, and a harmless
polylogarithmic pointwise majorant. The interval sieve uses the dimension-one
fundamental lemma at level `(x/m)^(1/3)`, uniformly for integer intervals. The
large-prime component matches `m/φ(m)` to the finite local product and uses the
already kernel-proved reciprocal-tail lemmas. The even-modulus branch reduces to
shifted powers of two. Endpoint and support bookkeeping complete the externally
audited assembly.

## Updated dependency graph

```text
TYPE I
  ├── finite local-density core                  LEAN_PROVED
  ├── divisor-weighted maximal BV                EXTERNALLY_AUDITED
  ├── interval-uniform rough sieve               EXTERNALLY_AUDITED
  ├── large-prime tail matching                  EXTERNALLY_AUDITED
  ├── even-modulus branch                        EXTERNALLY_AUDITED
  └── residue-aware Ford Type I                  EXTERNALLY_AUDITED
        range: m <= x^(1/2-epsilon)

SPARSE TWIN BOUNDARY TRANSFER
  ├── comparison / b.1 / b.2                     unchanged
  ├── sparse boundary a and b                    unchanged
  ├── Type I                                     DISCHARGED / EXTERNALLY_AUDITED
  ├── Type II                                    OPEN_INPUT
  └── Ford source/transference bridge            CONDITIONAL_INTERFACE

CURRENT BINDING ANALYTIC GATE
  └── arbitrary-coefficient centered Ford Type II

NOT CURRENTLY BINDING
  └── Type I
```

No status is changed here for arbitrary-coefficient Ford Type II, centered
shifted-prime Type II, global centering, Full F1/F2/F3, RCT, parity, twin-prime
infinitude, a correct-order twin lower bound, or Hardy--Littlewood.

---

# Fable Perfect-Power Reduction Bank Update

## A. Executive summary

The exact fixed-application perfect-power support and a finite elementary
counting core are now formalized.  The assembled analytic leakage closure remains
a proof-carrying conditional interface with status
`FABLE_DERIVED_PENDING_FORMAL_AUDIT`.  No `r_h = 1` census, Type II theorem, or
twin-prime result is claimed.

A parameter audit found one source error: under the stated range
`0 < ε ≤ ν₀/100`, the claim `3/σ+2 ≤ 20` is false at the upper endpoint. Lean
proves the counterstatement and the corrected uniform bound `3/σ+2 ≤ 21`.

## B. Existing project preserved

Existing declarations, statuses, local-density and comparison-sequence results,
externally audited residue-aware Type I interface, dependency records, and trust
interfaces are preserved. `ARISTOTLE_SUMMARY.md` was read and not edited.

## C. True parameter bank

With `ν₀ = 1663/10000`, `γ = 1/2-ε`, and `σ = ν₀-2ε`, Lean proves for
`0 < ε ≤ ν₀/100`:

- `ν₀ > 0`;
- `J = 2⌈1/(1-γ)⌉ = 4`;
- `ℓ = 3J = 12`;
- `⌊1/σ⌋ = 6`, hence a source-supplied `k ≤ ⌊1/σ⌋` gives `k ≤ 6`.

The requested `3/σ+2 ≤ 20` is not a true parameter and was not banked. At
`ε=ν₀/100` it fails; the corrected uniform rational bound is `≤ 21`.

## D. Fixed/universal ledger separation

`ApplicationLedger`, `FixedApplicationLedgerData`, and
`UniversalMajorantLedgerData` distinguish exact fixed-source data from terms
created by removing the fixed condition, freeing power relations, replacing
exact factors, and applying triangle majorants. A universal-majorant term is not
a binding fixed-application core.

## E. Perfect-power support formalisation

`PerfectPowerBranchSupport` explicitly carries `r≥2`, `c≥1`, `m_h=c^r`,
`m_h∣n`, `(X/2)^σ<m_h`, and `X/2<n≤X`. It has no global inhabitant. Status:
`PROVED_MODULO_SUPPLIED_SOURCE` pending extraction from exact source branches.

## F. Perfect-power counting core

`fixedExponentDivisorMass X T r = Σ_{T<c≤X} ⌊X/c^r⌋` is formalized. Lean proves:

- domination by the square exponent for every `r≥2`;
- the explicit square-tail bound `mass ≤ X/T` for `T≠0`;
- the same bound for every fixed `r≥2`;
- summation through exponent `R` costs at most `R-1`.

These are `LEAN_PROVED` finite inequalities and encode the elementary
`X^{1-σ/2}` saving after an appropriate threshold is supplied. A separate
optional divisor-weighted asymptotic is not claimed.

## G. Branch coefficient and multiplicity records

The following are separate proof-bearing structures, not one opaque premise:
`HBBranchCoefficientBound`, `BranchFactorisationMultiplicity`,
`CenteredWeightCrudeBound`, `CertificateDivisorBound`, and
`NormalizedLogCoefficientBound`. Their concrete analytic bounds are
`CONDITIONAL_INTERFACE` inputs.

## H. Assembled (r_h≥2) closure status

`RGeTwoFixedApplicationClosureInput` visibly contains perfect-power support,
all five coefficient/multiplicity packages, the exact leakage proposition, and
its proof. `R_GE_TWO_FIXED_APPLICATION_CLOSURE` is a transparent accessor.
Status: `FABLE_DERIVED_PENDING_FORMAL_AUDIT`, and more precisely
`CONDITIONAL_INTERFACE` as currently implemented. It is not promoted merely
from the Fable argument.

## I. Negative status corrections

- `M0`: `REJECTED_AS_UNIVERSALISATION_SURROGATE`; the exact complementary side
  retains mandatory logarithmic, Möbius, canonical, and fixed-application data.
- `C2_MIN`: `REJECTED_AS_MINIMAL_FIXED_APPLICATION_CORE`; its `k=1` form omits
  the required nontrivial `u/v` factor.
- `CU_NO_WINDOW_SUBSET`: `FALSE_BY_SOURCE_GEOMETRY`; exact leakage branches have
  a qualifying Type-II subset.

## J. (r_h=1) status

`R1_PATTERN_SKELETON` remains `PARTIAL` and `R1_EXACT_BINDING_CLASS` remains
`OPEN_INPUT`. No complete census or exact minimal binding core is recorded.

## K. Updated dependency graph

```text
FIXED-APPLICATION LEAKAGE
  ├── residue-aware Ford Type I                 EXTERNALLY_AUDITED
  ├── r_h >= 2 perfect-power branches           FABLE_DERIVED_PENDING_FORMAL_AUDIT
  │     ├── perfect-power branch support         PROVED_MODULO_SUPPLIED_SOURCE
  │     ├── finite perfect-power divisor count   LEAN_PROVED
  │     ├── branch multiplicity/bounds           CONDITIONAL_INTERFACE
  │     └── assembled closure                    CONDITIONAL_INTERFACE
  └── r_h = 1 branches                           OPEN
        ├── pattern skeleton                     PARTIAL
        ├── M0                                   REJECTED_AS_UNIVERSALISATION_SURROGATE
        ├── C2_MIN                               REJECTED_AS_MINIMAL_FIXED_APPLICATION_CORE
        └── exact binding cancellation class     OPEN_INPUT

UNIVERSAL FORD TYPE II                           OPEN_INPUT
```

## L. Files created or modified

- Created `RequestProject/PerfectPowerReduction.lean`.
- Modified `RequestProject/TwinPrimeBanking.lean` to export the module.
- Appended this update to `LEDGER.md`.
- Did not modify `ARISTOTLE_SUMMARY.md`.

## M. Kernel theorems and `#print axioms`

New kernel theorems: `fableNu0_pos`, `fable_J_eq_four`,
`fable_ell_eq_twelve`, `fable_floor_inv_sigma_eq_six`,
`fable_splitting_bound_twenty_false`,
`fable_splitting_bound_le_twenty_one`,
`fixedExponent_mass_mono_exponent`,
`fixedExponentDivisorMass_sq_tail`, `fixedExponentDivisorMass_bound`, and
`summedExponentDivisorMass_bound`. The transparent closure accessor is
`R_GE_TWO_FIXED_APPLICATION_CLOSURE`.

## N. Analytic input records

The coefficient, factorisation, centered-weight, certificate, normalized-log,
and assembled closure records are explicit inputs. A proof-carrying input record
does **not** prove the analytic proposition stored in that record; it only makes
every downstream use expose a supplied proof.

## O. Build and trust audit

A full build and declaration-level axiom audit are recorded in the final task
report. Search distinguishes explanatory comments from declarations; no global
analytic inhabitant is introduced.

## P. Exact remaining frontier

Extract `PerfectPowerBranchSupport` from the formal source branch definitions,
prove concrete branch coefficient/multiplicity/weight estimates, and derive the
arbitrary-log-power closure from those estimates and the finite counting core.
Separately, the exact `r_h=1` binding class remains open.

## Q. Explicit nonclaims

Not banked or promoted: `R1_CENSUS_COMPLETE`, `EXACT_MINIMAL_CORE_ISOLATED`,
`O1_BINDING_CORE`, `O2_BINDING_CORE`, `FIXED_APPLICATION_TYPEII_PROVED`, or
`UNIVERSAL_TYPEII_PROVED`. No Type II, twin-prime, parity, or complete leakage
result follows from this update.

## R. Final verdict

`R_GE_TWO_BANK_UPDATE_PARTIAL`

---

# Fixed-Certificate / K0-K1 Structural Bank Update

## 1. Executive summary

Added a finite Boolean-cube formal bank for the fixed-certificate algebra and a
conservative K0/K1 status ledger. Kernel-proved results include the exact finite
expansion, One-Möbius normal form, Möbius finite difference, threshold strip,
alternating binomial prefix, hostile values for `r=7,...,14`, rough depth at most
six, certificate support through subset size three, K1 exponent-polytope bounds,
and a Boolean-cube squarefull repair. No analytic theorem is promoted.

## 2. Existing project preserved

The residue-aware Type-I status remains `EXTERNALLY_AUDITED` below exponent
`1/2`; the exact endpoint remains `OPEN_INPUT`. Existing local-density,
congruence, Euler-product, support, parity, reciprocal-tail, boundary,
comparison-candidate, and analytic-interface declarations are unchanged.

## 3. New Lean-proved algebraic theorems

`fixedCertificateNoRoughMobiusSign`,
`fixedCertificateExactFiniteExpansion`, `oneMobiusNormalForm`,
`mobiusFiniteDifference`, `finiteDifferenceStripEndpoint`,
`alternatingChoosePrefix`, `k0EqualFactorSignTable`,
`k0EqualFactorR9Value70`, `sigmaLowerBound`, `sevenSigmaGtOne`,
`roughPrimeCountAtMostSix`, `certificateSupportedSubsetSizeAtMostThree`,
`k1_alpha_gt_epsilon`, `k1_beta_ge_three_epsilon`, and
`squarefullKernelAlgebraicRepair`.

The exact fixed expansion is a finite theorem after the unique smooth/rough
indexing is supplied; it does not prove the analytic source decomposition.

## 4. Source-dependent records

`K0OpenCellStabilityInput` and `FordSourceGeometryInput` contain an explicit
proposition and proof field and have no global inhabitants. Their accessors are
conditional projections, not proofs of the analytic/source propositions.
K0 hostile-cell exclusion from the Ford set is `PROVED_MODULO_SOURCE`.

## 5. Status changes

- Arbitrary centered Ford Type II remains `OPEN_INPUT`, sufficient but possibly
  overbroad for the fixed certificate.
- `EXACT_VAUGHAN_OR_HEATH_BROWN_PACKET_LEDGER` is the current immediate
  `OPEN_INPUT` frontier.
- Anatomical BV, BFI weight-class matching, and DFI determinant matching are
  `HYPOTHESIS_MISMATCH`.
- The two direct K0/K1 reductions are audited failed routes for the precise
  reasons stored in `k0k1Ledger`.
- Squarefull-fibre uniform analytic summation remains `OPEN_INPUT`.

## 6. Files created or modified

Created `RequestProject/FixedCertificateAlgebra.lean` and
`RequestProject/K0K1Status.lean`; updated `RequestProject/TwinPrimeBanking.lean`
and this ledger. Existing theorem statements were not weakened.

## 7. Exact theorem statements

The Lean sources are authoritative. Principal shapes are finite sum exchange;
Boolean-cube signed splitting; the alternating choose prefix; rational threshold
bounds; finite-coordinate cardinality; and linear K1 inequalities.

## 8. Axiom audit

The final report records declaration-level checks. Proof-carrying record
accessors are explicitly reported as conditional and do not establish their
stored source or analytic proposition.

## 9. Updated dependency graph

```text
RESIDUE-AWARE COMPARISON
  ├── finite local-density core                  LEAN_PROVED
  ├── residue-aware Ford Type I                  EXTERNALLY_AUDITED (gamma < 1/2)
  └── exact gamma = 1/2 endpoint                 OPEN_INPUT
FIXED-CERTIFICATE ALGEBRA
  ├── no rough Mobius sign / expansion / OM      LEAN_PROVED
  ├── finite difference / strip                  LEAN_PROVED
  └── squarefull algebraic repair                LEAN_PROVED
K0 STRUCTURE
  ├── alternating prefix and finite table        LEAN_PROVED
  ├── open-cell stability                        CONDITIONAL_INTERFACE
  └── hostile cells outside N                    PROVED_MODULO_SOURCE
K1 STRUCTURE
  ├── alpha > epsilon; beta >= 3 epsilon         LEAN_PROVED
  └── analytic cancellation                      OPEN_INPUT
FINITE ROUGH ANATOMY
  ├── k <= 6                                     LEAN_PROVED
  └── certificate support |J| <= 3               LEAN_PROVED
CURRENT ANALYTIC FRONTIER
  ├── exact Vaughan/HB packet ledger             OPEN_INPUT / IMMEDIATE
  ├── anatomical BV                              HYPOTHESIS_MISMATCH
  ├── b-side anatomical main term                OPEN_INPUT
  ├── fixed-coefficient packets                  OPEN_INPUT
  └── arbitrary Ford Type II                     OPEN_INPUT / OVERBROAD SUFFICIENT
```

## 10. Trust and nonclaims

No Type-II, shifted-prime, smooth-number distribution, Vaughan routing, BFI,
DFI, determinant, parity-breaking, K0/K1 cancellation, twin-prime, or
Hardy--Littlewood theorem is claimed.

## Final verdict

`FIXED_CERTIFICATE_STRUCTURAL_BANK_UPDATE_COMPLETE`

---

# High-P3 Corrective Bank Update

## Executive status correction

The exact Vaughan identity, finite T0 vanishing, P1/P2/P3 pairing decomposition,
P2/P3 logarithmic modulus-weight bounds, odd-modulus implication, and finite P3
discrepancy routing are kernel checked.  No new unconditional full-dimensional
high-P3 cancellation estimate has been proved.

The names are fixed as `T0 = Lambda_<=V`, `P1 = mu_<=U * log`,
`P2 = mu_<=U * Lambda_<=V * 1`, and
`P3 = mu_>U * Lambda_>V * 1`.  `P1_VANISHES_IDENTICALLY` is
`FALSE_RETIRED`: only T0 vanishes on support above V.  Any separated P1 main
term is rejected; the joint `log((n+2)/d) * c(n)` weight must remain.

## Corrective dependency graph

```text
VAUGHAN ALGEBRA
  ├── exact identity                           LEAN_PROVED
  ├── T0 vanishing                             LEAN_PROVED
  ├── P1/P2/P3 decomposition                   LEAN_PROVED
  ├── P2/P3 modulus log bounds                 LEAN_PROVED
  └── P3 discrepancy routing                   LEAN_PROVED

FIXED CELLS
  ├── r=9 distribution to 5/9                  EXTERNALLY_AUDITED
  ├── r=9 low-P3 to 5/9                        PROVED_MODULO_EXACT_SOURCE
  ├── r=10 distribution to 93/160              EXTERNALLY_AUDITED
  └── r=10 low-P3 to 93/160                    PROVED_MODULO_EXACT_SOURCE

R9 FINITE ALGEBRA
  ├── block convolution                        LEAN_PROVED
  ├── repeated-factor correction               LEAN_PROVED
  └── repeated-prime sparse mass               OPEN_INPUT

HIGH-P3 DIRECT FAMILY
  ├── CRT/Poisson architecture                 PROOF_SKETCH_TEMPLATE
  ├── exact operator                           OPEN_INPUT
  ├── Kloosterman-fraction theorem match       OPEN_INPUT
  └── new cancellation                         OPEN_INPUT

HIGH-P3 SWITCHED FAMILY
  ├── divisor-switched architecture            PROOF_SKETCH_TEMPLATE
  └── cancellation                             OPEN_INPUT

LONG-BLOCK PIVOT
  ├── exponent arithmetic                      LEAN_PROVED
  └── analytic skeleton closure                PROOF_SKETCH_TEMPLATE

CERTIFICATE PIVOTS
  ├── all-lower certificate                    FALSE_RETIRED
  └── hybrid certificate                       LIVE / OPEN_INPUT

FINAL ASSEMBLY
  ├── b-side constants                         OPEN_INPUT
  ├── exact main-term matching                 OPEN_INPUT
  ├── Ford margin                              OPEN_INPUT
  └── Bus Stop 5                               NOT_PROVED
```

## Analytic records and exact frontier

`K0R9FixedCellDistributionInput`, `K0R10FixedCellDistributionInput`, and
`R9RepeatedPrimeSparseMassInput` are explicit proof-carrying inputs with source
metadata and no global inhabitants.  Their accessors only project supplied
proofs.  Fixed-cell interfaces require residue `-2`, odd moduli,
divisor-bounded coefficients, an exact Siegel--Walfisz block, and rough support
`z0 = X^(1/(log log X)^3)`.

The old all-P3-open statement is retired because source-range low P3 is
conditional on exact fixed-cell inputs.  Beyond those ranges, both direct and
divisor-switched high-P3 families remain open.  The proposed exact direct
operator was overstated and is retired historically; its corrected current
status is `OPEN_INPUT`.  Large dispersion gcd fibres are not classified as
sparse.

Pascadi direct matching is a `HYPOTHESIS_MISMATCH`; DFI, Bettin--Chandee,
Dong--Robles--Zeindler, and transformed Pascadi matches remain source-audit
`OPEN_INPUT`s.  Naive Weil completion is an `AUDITED_FAILED_ROUTE`, not a claim
that all Weil-based methods fail.

## Certificate and assembly correction

The all-lower certificate remains `FALSE_RETIRED`.  The hybrid remains a live
but unadopted `OPEN_INPUT`, pending prime normalisation, complete Ford geometry,
comparison constant, strict margin, and easier high-P3 classes.  Pair and triple
support corrections are finite theorems; K1 and k=2,...,6 high-P3 cancellation
remain open.  B-side constants, exact A/B main-term matching, Ford margin, and
final assembly remain open/conditional.

Explicit nonclaims: no exact r=9 high-P3 analytic operator, source match,
high-P3 saving, K0/K1 closure, k=2,...,6 closure, Ford positive margin, Bus Stop
5, twin-prime infinitude, Hardy--Littlewood, Dickson, or general parity theorem.

## Gate 0–1 finite bank (NANC finite-repair run)

Banked as finite algebra, `PROVED` in Lean (`RequestProject/NANC/Gate01/`):
`CANONICAL_CONGRUENCE_BANKED`, `GENERIC_CRT_RESIDUE_BANKED`,
`H_ZERO_CENTERING_CANCELLATION_BANKED`, `SAME_PRIME_NO_JOINT_HIT_BANKED`,
`EXCEPTIONAL_ROW_NO_HIT_BANKED`, `RAMANUJAN_MINUS_ONE_REMAINDER_BANKED`.

Interfaces and open inputs: `COMP_GENERIC_COMPLETION_INTERFACE`
(CONDITIONAL / INTERFACE), `STRUCTURED_DSTAR_OPEN_ANALYTIC_INPUT` and
`ARBITRARY_DSTAR_STRONGER_OPEN_ANALYTIC_INPUT` (OPEN_ANALYTIC),
`DSTAR_IMP_AVG_COV_CONDITIONAL_BANKED` (CONDITIONAL implication only),
`AVG_COV` (OPEN_ANALYTIC), `GENERIC_HIGH_P3_CLOSURE`
(OPEN_SOURCE_AND_ANALYTIC).

Audited: `OLD_DIRECT_BC_SLOT_DICTIONARY_FALSE_FOR_COMP_REPRESENTATION` — the
direct COMP representation does not produce the slot triple `(H, RL, M)`; its
natural masses are `(H, L, LM)` or `(H, L², M)`.  No claim that any
Bettin--Chandee, Wright or dispersion reformulation is impossible.

Explicitly preserved as open: `FULL_TYPE_II`, `FCPT`, `TWIN_PRIME`.  No Gate 0
or Gate 1 closure is claimed.  Details in
`RequestProject/NANC/Gate01/BankStatus.md`.

---

## ROOT-COLLAPSE / R4C / PPD finite bank (Gate01Root + Gate04Root)

```text
LATEST CONTROLLING FINITE ROUTE:
ROOT-COLLAPSE / R4C / PPD

FIRST OPEN ANALYTIC THEOREM:
PPD

FIRST OPEN SOURCE OBLIGATION:
exhaustive weighted clean-edge coverage

LEGACY DSTAR INTERFACES:
preserved, not claimed solved
```

Lean modules: `Gate04Root/` (standalone finite core) and
`RequestProject/NANC/Gate01Root/` (incremental delta on the Gate 0–1 bank,
exported by `RequestProject/NANCBank.lean`).

Machine-checkable statuses live in
`RequestProject/NANC/Gate01Root/Ledger.lean` (`status : Item → Status`).

| Item | Status | Lean |
|---|---|---|
| Affine root identities `m'α − mβ = 2k`, `rβ = m'w₀ + 2` | PROVED | `Gate01Root/AffineRoot.lean` |
| Canonical range `0 ≤ w₀ < r` ⇒ `0 < α ≤ m` (needs `2 ≤ m`) | PROVED (reconstructed hypothesis) | `Gate01Root/AffineRoot.lean` |
| Root gcd lemmas `gcd(α,m) = gcd(β,m') = 1` (odd modulus) | PROVED | `Gate01Root/GCDRoot.lean` |
| BAL residue `k (m')⁻¹ = r⁻¹`, CRT projections | PROVED | `Gate01Root/BAL.lean` |
| Exact CRT roots `t_p`, `t_q`, `T_{pq}`, uniqueness | PROVED | `Gate01Root/CRTRoots.lean` |
| ROOT-COLLAPSE `m ∣ N_J`, residues, rational identity | PROVED | `Gate01Root/RootCollapse.lean` |
| Root-collision criteria, `Δ_A`/`Δ_B` rigidity, double zero | PROVED | `Gate01Root/RootCollisions.lean` |
| Divisor-relaxed row injection, divisor cardinal comparison | PROVED | `Gate01Root/DivisorRows.lean` |
| Fourth-moment row/column duality and diagonal split | PROVED (reuses `gramFourth_eq_corr_sq`) | `Gate01Root/MatrixFourthMoment.lean` |
| R4C ⇒ test-vector / operator / avg-cov scale | CONDITIONAL implication only | `Gate01Root/R4CInterfaces.lean` |
| Repeated-`p` bound `P₀E₀²C⁴`, symbolic `M⁴L⁵/H⁴` | CONDITIONAL on B-POINT | `Gate01Root/RepeatedP.lean` |
| `PPD + repeated-p ⇒ R4C` | PROVED (exact split) | `Gate01Root/PPDInterfaces.lean` |
| HIT-p | OPEN ANALYTIC INPUT | interface only |
| HIT | OPEN ANALYTIC INPUT | interface only |
| B-POINT | CONDITIONAL ON HIT-p + KERNEL DECAY | interface only |
| B-ROW | CONDITIONAL ON B-POINT | interface only |
| R4C | OPEN ANALYTIC INPUT | interface only |
| PPD | FIRST OPEN ANALYTIC INPUT | interface only |
| G0-COVER | OPEN SOURCE INPUT | interface only |
| SOURCE-G exact decomposition, `N_source = −N'` | PROVED | `Gate01Root/SourceGConsistency.lean` |
| ROOT MATRIX EQUALS SOURCE-G, ARCH FACTOR NEGLIGIBLE | CONDITIONAL / AWAITING OPUS AUDIT | uninhabited interfaces |
| Exponent ledger at `V₁`, `V₂`, `V₃` | PROVED (exact ℚ) | `Gate01Root/ExponentLedger.lean` |

No inhabitant of any analytic interface is constructed.  Nothing in this bank
claims PPD, R4C, Gate 0–4 closure, full Type II, FCPT or twin primes.

# Gate01Switch — switched high-P₃ finite bank

Machine-checkable statuses live in
`RequestProject/NANC/Gate01Switch/Ledger.lean` (`status : Item → Status`), and
the top-level direct/switched table in
`RequestProject/NANC/Gate01CombinedLedger.lean`.  Detailed notes:
`RequestProject/NANC/Gate01Switch/BankStatus.md`.

| Item | Status | Lean |
|---|---|---|
| RESIDUE_MINUS_TWO (`q ∣ n+2`, ZMod and natural-residue forms, boundaries) | PROVED | `Gate01Switch/ResidueMinusTwo.lean` |
| LAMBDA3_SOURCE (archive `lambda3` reused, not redefined) | PROVED | `VaughanPacketAlgebra.lean` |
| LAMBDA3_PRIME_POWER (L3-PP) | PROVED | `Gate01Switch/Lambda3.lean` |
| LAMBDA3_SQUAREFREE (L3-SF, `−μ(q) ∑ log p`) | PROVED | `Gate01Switch/Lambda3.lean` |
| SW0_SW1 (exact multiplier reindexing) | PROVED | `Gate01Switch/SwitchedOperator.lean` |
| SW1_SW2 (divisor-pair opening) | PROVED | `Gate01Switch/DivisorPairs.lean` |
| PRIME_POWER_DECOMPOSITION | PROVED | `Gate01Switch/PrimePowerStructure.lean` |
| PRIME_POWER_ANALYTIC_BOUND | EXPLICIT INTERFACE | uninhabited |
| REPEATED_P_ALGEBRA (`d = p d₀`, `p ∤ d₀`, squarefree, uniqueness) | PROVED | `Gate01Switch/RepeatedPrime.lean` |
| REPEATED_P_ANALYTIC_BOUND | EXPLICIT INTERFACE | uninhabited |
| GENERIC_SWITCHED_OPERATOR (exact three-way split) | PROVED | `Gate01Switch/GenericSwitched.lean` |
| SWITCHED_EXPONENT_GEOMETRY (exact ℚ) | PROVED | `Gate01Switch/ExponentGeometry.lean` |
| WELL_FACTORABLE_LOCAL_OBSTRUCTION | PROVED (local, conditional) | `Gate01Switch/WellFactorable.lean` |
| WELL_FACTORABLE_GLOBAL_CONCLUSION | WF_GLOBAL_NOT_PROVED (SourceOpen) | — |
| VAUGHAN_SWITCH_IDENTITY (`P₃ = Λ − P₁ + P₂`) | PROVED (source match) | `Gate01Switch/VaughanSwitchIdentity.lean` |
| R9_CELL_CONVOLUTION (C9) | SOURCE OPEN — not in the archive | hypothesis only |
| Q5_EQUATION (`mn + 2 = dpr`) | PROVED | `Gate01Switch/Q5Equation.lean` |
| Q5_ANALYTIC_BOUND | OPEN ANALYTIC INPUT | uninhabited |
| ACTUAL_C_DICTIONARY | SOURCE OPEN | uninhabited |
| ACTUAL_E_DICTIONARY | SOURCE OPEN | uninhabited |
| GATE0_SWITCHED_COVERAGE | SOURCE OPEN | uninhabited |
| GATE0_EXHAUSTIVE_OPERATOR_COVERAGE | SOURCE OPEN | uninhabited |
| GATE1B | OPEN ANALYTIC INPUT | uninhabited |

Direct and switched analytic operators are kept strictly separate.  No claim
that direct + switched exhaust the high-P₃ packets is made.

# Gate01Consolidation — Gate 0–1 finite consolidation bank

Machine-checkable statuses live in
`RequestProject/NANC/Gate01Consolidation/StatusLedger.lean`
(`status : Item → ProofStatus`).  Detailed notes:
`RequestProject/NANC/Gate01Consolidation/BankStatus.md`.

| Item | Status | Lean |
|---|---|---|
| E-separation (ESEP1 / ESEP2, nonzero term independent of `E`) | provedFinite | `Gate01Consolidation/ESeparation.lean` |
| Nonzero additive orthogonality (NZORTH) and RES_EQ | provedFinite | `Gate01Consolidation/NonzeroOrthogonality.lean` |
| CRT natural centering (CRT-CENTER), frequency modes, CRT frequency bijection | provedFinite | `Gate01Consolidation/CRTCentering.lean` |
| CRT source-density centering (CRT-SRC, premise DENS-MULT) | provedConditional | `Gate01Consolidation/CRTCentering.lean` |
| Shift-inverse algebra (SHIFTINV, SHIFT_PHASE) | provedFinite | `Gate01Consolidation/ShiftInverse.lean` |
| Shift representation multiplicity (divisor bound) | provedFinite | `Gate01Consolidation/ShiftInverse.lean` |
| Prime covariance kernel (KP, KP-DIAG, KP-OFF) | provedFinite | `Gate01Consolidation/PrimeCovariance.lean` |
| Prime-centered second moment identity (P2MOM) | provedFinite | `Gate01Consolidation/PrimeCovariance.lean` |
| Prime-centered off-diagonal bound | openAnalytic | uninhabited |
| ANOVA product-mode obstruction | provedFinite | `Gate01Consolidation/ProductModeObstruction.lean` |
| Determinant identity (DET) | provedFinite | `Gate01Consolidation/DeterminantIdentity.lean` |
| Determinant closure route (strict reduction) | reformulationOnly | — |
| Direct Gauss / character reassembly (CHAR-COMB, GAUSS-CONG, GAUSS-PHYS, DIRECT-PHYS) | provedFinite | `Gate01Consolidation/DirectGaussReassembly.lean` |
| Non-unit linear congruence stratification | provedFinite | `Gate01Consolidation/DirectGaussReassembly.lean` |
| Direct physical-phase bound | openAnalytic | uninhabited |
| r = 9 block family and 4\|5 regrouping (REGROUP-PROD / REGROUP-CONG, BLOCK-PARITY) | provedFinite | `Gate01Consolidation/R9Regrouping.lean` |
| 4\|5 threshold crossing and WEIL-DEF exponent arithmetic | provedFinite | `Gate01Consolidation/ExponentThresholds.lean` |
| 4\|5 q-averaged dispersion | openAnalytic | uninhabited |
| Switched centered mixed covariance | openAnalytic | uninhabited |
| Exact source expectation `E(q)` | openSource | uninhabited |
| j = 3..6 exact switched routing | openSource | uninhabited |
| Global high-P₃ exhaustive routing | openSource | uninhabited |
| Gate 1A / Gate 1B | openAnalytic | uninhabited |
| Gate 0 | openSource | uninhabited |

Gate 1A / Gate 1B / Gate 0 statuses agree with
`RequestProject/NANC/Gate01CombinedLedger.lean`; no existing status is
overwritten.  No analytic interface of this bank is ever inhabited.

## Switched r = 9 / 4|5 h-Poisson bridge — finite bank (HPoissonComplementaryDivisor)

Bank: `RequestProject/NANC/HPoissonComplementaryDivisor/`
(full report: `RequestProject/NANC/HPoissonComplementaryDivisor/StatusLedger.md`).

| Item | Status | Location |
|---|---|---|
| CRT existence / uniqueness mod `q₁q₂`, unit transfer | provedFinite | `CRTPhase.lean` |
| Additive CRT inverse phase identity (integer + rational mod 1) | provedFinite | `CRTPhase.lean` |
| Post-Poisson congruence reindexing `y ≡ 2w̄ ↔ yw ≡ 2`, CRT split | provedFinite | `PoissonCongruenceCore.lean` |
| Change of variables `y = nc + 2w̄` as a bijection | provedFinite | `PoissonCongruenceCore.lean` |
| Complementary divisor `yv − qℓ = 2`: existence, uniqueness, factorization | provedFinite | `ComplementaryDivisor.lean` |
| Exponent identities for `U = X^{4/9}`, `V = X^{5/9}`, `Q = X^{13/18}`, `H₀ = X` | provedFinite | `ExponentGeometry.lean` |
| Corrected dyadic `L_ℓ = YV/Q` exponent `γ − 1/6 ∈ [0, 5/18]`; global `ℓ ∼ X^{5/18}` refuted | provedFinite | `ExponentGeometry.lean` |
| Centered indicator `ρ_q` and coprime CRT expansion | provedFinite | `CenteringCore.lean` |
| Separation of the four centering operations | provedFinite | `CenteringCore.lean` |
| `T_A` target exponent `23/9 − 2δ` | conditionalOnSourceNormalization | `ConditionalExponentLedger.lean` |
| Real Poisson with source weight, source centering match, non-coprime strata, centered incidence variance, global switched reassembly, `d₂×d₃` dictionary, full Type II | openAnalytic / openSource | uninhabited predicates |

No analytic interface of this bank is ever inhabited; no existing status is
overwritten.

## Twin Prime Gate 1B — source-native HFMV determinant bank (HFMVGate1B)

Bank: `RequestProject/NANC/HFMVGate1B/`
(full report: `RequestProject/NANC/HFMVGate1B/StatusLedger.md`).

| Item | Status | Location |
|---|---|---|
| Complementary divisor `u v + 2 = d p l`: equivalence, uniqueness, positivity, dyadic range | provedFinite | `HFMVComplementaryDivisor.lean` |
| Determinant identity `v₂ d₁p₁l₁ − v₁ d₂p₂l₂ = 2(v₂ − v₁)` over `ℤ` | provedFinite | `HFMVDeterminant.lean` |
| Determinant converse with `u = (d₁p₁l₁ − 2)/v₁ = (d₂p₂l₂ − 2)/v₂` | provedFinite | `HFMVDeterminant.lean` |
| Diagonal identity `v₁ = v₂ → d₁p₁l₁ = d₂p₂l₂` and exact fibre-square decomposition | provedFinite | `HFMVDiagonal.lean` |
| Diagonal size bound | conditionalOnSuppliedDivisorCount | `HFMVDiagonal.lean` |
| Exponent ledger `U = X^{4/9}`, `V = X^{5/9}`, `Q = X^{13/18}`, `UV/Q = X^{5/18}`, `Q²/V² = X^{1/3}` | provedFinite | `HFMVExponentLedger.lean` |
| B1 determinant multiplicity one and abstract finite energy inequality | provedFinite | `B1DeterminantEnergy.lean` |
| Möbius dyadic log saving, dyadic divisor bound, small proper gcd, source centering match | externalAnalytic / openSource | uninhabited predicates |
| GSDV generic off-diagonal | openAnalytic | uninhabited predicate |
| Gate 1B, full Type II, twin primes | notProved | — |

No analytic interface of this bank is ever inhabited; `Gate1BClosed` is not
stated; no existing status is overwritten.

## Twin Prime Gate 1B — post-MAM45 determinant-2 deterministic bank (Gate1BDet2)

Bank: `RequestProject/NANC/Gate1BDet2/`
(full report: `RequestProject/NANC/Gate1BDet2/StatusLedger.md`).

| Item | Status | Location |
|---|---|---|
| Möbius prime-cofactor sign identity `μ d = −μ q` (squarefreeness not needed) | provedFinite | `ModulusSignCollapse.lean` |
| Weighted cell collapse `λ_{D,P}(q) = −μ(q) L_{D,P}(q)`, abstract ring-valued weight | provedFinite | `ModulusSignCollapse.lean` |
| Constant Möbius sign over distinguished primes of a fixed squarefree `q` | provedFinite | `ModulusSignCollapse.lean` |
| Congruence ↔ complementary divisor `u v + 2 = q l`, fixed shift 2 | provedFinite | `ComplementaryDivisorDet2.lean` |
| Determinant-2 integer normal form `l q − u v = 2` | provedFinite | `ComplementaryDivisorDet2.lean` |
| Divisor rigidity `gcd(u,l) ∣ 2`, `gcd(v,q) ∣ 2`; odd-sector coprimality | provedFinite | `Det2Coprime.lean` |
| Exact affine-line parametrisation with unique parameter `t` | provedFinite | `Det2AffineLines.lean` |
| Affine-form gcd divides 2; odd affine forms coprime | provedFinite | `Det2AffineCoprimality.lean` |
| Rational exponent ledger `4/9 + 5/9 = 1`, `ω + (1−ω) = 1`, `13/18 − 4/9 = 5/18` | provedFinite | `Gate1BExponentLedger.lean` |
| Small-measure correlation lemma (Phase B) | provedFinite | `SmallMeasureCorrelation.lean` |
| Dyadic amplitude layers: Chebyshev bound, `4·2^(−|j−k|)` correlation, finite tail | provedFinite | `DyadicAmplitudeSeparation.lean` |
| Modulus Fourier uniformity, natural major arc, PMS45, OST45 | externalAnalytic | uninhabited predicates |
| Source expected term, switched packet reassembly, Gate-0 exhaustiveness | openSource | uninhabited predicates |
| Gate 1B closure, full Type II, twin primes | notProved | uninhabited predicates |

No interface of this bank is ever inhabited; no earlier status is overwritten.

## Gate 1B post-MAM45 bank extension (Gate1BDet2, Modules 10–17)

Bank: `RequestProject/NANC/Gate1BDet2/`
(full report: `RequestProject/NANC/Gate1BDet2/StatusLedger.md`).

| Item | Status | Location |
|---|---|---|
| DFBT on-shell Gram identity `Δ = q₁q₂(ℓ₁−ℓ₂)` | provedFinite | `DFBTAntiLoop.lean` |
| Congruence lifting + integer rigidity ⟹ `r = ℓ₁ − ℓ₂` | provedFinite | `DFBTAntiLoop.lean` |
| DFBT off-shell decomposition `Δ = q₁q₂(ℓ₁−ℓ₂) + η₁q₂ − η₂q₁` | provedFinite | `DFBTOffShell.lean` |
| δ-conductor exponent ledger (`Uₑ+Vₑ=1`, `Qₑ+Rₑ=1`, `1/9 ≤ Rₑ ≤ 5/18`, `2Rₑ<Qₑ`) | provedRational | `DeltaExponentLedger.lean` |
| Near-top dual exponent `Hₑ = 2ω−1`, `Hₑ/Qₑ = 2 − 1/ω = 8/13` at `ω = 13/18` | provedRational | `DeltaExponentLedger.lean` |
| `C_e = Q_e = ω` | workingAnalyticChoice (rational label only) | `DeltaExponentLedger.lean` |
| Endpoint arithmetic `8/39 − 1/5 = 1/195` | provedRational | `NearTopKloostermanLedger.lean` |
| Prime-modulus coordinate change `uv+2 = u(v+2u⁻¹)`, character rewrite, injectivity of `u ↦ 2u⁻¹` | provedFinite | `PrimeCharacterReduction.lean` |
| Karatsuba-regime margins (`Uc ≥ 1/2`, `Vc ≥ 5/8`, `−1/160`, `−37/160`, saving `1/160`) | provedRational | `KaratsubaExponentLedger.lean` |
| Finite-depth dyadic Möbius identity `μ(d) = −(μ_{≤y}*μ_{≤y}*ζ)(d)` (+ finite divisor-sum form) | provedFinite, sign corrected | `MobiusK2Dyadic.lean` |
| Unsigned form of that identity | refuted in Lean | `MobiusK2Dyadic.lean` |
| Delta blocks, near-top MC45, Karatsuba input, prime/composite MC45 transfers, zero dual, source `E(q)`, κ₄, packet, Gate 1B closure | externalAnalytic / openSource | uninhabited predicates in `Gate1BMCInterfaces.lean` |
| `PrimeCharacterKaratsubaInput → PrimeMC45CovarianceTransfer` | not proved (missing covariance datum; guard supplied) | `Gate1BMCInterfaces.lean` |
| Karatsuba/FSX analytic theorem, Blomer–Pascadi, delta-symbol estimates | notFormalized | — |
| Gate 1B, full Type II, twin primes | notProved | — |

No interface of this extension is ever inhabited, no axiom is declared, and no
earlier status is overwritten.

## Gate 1B on-shell bank extension III (Gate1BDet2, Modules 19–29)

Bank: `RequestProject/NANC/Gate1BDet2/`
(full report: `RequestProject/NANC/Gate1BDet2/StatusLedger.md`, section
"Extension III").

| Item | Status | Location |
|---|---|---|
| Pair shift identity `v₂z₁ − v₁z₂ = h(ℓz₁ − uv₁)` | provedFinite | `PrimitiveDet2PairSurface.lean` |
| On-shell pair determinant `= 2h` | provedFinite | `PrimitiveDet2PairSurface.lean` |
| Translation stability `ℓ(z+uh) − u(v+ℓh) = ℓz − uv` | provedFinite | `PrimitiveDet2PairSurface.lean` |
| gcd recovery `gcd(ℓh, uh) = h` (ℕ and ℤ) | provedFinite | `CommonShiftGCD.lean` |
| Pair-surface forward package (`= 2h` and `gcd = h`) | provedFinite | `CommonShiftGCD.lean` |
| Pair-surface converse (cancellation of `h`), normal-form uniqueness | provedFinite | `PrimitiveDet2PairConverse.lean` |
| β-pair rigidity `u ∣ Δz`, `ℓz₁ ≡ 2 (mod u)`, short-interval uniqueness of `ℓ` | provedFinite | `CommonShiftRigidity.lean` |
| b-pair rigidity `ℓ ∣ Δv`, `uv₁ ≡ −2 (mod ℓ)` | provedFinite | `CommonShiftRigidity.lean` |
| Residue-class count in an interval `≤ (b−a)/m + 1` | provedFinite | `CommonShiftRigidity.lean` |
| Abstract bipartite Schur bound (squared and sqrt forms) | provedFinite | `CommonShiftSchur.lean` |
| `k = 0,1,2` split ledger (`x_k, s_k, H_k, Rₑ/s_k`) | provedRational | `SplitSchurExponentLedger.lean` |
| Schur endpoint losses `δ₀ = 1/12 < δ₁ = 5/36 < δ₂ = 7/36` | provedRational, method-specific only | `SplitSchurExponentLedger.lean` |
| `(1/2)(3·5/18 − 13/18) = 1/18` and `1/12 − 1/36 = 1/18` | provedRational, method-specific only | `SequentialDeficitLedger.lean` |
| Analytic stacking of the `1/12` and `1/36` savings | not proved (Guard B) | `SequentialDeficitLedger.lean` |
| Pascadi `k = 1` four-prime grouping rational no-go (all three groupings) | provedRational | `PascadiGroupingLedger.lean` |
| Pascadi Proposition 6.3 itself | externalAnalytic / notFormalized | — |
| `2 × 2` unipotent action and determinant preservation | provedFinite | `Det2Unipotent.lean` |
| Joint-Fourier interfaces; `ExactJointFourierRepresentation → NewOrthogonality` | openInterface; not proved (guard supplied) | `JointFourierInterfaces.lean` |
| On-shell analytic core, mixed fourth moment, pre-Cauchy `P45`, determinant-conditioned `U^{1+}`, quotient-weight separation, automorphic source-weight compatibility, source `E(q)`, Gate 1B closure | openInterface | `Gate1BOnShellInterfaces.lean`, `JointFourierInterfaces.lean` |
| `PrimitivePairSurfaceBanked → OnShellAnalyticCoreClosed` | not proved (guard supplied) | `Gate1BOnShellInterfaces.lean` |
| Gate 1B, full Type II, twin primes | notProved | — |

No interface of this extension is ever inhabited, no axiom is declared, and no
earlier status is overwritten.

## NANC Bank Extension IV — Gate 1B reciprocal frame / composite view / source boundary

| Item | Status | File |
|---|---|---|
| Finite additive orthogonality on `ZMod q` | provedFinite | `Det2AdditiveReciprocalFrame.lean` |
| Additive frame `1_{uv=−2} = q⁻¹ ∑_h e_q(hv+2hu⁻¹)` | provedFinite | `Det2AdditiveReciprocalFrame.lean` |
| Zero mode ≠ source expected term (guard) | provedFinite | `Det2AdditiveReciprocalFrame.lean` |
| Reciprocity congruence `u q ∣ u ū + q q̄ − 1` | provedFinite | `Det2Reciprocity.lean` |
| Phase reciprocity `e(2hū/q) = e(−2hq̄/u) e(2h/(uq))` | provedExact | `Det2Reciprocity.lean` |
| Gram relation, block support, block size `g`, row sum `mg` | provedFinite | `FiniteReciprocalFourierOperator.lean` |
| Coprime case: normalised kernel has orthonormal rows | provedFinite | `FiniteReciprocalFourierOperator.lean` |
| Operator-norm identity `‖F‖ = √(mg)` | openInterface | `FiniteReciprocalFourierOperator.lean` |
| Fixed-cell twisted convolution `D·P = ∑_q β(q)τ(q)` | provedExact | `FixedCellBetaTwistRecombination.lean` |
| Fixed-cell ≠ full-face recombination (guard) | provedFinite | `FixedCellBetaTwistRecombination.lean` |
| Composite view `q l ≡ 2 (mod u)`, `(mod s)`, `(mod us)` | provedExact | `CompositeViewDet2.lean` |
| Composite-view interval uniqueness of `l`; reconstruction of `ρ` | provedExact | `CompositeViewDet2.lean` |
| Composite-view multiplicity `≤ Mfact` | provedFinite | `CompositeViewMultiplicity.lean` |
| Projective third-coordinate rigidity over odd `p` | provedExact | `ProjectiveThirdCoordinateRigidity.lean` |
| Projective rigidity ⇏ operator saving (guard) | provedFinite | `ProjectiveThirdCoordinateRigidity.lean` |
| `λ_c(q) = −μ(q) L_c(q)`; switched-packet recombination | provedExact | `FullFaceFixedPacket.lean` |
| `L_sw(q) = log q`; `SourceFaceCompleteness` | notProved / openInterface | `FullFaceFixedPacket.lean` |
| `(μ*Λ)(n) = −μ(n) log n`; `ζ*(μ*Λ) = Λ`; derivation identity | provedExact | `FullDivisorBoundaryAlgebra.lean` |
| Spectator non-tensorization countermodel | provedFinite | `SpectatorNonTensorizationGuard.lean` |
| Upper-band interfaces; two deterministic chains; three guards | openInterface / provedDeterministic | `Gate1BUpperBandInterfaces.lean` |
| Finite Steinberg jet (explanatory) | provedFinite | `SteinbergJetFinite.lean` |
| Band II, lower/upper Band III, master bound, Gate 1B closure | notProved | — |
| Full Type II, twin primes | notClaimed | — |

---

# Gate-1A Δv4 — final closure certification (appended)

Lean artifacts: `Gate1A/Delta4/` (14 modules), inside the `Gate1A` library.
Full structured report: `GATE1A_DELTA_V4_REPORT.md`.

| Δv4 item | Status |
|---|---|
| α range `0 ≤ α < m + 2/r` and the Archimedean bound | PROVED |
| root collapse `m'α − mβ = 2k` (exact modular) | PROVED |
| Option A / quotient recombination | RETAINED (unchanged) |
| flat profile remainder `≤ C_N U⁻¹` | PROVED |
| error root capacity `U⁻¹ ≤ √(H/M)`, margins 1/36, 1/36, 1/48 | PROVED |
| two-sided S2 norm equivalence | RETRACTED (countermodel banked) |
| S2-UPPER `‖C‖ ≤ C₀B + ‖Err‖` | PROVED |
| rank-one `p/q` separation | PROVED |
| corrected PB `Z`-coordinate identity | PROVED |
| corrected PB analytic lattice bound | OPEN INTERFACE |
| `Z = 0 ⇒ a = n = 0` | PROVED |
| `L = 0 ⇒ h₁ = h₂ = 0` | PROVED |
| outer dictionary `S_r(0,L) = −1 / r−1` | PROVED (both branches) |
| "all five factors are −1" | REFUTED |
| `Z = 0, r ∤ L` regular axis contraction | PROVED |
| `Z = 0, r ∣ L` true local zero / divisor sparsity | PROVED |
| generic S3 projective pushforward | PROVED (ratio grouping; product grouping refuted) |
| prime-quadruple no-tax | PROVED |
| outer curvature `R^{−1}` saving | PROVED |
| clean-block partition (5 sectors, exhaustive + disjoint) | PROVED |
| p/q face cascade | NON_LOAD_BEARING_FOR_MAIN_CLEAN_BLOCK (old face lemmas retained) |
| root depth, exactly one Cauchy over `r`, margins 1/12, 1/9, 5/48 | PROVED |
| exceptional routing table (11 items) | 2 PROVED MAP, 9 OPEN |
| §27 conditional assembly `gate1a_of_final_interfaces` | PROVED |
| §28 unconditional theorem | NOT CREATED (by design) |

First remaining unproved interface: **flat-profile source legality**.

## Final Δv4 status

`GATE1A_CLOSURE_FORMALISED_CONDITIONAL_ON_EXPLICIT_INTERFACES`

## Gate 1B / Gate 1A safe algebra bank (new session)

New libraries `Gate1B/` and `Gate1A/SafeAlgebra/`; full report in
`GATE1B_SAFE_ALGEBRA_REPORT.md`.

* Gate 1B: integer shell and mod-`r²` unit form (S1); on-shell multiplicative
  character saturation SAT1 and SAT-k (arbitrary hom into a commutative group,
  arbitrary integer exponents); C45 master identity `D = u(v₁ℓ₂ − v₂ℓ₁)`;
  `u ∣ (v₁ℓ₂ − v₂ℓ₁) ↔ u² ∣ D` (converse needs `u ≠ 0`, countermodel banked);
  zero-defect diagonal lemma with explicit `(ZD-HYP)` (also shown load-bearing);
  additive coordinate `R ∣ D ↔ q₁ − 2ℓ₁⁻¹ ≡ q₂ − 2ℓ₂⁻¹ (mod R)`; local
  prime-square lift `s² ∣ D ↔ x₁ ≡ x₂ (mod s)`; local density `s/s² = 1/s`;
  four-prime CRT factorisation and the exact four-local-collision equivalence;
  anti-Cartesian counterexample `shell_sum_ne_cartesian_sum`.
* Guards banked: saturation carries no value information; `u ≠ 0` and `(ZD-HYP)`
  are load-bearing; the four local conditions are NOT independent.
* Gate 1A companion bank: outer projective defect `Z₁L₂ − Z₂L₁`, PB expansion,
  projective rigidity under primitivity, additive projective coordinate
  `Z L⁻¹ (mod R)`, local prime-square lift, four-prime CRT, finite fibre counts,
  anti-Cartesian guards and the additive saturation certificate.
* Interface-only (comments, no declarations, never inhabited): MAM45,
  SIGNED_C45, ASPE45, PSC45, ADDITIVE_PSQ_C45, ZHAO_SQUARE_MODULUS_LARGE_SIEVE,
  E(q), Z_E(q), KAPPA4, FIXED_SWITCHED_REASSEMBLY, and the five open Gate-1A
  analytic interfaces.
* Analytic claims banked: NONE. Gate 1B closure: NOT claimed. Gate 1A closure:
  unchanged, still conditional.

---

## UNIVERSAL v8 SAFE FORMAL BANK EXTENSION (appended, nothing overwritten)

```text
LEAN 4.28.0 / mathlib 8f9d9cff6bd728b17a24e163c9402775d9e6a365
LAKE BUILD: PASS (8368 jobs)
SORRY: 0   USER AXIOM: 0   OPAQUE: 0   NATIVE_DECIDE: 0   IMPLEMENTED_BY: 0

OLD GATE1A/GATE1B SAFE ALGEBRA REGRESSION:  PASS (rebuilt from source, unchanged)
DISCRETE ABEL IDENTITY:                     PROVED   UniversalV8.local_sum_by_parts
ABSTRACT BV BOUND:                          PROVED   norm_sum_le_partialSumBound_mul_variation
                                                     weighted_sum_le_partialSum_mul_dBV
PIECEWISE ROUTING JUMP -> BV:               PROVED   variation_le_two_mul_bound_mul_jumpCount
                                                     dBV_le_of_jumpCount
SYNTHESIS / BLOCK GRAM:                     PROVED   blockGramIdentity, synthesis_norm_sq,
                                                     normalizedSynthesisBound
ACTUAL-VECTOR TRANSPORT:                    PROVED   inner_apply_le_of_apply_norm_le,
                                                     actualVectorTransport
UNWEIGHTED SCHUR:                           PROVED   (strengthened: arbitrary real x)
WEIGHTED SCHUR:                             PROVED   (repaired: symmetry load-bearing,
                                                     countermodel weightedSchur_needs_symmetry)
BUDGETED SYNTHESIS PRINCIPLE:               PROVED   budgetedSynthesis(_closes,_ratio)
DIAGONAL/OFF-DIAGONAL DECOMPOSITION:        PROVED   gram_eq_diag_add_offdiag,
                                                     quadraticForm_eq_diag_add_offDiag
OPEN CHAIN k = 2:                           PROVED   Universal.SafeAlgebra.openChain_two
CLOSED-CYCLE SIGN ERASURE:                  PROVED   closedCycle_trace_invariant,
                                                     closedCycle_sign_telescopes
NO-FREE-FAMILY COUNTERMODEL:                PROVED   identical_packets_have_family_congestion
NO-FREE-SIGN COUNTERMODEL:                  PROVED   signs_do_not_force_cancellation
dBV LOAD-BEARING COUNTERMODEL:              PROVED   dBV_needs_partialSum_bound
DEFECT CAPACITY:                            PROVED   defectCapacity (coprimality shown
                                                     unnecessary for the product form),
                                                     defectCapacity_pow, defectCapacity_log
GATE 1A BP EXPONENT REPAIR:                 PROVED EXACTLY OVER ℚ
GATE 1A WORST ENERGY SURPLUS:               1/72     bp_worst_energy_surplus
GATE 1A AMPLITUDE TAX:                      1/144    bp_amplitudeTaxMargin
GATE 1B NO-WRAP EXPONENT LEDGER:            PROVED   nearPrimitiveNoWrapExponent
GATE 1B DIAGONAL EXPONENT FLOOR:            1/18     npl_diagonal_saving_floor
ABSTRACT SAME-CONDUCTOR DIAGONAL REDUCTION: PROVED   sameConductorDiagonal_le
GATE 1B X/Q = R BUDGET:                     PROVED   X_div_Q_eq_R, gate1B_congestionBudget
MOEBIUS FIXED-q SIGN COLLAPSE:              PROVED   squarefree_moebius_remove_prime,
                                                     fixedQ_weightedSignCollapse
PRIMITIVE-CONDUCTOR TRICHOTOMY:             PROVED   primitiveConductorTrichotomy
CENTERED rho_dp IDENTITY:                   REUSED   Gate01Consolidation.rho_mul_coprime
                                                     (already banked; not duplicated)

ROUTE-BV45:      INTERFACE ONLY — OPEN (source lock)
NPL-OFF45:       INTERFACE ONLY — OPEN
CF-BP1A:         INTERFACE ONLY — OPEN
ANALYTIC CLAIMS BANKED: NONE
GATE 1A CLOSED: NO      GATE 1B CLOSED: NO
FULL TYPE II / TWIN PRIMES: NOT INFERRED

REPAIR OF RECORD: two pre-existing `native_decide` proofs in
RequestProject/NANC/PatternCount69.lean are now kernel-checked `decide`.
```

Full statement-by-statement report: `UNIVERSAL_V8_SAFE_FORMAL_REPORT.md`.

---

## UNIVERSAL v8.1 — GATE 1B PHYSICAL-SPLICE / PCL MIXED-FACE EXTENSION (appended)

```text
REGRESSION:                                 PASS (8379 jobs, exit 0, 0 errors)
BUILD:                                      PASS
SORRY / ADMIT / USER AXIOM / OPAQUE:        0 / 0 / 0 / 0
NATIVE_DECIDE / @[implemented_by]:          0 / 0

QUADRATIC + SESQUILINEAR HOMOGENEITY:       PROVED   quadraticEnergy_smul,
                                                     sesquilinear_same_smul,
                                                     finiteSesquilinearForm_smul
NO POSITIVE UNIFORM ENERGY FLOOR:           PROVED   noPositiveUniformEnergyFloor,
                                                     zeroEnergy_counterexample
C2 LOWER-FLOOR RETRACTION GUARD:            PROVED   c2Floor_not_formal_from_upperBound,
                                                     noAutomaticC2LowerMass
PHYSICAL OUTER CAUCHY:                      PROVED   physicalOuterCauchy
PHYSICAL SECOND-MOMENT BUDGET:              PROVED   gate1B_physicalSecondMomentBudget
HFMV WEIGHTED FACE DECOMPOSITION:           PROVED   rawCentered_eq_mixed_add_unaryD_add_unaryP
MIXED-FACE ≠ RAW SOURCE (FIREWALL):         COUNTERMODEL
                                                     mixedFace_ne_raw_without_unary_hypotheses
RAMANUJAN DIVISOR IDENTITY:                 PROVED   ramanujanSum_over_divisors
PROPER-DIVISOR RAMANUJAN = d·rho_d:         PROVED   ramanujanProperDivisors_eq_centeredDivisibility
PCL MIXED-FACE EXACT REINDEXING:            PROVED   pclMixedFace_exact,
                                                     betaMixedFace_to_PCL_exact
PCL FINITE EULER SQUARE-MASS CORE:          PROVED   subsetProductSquareSum_eq_eulerProduct,
                                                     pclCoreSquareMass_factorization,
                                                     pclCoreSquareMass_finiteBound
PRIME-CENTERED SQUARE MASS:                 PROVED   primeCenteredSquareMass_split,
                                                     primeCenteredSquareMass_le
FUF LARGE STRUCTURAL ROUTER:                PROVED   eq_one_or_prime_of_all_primeFactors_gt_sqrt,
                                                     largeUnmatchedFactor_unique,
                                                     fufLargeRouter_finite
PHYSICAL-SPLICE ABSTRACT BUDGET:            PROVED   akPhysicalSplice_of_suppliedBound,
                                                     akPhysicalSpliceBudget,
                                                     akPhysicalSplice_closes_of_margin
1/144 ENERGY EXPONENT ARITHMETIC:           PROVED   ak_energyMargin_exact
1/288 AMPLITUDE EXPONENT ARITHMETIC:        PROVED   ak_amplitudeMargin_exact
AK SPECTRAL TAX 7/144:                      PROVED   ak_largeCell_spectralTax_le

AK-GM-X012 ANALYTIC INTERFACE:              COMMENTS ONLY / OPEN
TYPED AK INTEGRATED KERNEL:                 NOT DECLARED / OPEN
CLEAN MIXED P*Pi>=V ANALYTIC PROMOTION:     NOT DECLARED
E_AK(L) ANALYTIC ESTIMATE:                  NOT DECLARED (external interface)
ANALYTIC CLAIMS BANKED:                     NONE
GATE 1B:                                    OPEN / UNCHANGED
FULL TYPE II / TWIN PRIMES:                 NOT DECLARED
```

Full report: `UNIVERSAL_V8_1_GATE1B_PHYSICAL_SPLICE_REPORT.md`.

---

## UNIVERSAL / GATE 1B v8.2 — SIGNED-PARENT / QK5 SAFE BANK

```
BUILD:                                      PASS   8406 jobs, 0 errors
SORRY / ADMIT / USER AXIOM:                 0 / 0 / 0
OLD BANK:                                   PRESERVED (0 deletions, new files only)

GENERIC FINSET ANOVA:                       PROVED   finset_prod_add_eq_sum_powerset,
                                                     mem_powerset_iff_subset,
                                                     card_sdiff_of_subset
FULL-NINE ANOVA ALGEBRA:                    PROVED   fullNine_anova, fullNine_anova_term,
                                                     fullNine_five_complement_four,
                                                     fullNine_defectOrder_card_table
PHYSICAL FULL-NINE SOURCE BRIDGE:           SOURCE_UNVERIFIED / OPEN
CRITICAL-FIVE PRODUCT GEOMETRY:             PROVED   criticalFive_product_split,
                                                     criticalFive_shell_rewrite
DEFECT-ORDER <=4 EXPONENT ARITHMETIC:       PROVED   defectOrder_le_four_C2OverX_margin,
                                                     defectOrder_four_C2OverX_eq_neg_one_ninth
ORDER-5 C^2/X TAX ARITHMETIC:               PROVED   defectOrder_five_C2OverX_eq_one_ninth
P4.4 FIVE-FACTOR PARTITION ENUMERATION:     PROVED   p44_only_320_has_hard_interior,
                                                     p44_320_has_hard_interior,
                                                     p44_320_upper_eq_seven_eighteenths
CRT / ADDITIVE RECIPROCITY:                 PROVED   crt_inverse_sum_eq_one_mod_product,
                                                     crt_inverse_sum_witness,
                                                     additive_reciprocity_rational_identity
PHYSICAL SHELL MOD-q IDENTITY:              PROVED   physicalShell_mod,
                                                     physicalShell_inverse_mod
RECIPROCITY ARCHIMEDEAN TAX:                PROVED   reciprocity_archimedean_tax_le_invX
UNIT-HYPERBOLA REINDEXING:                  PROVED   unitHyperbolaEquiv,
                                                     sum_unitHyperbola_eq_sum_units
KLOOSTERMAN-LIKE SCALING:                   PROVED   kLike_scale,
                                                     kLike_productSlot_reindex
SIGNED-PARENT ASYMMETRIC CAUCHY:            PROVED   asymmetricCauchy_left,
                                                     asymmetricCauchy_right
DOUBLE-CAUCHY CANCELLATION FIREWALL:        COUNTERMODEL
                                                     signedParent_zero_counterexample,
                                                     coefficientBlindEnergy_positive_counterexample,
                                                     doubleCauchy_can_destroy_exact_signed_cancellation
v8.1 HOMOGENEITY COMPATIBILITY:             PROVED   signedParentCounterexample_smul_energy
REINDEX-NOT-CONTRACTION GUARD:              PROVED   kLike_reindex_not_contraction
ABSTRACT CHARACTER DIAGONALIZATION:         PROVED   finiteCharacterDiagonalization_of_orthogonality
                                                     (orthogonality is an explicit hypothesis)
CONCRETE QK5 MCHAR DIAGONALIZATION:         OPEN

QK5-SIGNED-OUTER45:                         COMMENTS ONLY / OPEN
QK5-CCM9-HC45:                              COMMENTS ONLY / OPEN
QK5-BP-QCHAR-PARENT45:                      COMMENTS ONLY / OPEN
QK5-QCHAR-SAT45:                            COMMENTS ONLY / OPEN
FDLC-YANG5:                                 COMMENTS ONLY / OPEN
E(q) / Z_E(q) / KAPPA4:                     SOURCE FIELD MISSING
ANALYTIC CLAIMS BANKED:                     NONE
GATE 1B:                                    OPEN / UNCHANGED
FULL TYPE II / TWIN PRIMES:                 NOT DECLARED

VERDICT: ARISTOTLE_V8_2_GATE1B_SIGNED_PARENT_QK5_SAFE_BANK_PARTIAL
```

Full report: `UNIVERSAL_V8_2_GATE1B_SIGNED_PARENT_QK5_REPORT.md`.

---

## NANC / GATE 1A v9 — POSTDET / AMPLINE / SIGNED-PARENT SAFE BANK

```
BUILD:                                      PASS   8406 jobs, 0 errors
SORRY / ADMIT / USER AXIOM:                 0 / 0 / 0
OLD BANK:                                   PRESERVED (0 deletions, new files only)

PMLS_NORMALIZATION:                         PROVED   outerP_cauchy,
                                                     pmls_to_normalizedGateBudget,
                                                     gpmls_to_physicalGateBudget
GENERAL_COMPLEMENTARY_DIVISOR:              PROVED   complementary_deltaP_dvd,
                                                     complementary_m_eq,
                                                     complementary_m_ediv
M_FIBRE_ONE_ROOT:                           PROVED   complementary_m_unique
DOUBLE_DETERMINANT:                         PROVED   doubleDet_left, doubleDet_right,
                                                     doubleDet_conductorPair_unique
N_DELTA_PUSHFORWARD:                        PROVED   detMap_injective_of_crossDet_ne_zero,
                                                     injectivePushforward_l2,
                                                     nDelta_pushforward_l2
REDUCED_PLUCKER:                            PROVED   reducedPlucker_g_dvd_N,
                                                     reducedPlucker_left, reducedPlucker_right,
                                                     reducedPlucker_coprime_cd,
                                                     reducedPlucker_coprime_cn
REDUCED_CONDUCTOR:                          PROVED   reducedConductor_dvd,
                                                     reducedConductor_cSharp_dvd
FIRST_DELTA_ZERO:                           ROUTED   constantReducedConductor_impossible
HFIRST:                                     FAILED_ROUTE (anti-loop; nothing banked)
POSTDET_OMEGA:                              PROVED   postDetOmega_factorization
GENERIC_POSTDET_ZERO:                       PROVED UNDER EXPLICIT HYPOTHESES
                                                     postDet_zero_amplifier_match,
                                                     postDet_zero_generic_longDiagonal
                                                     (needs ell1 <> ell2', |h1| < ell2,
                                                      |delta| + |delta'| < ell1)
DELTA_LCM_FINITE_ROUTER:                    PROVED   hardDeltaPairs_card_le_divisorSquareSum
MAXIMAL_AMPLIFIER_BUDGET:                   PROVED   amplifier_budget_general,
                                                     amplifier_budget_maximal,
                                                     amplifier_spare_pays_familyTax_identity
AMPLIFIER_LINE:                             PROVED   complementarySolutions_parametrized
DELTA_ALONG_LINE:                           PROVED   deltaAlongLine_affine (+ primed)
AMPLINE_OMEGA_FIBRE2:                       PROVED   postDet_on_amplifierLines,
                                                     omegaLine_coeff_two, omegaLine_nonzero,
                                                     omegaLine_zeroFiber_card_le_two
FAMILY-INDEX FIREWALL:                      COUNTERMODEL  familyIndex_counterexample,
                                                     familyIndex_selection_not_lossless
SIGNED-PARENT FIREWALL:                     COUNTERMODEL  signedParent_child_not_parent
OPTIONAL RECIPROCAL-PRODUCT DFT:            OPTIONAL_FINITE_CHILD
                                                     reciprocalProductKernel_hilbertSchmidt

XQ-AMPLINE-SIGNED1A:                        OPEN / NO INHABITANT
XQ-POSTDET-AMP-LS1A:                        OPEN / NO INHABITANT
Gate1ADirectCleanP3Closed:                  OPEN / NO INHABITANT / NO DECLARATION
ANALYTIC CLAIMS BANKED:                     NONE
GATE1A DIRECT CLEAN-P3:                     OPEN
FULL TYPE II / TWIN PRIMES:                 NOT DECLARED

VERDICT: ARISTOTLE_GATE1A_V9_POSTDET_AMPLINE_BANK_COMPLETE
```

Full report: `UNIVERSAL_V9_GATE1A_POSTDET_AMPLINE_REPORT.md`.

---

## Gate 1A v9.1 — SOURCE-CERTIFICATE / WEIGHTED-ROOT / DEFECT-MULTIPLIER

```
ROOT MULTIPLIER ALGEBRA:            PROVED   rootMultiplier_rewrite,
                                             rootMultiplierKappa_eq_u_mul,
                                             rootMultiplierU_indep_q1
ROOT MULTIPLIER MOD CLEAN FACTOR:   PROVED   rootMultiplier_mod_cleanFactor
HARD DELTA UNIT ROUTER:             PROVED   hardDelta_isUnit_mod_cleanPrime,
                                             rootMultiplierU_isUnit_mod_cleanPrime
WEIGHTED ROOT ANALYSIS:             PROVED   rootAnalysis_sq_le,
                                             weightedRootAnalysis_of_fibreBound,
                                             weightedRootAnalysis_energy
RESIDUE-MASS -> ROOT-FIBRE:         PROVED   weightedRootFibre_of_residueMass
NONUNIT FIREWALL:                   COUNTERMODEL nonunitMultiplier_collapses_rootFibre
FINITE DEFECT MULTIPLIER:           PROVED   defectOp_character_eigen, dftHat_defectOp,
                                             dftHat_plancherel
FOURIER MULTIPLIER NORM:            PROVED   defectOp_energy_le_fourierSup,
                                             defectOp_of_multiplierBound
NO RAW FEJER l1 CLAIM:              COUNTERMODEL defectOp_l1_mass_not_canonical
COMBINED ROOTDEFECT BOUND:          PROVED   rootDefect_bilinear_bound
PROJECTIVE CROSSED CONVOLUTION:     PROVED   projectiveCrossedConvolution,
                                             projectiveCrossedConvolution_of_fibreCard
FIXED-QUOTIENT FINITE KERNEL:       PROVED   centeredQuotientKernel_withAmplitude

ROOTDEFECT-SOURCE-FACTOR1A:         INTERFACE OPEN / NO INHABITANT
ZERO-PROJ-SOURCE-SPLICE1A:          OPEN INTERFACE / NO INHABITANT
Gate1ACleanP3ClosureCertificate:    NOT CONSTRUCTED
ANALYTIC CLAIMS BANKED:             NONE
GATE1A DIRECT CLEAN-P3:             OPEN
FULL TYPE II / TWIN PRIMES:         NOT DECLARED

VERDICT: ARISTOTLE_GATE1A_V9_1_SOURCE_CERT_BANK_PARTIAL
```

Full report: `UNIVERSAL_V9_1_GATE1A_SOURCE_CERT_REPORT.md`.

---

## Gate 1A v9.2 — CORRECTED FIXED-QUOTIENT / S1

```
CORRECTED FIXED-QUOTIENT ROOT:      PROVED   correctedFixedQuotient_unique,
                                             CorrectedFixedQuotientData.root_unique
OLD/NEW CONGRUENCE FIREWALL:        COUNTERMODEL oldNew_congruence_not_interchangeable,
                                             oldNew_rootSets_differ
OLD/NEW COORDINATE ENERGY:          PROVED   oldNewQCoordinate_unitEquiv,
                                             oldNewQCoordinate_l2Preserved,
                                             oldNewQCoordinate_card_preserved
CORRECTED S1 CLOSED FORM:           PROVED   correctedS1_closed_form
CORRECTED QUOTIENT FOURIER:         PROVED   correctedQuotient_fourier,
                                             correctedQuotient_crt_phase
CRT SIGN CONVENTION:                PINNED   correctedQuotient_authoritative_match (c = -2)
                                             correctedQuotient_match_c_two (q-factor only)
NORMALISATION:                      PROVED   Uq_div_q (Uq = q/H)
RECIPROCAL FORM:                    COUNTERMODEL Uq_ne_reciprocal_of_ne
FULL SOURCE TRANSCRIPTION:          NOT CLAIMED
GATE1A:                             OPEN
```

Full report: `UNIVERSAL_V9_2_GATE1A_FINAL_SOURCE_CLOSURE_REPORT.md`.

---

## Gate 1A v9.3 — BPP / CRT SCOPE AUDIT

```
SCOPE AUDIT ONLY — NO NEW DECLARATIONS
CRT SIGN CONVENTION:                PINNED (c = -2)
NORMALISATION:                      Uq = q/H
COORDINATE CHANGE:                  l2-NEUTRAL
BPP PARTICIPATION:                  INTERFACE OPEN (no axiom)
DIRECT R1 WEIGHTED PROMOTION:       RETRACTED
OLD MARGIN LEDGER (1/12,1/9,5/48):  RETRACTED
GATE1A:                             OPEN
```

Full report: `UNIVERSAL_V9_3_GATE1A_BPP_CRT_SCOPE_REPORT.md`.

---

## Gate 1A v9.4 — CORRECTED BPP BANK

```
PRIME PARTICIPATION (finite part):  PROVED   participation_of_plateau, sup_le_envelope
FAMILY ENERGY:                      PROVED   envelopeMass_le_of_participation,
                                             familyEnergy_of_participation,
                                             PrimeParticipationCertificate.familyEnergy
CORRECTED BPP MARGINS:              PROVED   bpp_gate_margin_V1 = 1/72
                                             bpp_gate_margin_V2 = 1/24
                                             bpp_gate_margin_V3 = 1/32
OBSOLETE MARGINS:                   RETRACTED obsolete_margins,
                                             ledgers_not_interchangeable
RECOMBINATION ERROR:                PROVED   recombinationError_U2_budget
U1 ERROR MARGIN:                    FAILS    errorMarginU1_fails_at_V2
PB ONE-SIDED BUDGET:                PROVED   pb_oneSided_budget_eq_one
ONE-ROOT -> OPERATOR:               PROVED   oneRoot_energy_to_operator (R^{-1/4})
DIRECT R1 PROMOTION:                COUNTERMODEL directR1_promotion_countermodel(_general)
POSITIVE ROW ENLARGEMENT:           PROVED   cleanP3_energy_le_esharp_energy,
                                             cleanP3_energy_le_of_esharp_bound
                                    ONE-WAY  rowEnlargement_not_reversible
PB UNIT REPAIR:                     PROVED   klSum_unit_scaling, pbQFrequency_unitRepair,
                                             pbQFrequency_normPreserved
                                    GUARD    pbQFrequency_repair_not_identity
SMOOTH-R ENVELOPE:                  PROVED   coeff_lipschitz,
                                             SmoothEnvelopeCertificate.variation_bound
                                    COUNTERMODEL commonSource_not_rIndependent
PROJECTIVE CLOSURE:                 PROVED   outerProjectiveCollision_iff_dvd_deltaOut,
                                             projAxis_correlation (= s^2*1_{U=U'} - s,
                                             EXACT identity, NOT a Weil bound)
QUOTIENT RECOMBINATION:             PROVED   packetEnergy_split, source_energy_le
                                    GUARD    packetEnergy_split_factor_needed
FIXED-STATE EXCLUSION:              PROVED   excluded_card_le, exists_admissible
                                    GUARD    rDependent_obstruction_excludes_everything
SECTOR TABLE:                       PROVED   sectorStatus_not_all_banked,
                                             genericFullConductor_analyticOpen,
                                             projective_sourceInterfaceOpen
CLOSURE COMPILER:                   PROVED   Gate1ACleanP3ClosureCertificate.toFinalBudget
AllMSourceExhaustivenessCertificate:NOT CONSTRUCTED
Gate1ACleanP3ClosureCertificate:    NOT CONSTRUCTED
ANALYTIC INTERFACES:                COMMENTS ONLY (AnalyticInterfacesV94.lean, 0 decls)
GATE1A CLEAN-P3:                    OPEN
GATE1B:                             UNCHANGED
FULL TYPE II / TWIN PRIMES:         NOT DECLARED

VERDICT: ARISTOTLE_GATE1A_V9_4_BANK_PARTIAL
```

Full report: `UNIVERSAL_V9_4_GATE1A_CORRECTED_BPP_REPORT.md`.

---

## Gate 1A v9.5 — ALL-m PACKET EXHAUSTIVENESS

```
PACKET CENSUS:                      19 ENTRIES  census_nodup
NOT ALL CLASSIFIED:                 PROVED   census_not_all_classified
FIRST UNCLASSIFIED PACKET:          edgeDependentD2
                                    (RequestProject/CenteredCRTRootNormalForm.lean,
                                     bilinearLargeSieve, edgeDependent, mult. none,
                                     target gate1A_ML4overH)
                                    firstUnclassified_is_edgeDependentD2,
                                    firstUnclassified_weightDependence,
                                    firstUnclassified_target
MULTIPLICITY NOT CONTROLLED:        PROVED   multiplicity_not_fully_controlled
HIGH-P3 OPERATORS UNROUTED:         PROVED   multiple_highP3_operators_unrouted
WEIGHT FIREWALL:                    PROVED   edgeDependent_not_common,
                                             finiteTemplate_nuclear_cost, weight_norm_le
MULTIPLICITY LEDGER:                PROVED   multiplicity_energy_le,
                                             PacketMultiplicityCertificate.energy_le
                                    GUARD    multiplicity_not_from_injectivity
E-SHARP SCOPE (P3-FREE):            PROVED   ESharpGenericIsP3Free,
                                             genericBound_depends_only_on_esharpData,
                                             cleanP3_controlled_of_generic
ASSEMBLY:                           PROVED   actualSource_eq_generic_add_exceptions,
                                             no_silent_double_counting,
                                             genericPackets_nuclearAssembly
                                    GUARD    localRepair_does_not_imply_targetClosed
CLOSURE COMPILERS:                  PROVED   allM_packet_exhaustive,
                                             Gate1AAllMClosureCertificate.toTarget,
                                             Gate1ACleanP3ClosureCertificateV95.toTarget
TARGET BRIDGE:                      PROVED   gate1A_target_bridge,
                                             commonD2_target_eq_ML4_over_H
UNINHABITED (open fields):          SourceExactPacketDictionary, GenericBPPBound,
                                    AllMExhaustiveness, Gate1AAllMClosureCertificate,
                                    Gate1ACleanP3ClosureCertificateV95
ALL-m EXHAUSTIVENESS:               NOT ESTABLISHED
GATE1A CLEAN-P3 / ALL-m:            OPEN
GATE1B:                             UNCHANGED
FULL TYPE II:                       NOT DECLARED / NOT INFERRED
TWIN PRIMES:                        NOT DECLARED / NOT INFERRED

VERDICT: ARISTOTLE_GATE1A_V9_5_ALLM_BANK_PARTIAL
```

Full report: `UNIVERSAL_V9_5_GATE1A_ALLM_EXHAUSTIVENESS_REPORT.md`.

---

## v9.6 — Gate 1A actual-source inhabitance (append only)

```
ACTUAL W_{D,e}:                     ARBITRARY EDGE DEPENDENT
                                    actualWeightVerdict, actualWeightSourcePath
                                    (CenteredCRTRootNormalForm.lean ::
                                     EdgeDependentD2Data.coeff)
SOURCE CONSTRAINS NOTHING:          PROVED   edgeData_coeff
EDGEDEPENDENT-D2 -> E-SHARP:        REFUTED  template_count_ge_of_linearIndependent,
                                             deltaEdgeData_linearIndependent,
                                             deltaEdgeData_no_small_template,
                                             finiteTemplateCertificate_delta_card
FINITE TEMPLATE (COMMON ONLY):      PROVED   commonFiniteTemplate,
                                             commonFiniteTemplate_cost
SOURCE LOCATORS (COMPILE-TIME):     PROVED   V96SourceLocators #check block,
                                             sourceDecl_ne_empty
SOURCE-KIND CENSUS:                 PROVED   commonD2_is_the_only_dictionary_ready_packet,
                                             edgeDependentD2_is_dataOnly,
                                             interfaceOnlyPackets_length = 12,
                                             majority_of_packets_are_interfaces,
                                             first_non_dictionary_ready
VACUITY AUDIT (free fields):        PROVED   sourceDictionary_inhabited_for_every_source,
                                             genericBPPBound_vacuously_inhabited,
                                             genericBPP_says_nothing_about_other_energy,
                                             esharpAdapter_nonempty_iff,
                                             cleanP3Certificate_self_referential
PINNED ACTUAL DICTIONARY:           CONSTRUCTED commonD2Dictionary,
                                             commonD2Dictionary_pins,
                                             commonD2Dictionary_contribution
SOURCE PARTITION IDENTITY:          PROVED   commonD2_source_partition
PACKET MULTIPLICITY (commonD2):     PROVED   commonD2Multiplicity,
                                             commonD2Multiplicity_exact  (= 1)
PACKET MULTIPLICITY (interfaces):   SOURCE MISSING
ROOTDEFECT SOURCE FACTORIZATION:    CONSTRUCTED canonicalRootDefect (canonical),
                                             rootDefect_hardParent_unique;
                                             pinning to actual hard parent OPEN
ZERO-PROJ SOURCE FACTORIZATION:     CONSTRUCTED canonicalZeroProjective (canonical),
                                             zeroProjective_sourceCoeff_unique;
                                             trivial fibre multiplicity, pinning OPEN
CLEAN-P3 CLOSURE CERTIFICATE:       CONSTRUCTED CONDITIONALLY
                                             cleanP3Certificate_of_bound,
                                             cleanP3Certificate_physical_target
ALL-m EXHAUSTIVENESS (commonD2):    CONSTRUCTED CONDITIONALLY commonD2Exhaustiveness
ALL-m CLOSURE (commonD2):           CONSTRUCTED CONDITIONALLY commonD2Closure,
                                             commonD2Closure_bound,
                                             commonD2Closure_finalTarget_is_trivial
                                             (triangle-inequality target only)
ALL-m EXHAUSTIVENESS (full census): NOT CONSTRUCTED  allM_still_blocked
GENERIC BPP ANALYTIC INHABITANT:    ABSENT
LAYER FIREWALL:                     PROVED   layers_not_collapsed,
                                             no_unconditional_closure, v96_not_complete
GATE1A CLEAN-P3:                    ANALYTICALLY CONDITIONAL
GATE1A ALL-m:                       SOURCE-EXHAUSTIVENESS OPEN
GATE1B:                             UNCHANGED
FULL TYPE II:                       NOT INFERRED
TWIN PRIMES:                        NOT INFERRED

VERDICT: ARISTOTLE_GATE1A_V9_6_ACTUAL_SOURCE_PARTIAL
```

Full report: `UNIVERSAL_V9_6_GATE1A_ACTUAL_SOURCE_INHABITANCE_REPORT.md`.

---

## NANC Gate 1A v9.8 — canonical Direct all-`m` common-weight bank (append-only)

Files added (all new, append-only, under
`RequestProject/NANC/Gate1A/SafeExtensions/`):
`V98CanonicalDirectSource.lean`, `V98CanonicalAllMRows.lean`,
`V98DirectEnergyPin.lean`, `V98BPPProvenance.lean`, `V98DirectClosure.lean`,
`V98Gate0ScopeSplit.lean`, `V98Status.lean`.
No v9–v9.7 file was edited, renamed, deleted or restated.

```
AUTHORITATIVE DIRECT SOURCE:      PINNED    Gate1ADirectCanonicalSource, ctilde_def
                                            (provenance sourceInspectedNotProved)
PHYSICAL W_D:                     COMMON    gate1A_direct_physicalWeight_common,
                                            covariance_eq_weight_pairing,
                                            exists_rowDependent_weight_not_common
CANONICAL ALL-m ROW FAMILY:       CONSTRUCTED Gate1ADirectAllMRow (= ESharpRow),
                                            exists_allMRow_not_cleanP3
DETERMINANT IDENTITY:             PROVED    Fibre.direct_determinant_identity
                                            ((m+kr)A_e - m B_e = 2k)
GATE1A DIRECT ENERGIES:           CONSTRUCTED Gate1ADirectPacket.normalizedEnergy,
                                            gate1ADirectAllMPhysicalEnergy
TARGET BRIDGE:                    PROVED    directTarget_bridge,
                                            physical_of_normalized_bound
BPP ENERGY PIN:                   INTERFACE  Gate1ADirectBPPEnergyPin (UNINHABITED),
                                            energyPin_not_automatic,
                                            energyPin_not_implied_by_conclusion,
                                            energyPin_nonempty_iff
BPP FINITE COMPILER:              PROVED    primeParticipation_familyEnergy
                                            (E_off <= D*S/P^2 * T_abs)
BPP EXTERNAL ANALYTIC INPUT:      EXTERNAL   Gate1ABPPPrimeParticipationInput,
                                            provenance externallyPublished;
                                            NOT formalised in Lean
SMOOTH SEPARATION TEMPLATES:      INTERFACE  SmoothSeparationCertificate;
                                            canonicalWeight_finiteTemplate proved
FAMILY ENERGY / ONE ROOT:         PROVED    familyEnergyExp_eq = -1/2,
                                            oneRoot_exponent = -1/4, oneRoot_real
MARGINS V1 V2 V3:                 1/72, 1/24, 1/32  (frozen v9.4 ledger reused)
U^-2 RECOMBINATION:               PROVED    directRecombinationError_U2,
                                            margins 1/18, 1/18, 1/24
CLEAN-P3:                         COROLLARY cleanP3_of_allM_bound
CLOSURE COMPILER:                 CONDITIONAL Gate1ADirectClosureCertificate,
                                            toCanonicalStatement,
                                            closureCertificate_nonempty_iff
EDGEDEPENDENT-D2:                 GATE 0 ADAPTER OBLIGATION
                                            edgeDependentD2_is_gate0_adapter_obligation
                                            (datum itself untouched)
ROOTDEFECT FACTORISATION:         SECONDARY OPEN  rootDefect_is_secondary_route
GATE0 -> GATE1A COMPILER:         OPEN      Gate0.gate0Exhaustiveness_not_definitional,
                                            gate1ADirect_closure_independent_of_gate0
GATE1A DIRECT ALL-m LEAN STATUS:  EXTERNAL-UNINHABITED
GATE1B:                           UNCHANGED
FULL FM TYPE II:                  OPEN / UNINHABITED
TWIN PRIMES:                      NOT PROVED

VERDICT: ARISTOTLE_GATE1A_V9_8_DIRECT_ALLM_CLOSURE_REPORT
```

Full report: `UNIVERSAL_V9_8_GATE1A_DIRECT_ALLM_PERMANENT_CLOSURE_REPORT.md`.

---

## GATE 1B v8.2 — CUMULATIVE SAFE FORMAL BANK (append-only)

```
LAYER                             STATUS     LEAN EVIDENCE
--------------------------------  ---------  ------------------------------------
PERMUTATION / TWIST ENERGY        PROVED     Universal.SafeAlgebra.squareTwist_l2Energy,
                                             squareTwist_gram_bound
PRODUCT ENERGY (labelled boxes)   PROVED     l2Energy_pi_product,
                                             l2Energy_product_of_injective
                                             (+ needs_injective countermodel)
CRITICAL-FIVE EXPONENTS           PROVED     defectEnergyExponent, order 4 = -1/9,
                                             order 5 = +1/9, neg_iff_le_four
KAPPA4 NORMALISATION              PROVED     kappa4_over_kappa2_eq_two_sevenths = 2/7
2-ADIC SOURCE GUARD               PROVED     odd_mul_not_modEq_neg_two_mod_even
                                             (count empty; E NOT determined)
B NON-UNIT GUARD                  PROVED     not_dvd_of_shell_congr
SQUAREFREE ROUTER                 PROVED     squarefree_router_dichotomy
D12 CRT SLOT                      PROVED     d12_exists_unique, d12_spec_left/right
D12 PUSHFORWARD FACTORISATION     PROVED     d12Pushforward_l1_factor / _l2_factor
FINITE KLOOSTERMAN INTERFACE      TIER 2     AdditiveCharacterSystem (supplied)
KLOOSTERMAN UNIT SCALING          PROVED     kloosterman_scale
KLOOSTERMAN SQUARE MASS           PROVED     kloosterman_squareMass = q * phi(q)
                                             (no Weil bound claimed)
TWISTED CRT FACTORISATION         TIER 2     kloosterman_mul_coprime_twisted
RAMANUJAN UNIT BASELINE           PROVED     ramanujan_fourier,
                                             unit_indicator_baseline
GCD TWIST UNITARITY               PROVED     gcdTwistFamily_energy / _gram_bound
GCD SCHUR CAPACITY                PROVED     gcdSchurCapacity (weighted Schur reuse)
GCD-BETA SOURCE MASS CAPACITY     PROVED     gcdBetaMass_of_strata_bounds
SEVEN-BOX ENERGY                  PROVED     sevenBoxEnergy_factor
GLOBAL ZERO MODE                  PROVED     centeredResidue_eq_zeroMode_add_nonzero,
                                             nonzeroPart_independent_expectedTerm
QK5 CAPACITY MARGINS              PROVED     PV -1/2 -> X^-1/18; overlap -1/6 ->
                                             X^-1/54; axis X^-1/9 (exact Q)
COUNTERMODELS A-E                 PROVED     CountermodelsV82
CAPACITY COMPILERS                CONDITIONAL pvMedium_of_analyticHyp, axisBudget_of_axisBound,
                                             gcdBudget_of_sourceMassAndSchur
ZERO-MODE COMPILER                CONDITIONAL zeroModeCompiler_of_E_eq_MT
ABSTRACT REASSEMBLY               CONDITIONAL reassemble_of_face_certificates
                                             (no face certificate inhabited)
QK5 ANALYTIC INTERFACES           OPEN       QK5InterfacesV82 (comments only)
GATE1B:                           NOT CLOSED
FULL TYPE II:                     NOT INFERRED
TWIN PRIMES:                      NOT INFERRED

VERDICT: ARISTOTLE_V8_2_GATE1B_CUMULATIVE_SAFE_BANK_PARTIAL
```

Full report: `UNIVERSAL_V8_2_GATE1B_CUMULATIVE_SAFE_BANK_REPORT.md`.

---

## GATE 1B v8.3 — HIGH-ORDER REGROUP / CHARACTER SAFE BANK (append-only)

```
ITEM                              STATUS      LEAN WITNESS
HIGH-ORDER REGROUP GEOMETRY       PROVED      regroupBExponent_eq_seven (j ≤ 7 ⟹ 7),
                                              hasTwoModels_of_order_le_seven,
                                              orderEight_oneModel, orderNine_noModel
GENERIC SHELL REGROUP             PROVED      shell_regroup_twoModels,
                                              shell_regroup_order5/6/7
H6 EXACT REGROUP                  PROVED      h6_shell_regroup, h6_congruence,
                                              h6_congruence_modEq, h6_ell_unique
H7 2D REGROUP                     PROVED      h7_qk5_shell, h7_qk5_congruence
H7 1D RECIPROCAL SHELL            PROVED      h7_rf1d_shell, h7_rf1d_congruence
H8 1D RECIPROCAL SHELL            PROVED      h8_rf1d_shell, h8_rf1d_congruence
H9 PURE-DEFECT SHELL              PROVED      h9_shell, h9_shell_congruence,
                                              h9_qell_coprime(_shell)
FINITE-FIBRE PUSHFORWARD ENERGY   PROVED      l2_pushforward_le_fiber_card_mul,
                                              l2_pushforward_product_le
H6/H7 SOURCE ENERGY COMPILER      CONDITIONAL h6Energy_of_fiberBound (explicit fibre
                                              bound), h7Energy_exact
FINITE MUL-CHARACTER SYSTEM       TIER 2      MulCharSystem (supplied),
                                              character_fourier_inversion,
                                              character_parseval
RECIPROCAL PHASE EXPANSION        PROVED      gauss_twist, reciprocal_addChar_fourier,
                                              reciprocal_phase_character_expand,
                                              reciprocal_phase_expand_shift_two
H7/H8 PACKET FACTORISATION        PROVED      h7_characterPacket_factor,
                                              h8_characterPacket_factor
H9 NONPRINCIPAL PACKET            PROVED      unit_residue_indicator_character_expand,
                                              h9_nonprincipal_character_packet,
                                              h9_packet_of_factorisation
SAME-q CHARACTER EXPANSION        PROVED      kloostermanCharSum_eq (τ² χ(b) χ(t)),
                                              sameQ_character_expand
SAME-q GRAM EXPANSION             PROVED      sameQ_gram_expand, dualCorrelation
SAME-q ≠ RESIDUE ENERGY           COUNTERMODEL sameQ_gram_eq_gramForm,
                                              sameQ_not_function_of_residueEnergy,
                                              sameQ_ne_residueEnergy_counterexample
NINE-FACTOR GRAM COMPILER         CONDITIONAL SameQNineFactorData,
                                              sameQ_of_nuclear_factorisation
                                              (interface, not inhabited)
BULK-SPIKE FINITE INEQUALITIES    PROVED      bulk_bound, spike_l1_bound,
                                              spike_weighted_bound,
                                              spike_card_l1_bound,
                                              spike_l2_card_bound, bulkSpike_bound
D12 BULK-SPIKE CAPACITY           CAPACITY    d12_rms_exponent = 1,
                                              d12_sup_over_rms_exponent = 5/6,
                                              d12_bulkSpike_loss_exponent = 5/12,
                                              bulkSpike_balance_exponent
TIER-3 ZERO RESIDUAL              PROVED      historical_eq_canonical_sub_residual,
                                              expectedTerm_not_freely_choosable
HIGH-ORDER ROUTING TABLE          BOOKKEEPING highOrderStatus (no "closed" constructor),
                                              highOrderStatus_analytic_open
COUNTERMODELS A-D (v8.3)          PROVED      CountermodelsV83
V8.3 ANALYTIC INTERFACES          OPEN        V83HighOrderInterfaces (comments only)
ANALYTIC H7 / H8 / H9:            OPEN
SAME-q ANALYTIC MOMENT:           OPEN
D12 MOVING-D MOMENT:              OPEN
S2 SIEGEL-WALFISZ APPLICATION:    OPEN / EXTERNAL
R_E SOURCE BOUND:                 OPEN / SOURCE INTERFACE
GATE1B:                           OPEN / UNCHANGED
FULL TYPE II:                     NOT DECLARED
TWIN PRIMES:                      NOT DECLARED

BUILD: PASS (8495 jobs, 0 errors) · SORRY: NONE · USER AXIOMS: NONE
V8.1 / V8.2 BANKS: PRESERVED (append-only; no existing proof modified)

VERDICT: ARISTOTLE_V8_3_GATE1B_HIGHORDER_CHARACTER_SAFE_BANK_PARTIAL
```

Full report: `UNIVERSAL_V8_3_GATE1B_HIGHORDER_CHARACTER_SAFE_BANK_REPORT.md`.
