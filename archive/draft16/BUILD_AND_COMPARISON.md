# Build report and ledger comparison

## 1. Build report

* Toolchain: `leanprover/lean4:v4.28.0`, Mathlib `v4.28.0`.
* Exact command:

  ```bash
  lake build
  ```

* Result: **`Build completed successfully (8041 jobs).`**
  (The only message is a benign `manifest out of date` warning about the Mathlib
  dependency source kind; it does not affect the build.)
* No `sorry`, `admit`, `axiom`, or `implemented_by` in any project file
  (`rg` over `RequestProject/` returns only occurrences inside doc comments).
* Axiom check of representative machine-checked theorems (`#print axioms`) lists
  only `propext`, `Classical.choice`, `Quot.sound` (and the purely propositional
  `status_distinctions_consistent` depends on no axioms at all).

### Files created or modified

| File | Role |
|---|---|
| `RequestProject/Status.lean` | `ProofStatus` datatype + machine-readable `ledger` (updated) |
| `RequestProject/Parameters.lean` | `Params`, `oldWedge`, `newWedge`, `gap`, `sigmaSplit` |
| `RequestProject/Wedge206274.lean` | old-wedge algebra (preserved, subsumed) |
| `RequestProject/Wedge122162.lean` | §12.1–§12.2 / §13.2–§13.3 widened wedge + splitting exponent |
| `RequestProject/WrightExponentAudit.lean` | §12.4 Wright exponent inequalities |
| `RequestProject/SectorPartition.lean` | §12.5–§12.6 sector partition + implications |
| `RequestProject/DoubleCrossArithmetic.lean` | §6/§13 modular core (coprimality, CRT) |
| `RequestProject/MesoscopicParameters.lean` | §13.6 finite-product bound |
| **`RequestProject/RoutingThreshold.lean`** | **§13.1 routing threshold `w*(μ)` + equivalence (new)** |
| **`RequestProject/FixedDepthConvolution.lean`** | **§13.4 coefficient-majorant + fixed-depth divisor bound (new)** |
| **`RequestProject/FixedDepthRouting.lean`** | **§13.5 exact routing reindexing + `λ^{(j)}` divisor bound (new)** |
| **`RequestProject/F1Migration.lean`** | **§7/§8/§13.6 routable F1 migration interface (new)** |
| `RequestProject/DependencyInterfaces.lean` | §14 analytic interfaces; routed-F3 kernel-vs-piece split; §13.7 status distinctions (updated) |
| `RequestProject/Banking.lean` | top-level aggregator; preserved `Superseded` layer; routing summary (updated) |
| `LEDGER.md` | updated master ledger |
| `DEPENDENCY_GRAPH.md` | Mermaid + plain-text DAG (updated) |

## 2. Theorem/status comparison (previous ledger vs this update)

| Label | Previous ledger | This update |
|---|---|---|
| `F3_FIXED_DEPTH_ROUTING` | OPEN_INPUT | `F3_FIXED_DEPTH_ROUTABLE_SECTOR_PROVED` — EXTERNALLY_AUDITED + LEAN_PROVED_CORE |
| `LONG_MOBIUS_F1_MIGRATION_THEOREM` | OPEN_INPUT | `LONG_MOBIUS_F1_MIGRATION_ROUTABLE_PROVED` — EXTERNALLY_AUDITED + LEAN_PROVED_CORE |
| high-conductor vs full piece | conflated (`RATIO_SPLIT_WRIGHT_WEDGE_PROVED`) | split: `HIGH_CONDUCTOR_COMPONENT_POWER_SAVING` (power) vs `FULL_ROUTED_PIECE_LOG_SAVING` (log) |
| whole routed piece power saving | implicitly claimed | `FULL_ROUTED_PIECE_POWER_SAVING_REFUTED_AS_STATED` — REFUTED |
| routing threshold | (not present) | `ROUTING_THRESHOLD_W_STAR` — LEAN_PROVED (`w*(μ)=(40+61μ)/81`) |
| fixed-depth reindexing / convolution | (not present) | `FIXED_DEPTH_ROUTING_REINDEX`, `FIXED_DEPTH_CONVOLUTION_MAJORANT` — LEAN_PROVED |
| exact next wall | `F3_FIXED_DEPTH_ROUTING` / `HYBRID_MQ...` | `TWO_OUTER_VARIABLE_F3_KERNEL` — OPEN_INPUT |
| global-orientation Wright widening | (not present) | `GLOBAL_ORIENTATION_WRIGHT_WIDENING_FAILED` — REFUTED |
| mesoscopic-lemma-alone F1 | (not present) | `MESOSCOPIC_LEMMA_ALONE_DOES_NOT_SOLVE_F1` — REFUTED |
| pre-Poisson diagonal / double-cross / KF wedge | SUPERSEDED (already) | unchanged (SUPERSEDED_BY_LATER_AUDIT) |

## 3. Theorem inventory by status

### Newly Lean-proved in this update
`routing_threshold_equiv`, `newWedge_iff_wStar`, `wStar_mono`, `wStar_zero`,
`wStar_zero_lt_half`, `maj_mul`, `maj_one`, `maj_finset_prod`, `maj_fixed_depth`,
`routing_reindex`, `routing_reindex_apply`, `routedCoeff_divBounded`,
`block_routable_iff`, `F1RoutableHyp.wedge_holds`,
`long_mobius_f1_migration_routable`, `ultrashort_product_bound`,
`full_f1_migration_conditional`, `f3_fixed_depth_kernel_power_saving`,
`f3_fixed_depth_routable_full_piece`, `status_distinctions_consistent`,
`banking_routing_summary`.

### Previously Lean-proved (preserved)
`wedge_containment_206_implies_122`, `splitting_parameter_122_162`,
`fixed_factor_identity/le`, `oldWedge_sigma_feasible_iff`,
`wright_term_one/two`, `wright_cube/seventh_mono`,
`sectors_exhaustive`, `sector_partition_exhaustive_disjoint`,
`double_cross_residual_coprime`, `primepower_parts_coprime`,
`crt_residual_collapse_core`, `crt_lift_independence`,
`mesoscopic_finite_product_bound(')`, and the remaining §12 inequality chain.

### Lean conditional interfaces (Method A/B, from explicit hypotheses)
`ratio_split_wright_wedge`, `ratio_split_wright_wedge_of_oldWedge`,
`mesoscopic_mobius_admissible`, `f3_fixed_depth_kernel_power_saving`,
`f3_fixed_depth_routable_full_piece`, `long_mobius_f1_migration_routable`,
`full_f1_migration_conditional`, and the preserved `Superseded.*` interfaces.

### Externally audited (analytic, not fully Lean-formalized)
`CW_MU_CONDUCTOR_WINDOW_BANKED`, `F3_R2_BD_REDUCTION`, `F3_R2_MAIN_TERM_KILLED`,
`LOW_MID_CONDUCTORS_CONTROLLED`, `ACTUAL_KF_DIAGONAL_PROVED`,
`KF_OFFDIAG_CROSSCOPRIME_PROVED`, `COMPLETE_DOUBLE_CROSS_PHASE_FACTORIZED`,
`ONE_MODULUS_FOURIER_SEPARATION`, `FOURIER_LOSS_DM_SQRT`,
`ACTUAL_KF_TINY_WEDGE_CORRECTED`, `RATIO_SPLIT_WRIGHT_WEDGE_PROVED`,
`ACTUAL_KF_WEDGE_122_162`, `F3_R2_HIGH_CONDUCTOR_POWER_SAVING`,
`F3_R2_PARTIALLY_KILLED_WIDENED`, `F3_FIXED_DEPTH_ROUTABLE_SECTOR_PROVED`,
`HIGH_CONDUCTOR_COMPONENT_POWER_SAVING`, `FULL_ROUTED_PIECE_LOG_SAVING`,
`LONG_MOBIUS_F1_MIGRATION_ROUTABLE_PROVED`,
`MESOSCOPIC_MOBIUS_LEMMA_ADMISSIBLE_Q`; with LEAN_PROVED_CORE for
`DOUBLE_CROSS_PRIMEPOWER_EXTRACTION`, `RESIDUAL_COLLAPSE_PROVED`,
`F3_FIXED_DEPTH_ROUTABLE_SECTOR_PROVED`, `LONG_MOBIUS_F1_MIGRATION_ROUTABLE_PROVED`.

### Open inputs
`TWO_OUTER_VARIABLE_F3_KERNEL` (exact next wall),
`F3_SINGLE_OUTER_UNROUTABLE_CORE`, `FULL_F1_MIGRATION_OPEN`,
`F1_ULTRASHORT_AGGREGATE_MAIN_TERM`, `F1_ULTRASHORT_OFFDIAGONAL`,
`HYBRID_MQ_KLOOSTERMAN_LARGE_SIEVE`, `BALANCED_TII_CORE`, `PARITY_OPEN`.

### Refuted
`ABSTRACT_POISSON_DIAGONAL_FALSE`, `ABSOLUTE_BD_REFUTED`,
`FALSE_MPAIR_ONE_OVER_G_REFUTED`, `UNRESTRICTED_Q_MESOSCOPIC_FALSE`,
`GLOBAL_ORIENTATION_WRIGHT_WIDENING_FAILED`,
`FULL_ROUTED_PIECE_POWER_SAVING_REFUTED_AS_STATED`,
`MESOSCOPIC_LEMMA_ALONE_DOES_NOT_SOLVE_F1`.
