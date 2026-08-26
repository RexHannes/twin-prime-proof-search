# Dependency graph — Shifted Möbius Type-II / F3

Status legend: **[A]** externally audited, **[L]** Lean-proved (or Lean algebraic
core), **[C]** conditional interface / bridge, **[O]** open input, **[R]** refuted.

```mermaid
graph TD
  BD["F3_R2_BD_REDUCTION [A]"]
  MT["F3_R2_MAIN_TERM_KILLED [A]"]
  LM["LOW_MID_CONDUCTORS_CONTROLLED [A]"]
  DIAG["ACTUAL_KF_DIAGONAL_PROVED [A]"]
  CROSS["KF_OFFDIAG_CROSSCOPRIME_PROVED [A]"]

  PPE["DOUBLE_CROSS_PRIMEPOWER_EXTRACTION [A/L]"]
  RC["RESIDUAL_COLLAPSE_PROVED [A/L]"]
  PHASE["COMPLETE_DOUBLE_CROSS_PHASE_FACTORIZED [A]"]
  FOUR["ONE_MODULUS_FOURIER_SEPARATION + FOURIER_LOSS_DM_SQRT [A]"]
  DC["double-cross sector"]

  PART["ratio-split sector partition I/II/IIIa/IIIb [L]"]
  WRIGHT["Wright five-term estimate [A]"]
  WEDGE["RATIO_SPLIT_WRIGHT_WEDGE_PROVED (122μ+162θ<1) [A]"]
  KILL["F3_R2_PARTIALLY_KILLED_WIDENED [A]"]

  BD --> MT
  BD --> LM
  BD --> DIAG
  BD --> CROSS
  BD --> DC
  PPE --> DC
  RC --> DC
  PHASE --> DC
  FOUR --> DC
  DC --> PART
  PART --> WRIGHT
  MT --> WEDGE
  LM --> WEDGE
  DIAG --> WEDGE
  CROSS --> WEDGE
  WRIGHT --> WEDGE
  WEDGE --> KILL

  %% fixed-depth routing + full-vs-kernel split (this update)
  HCK["HIGH_CONDUCTOR_COMPONENT_POWER_SAVING [A]"]
  ROUTE["routing threshold w*(μ)=(40+61μ)/81 [L]"]
  REIDX["fixed-depth routing reindex λ^{(j)}=γ·∏ψ [L]"]
  FULLP["FULL_ROUTED_PIECE_LOG_SAVING [A]"]
  FDR["F3_FIXED_DEPTH_ROUTABLE_SECTOR_PROVED [A/L]"]
  KILL --> HCK
  ROUTE --> FDR
  REIDX --> FDR
  HCK --> FDR
  MT --> FULLP
  LM --> FULLP
  HCK --> FULLP
  FULLP --> FDR
  FRPS["FULL_ROUTED_PIECE_POWER_SAVING_REFUTED_AS_STATED [R]"]
  FRPS -.only log saving for whole piece.-> FULLP

  %% refuted siblings
  ABSPD["ABSTRACT_POISSON_DIAGONAL_FALSE [R]"]
  ABSBD["ABSOLUTE_BD_REFUTED [R]"]
  FMP["FALSE_MPAIR_ONE_OVER_G_REFUTED [R]"]
  ABSPD -.refutes stronger form.-> DIAG
  ABSBD -.forbids abs-value in q.-> BD
  FMP -.corrects pair count.-> DC
```

```mermaid
graph TD
  MES["MESOSCOPIC_MOBIUS_LEMMA_ADMISSIBLE_Q [A]"]
  FDR2["F3_FIXED_DEPTH_ROUTABLE_SECTOR_PROVED [A/L]"]
  MIG["LONG_MOBIUS_F1_MIGRATION_ROUTABLE_PROVED [A/L]"]
  FULLMIG["FULL_F1_MIGRATION_OPEN [O]"]
  CORE["F1_ULTRASHORT_CORE_REDUCTION [C]"]
  AGG["F1_ULTRASHORT_AGGREGATE_MAIN_TERM [O]"]
  OFF["F1_ULTRASHORT_OFFDIAGONAL [O]"]
  UNR["UNRESTRICTED_Q_MESOSCOPIC_FALSE [R]"]
  ALONE["MESOSCOPIC_LEMMA_ALONE_DOES_NOT_SOLVE_F1 [R]"]
  MES --> MIG
  FDR2 --> MIG
  MIG --> FULLMIG
  MIG --> CORE
  CORE --> AGG
  CORE --> OFF
  UNR -.refutes unrestricted q.-> MES
  ALONE -.mesoscopic lemma alone insufficient.-> MIG
```

```mermaid
graph TD
  TWO["TWO_OUTER_VARIABLE_F3_KERNEL [O]"]
  UNROUT["F3_SINGLE_OUTER_UNROUTABLE_CORE [O]"]
  FULLF3["larger full-F3 sector [O]"]
  TWO --> UNROUT
  TWO --> FULLF3

  HYB["HYBRID_MQ_KLOOSTERMAN_LARGE_SIEVE [O]"]
  F2["F2_CENTRAL_ENDPOINT [O]"]
  BAL["BALANCED_TII_CORE [O]"]
  PAR["PARITY_OPEN [O]"]
  HYB --> F2 --> BAL --> PAR
```

## Plain-text DAG (as requested in §15.B)

```text
BD reduction
  -> main term + low conductors
  -> pre-Poisson diagonal
  -> cross-coprime sector
  -> double-cross algebra/Fourier
  -> ratio-split Wright sectors
  -> 122/162 KF wedge
  -> widened r=2 F3 partial kill (high-conductor component, power saving)

fixed-depth routing (this update)
  -> routing threshold w > w*(μ) = (40+61μ)/81            [L]
  -> routing reindex λ^{(j)} = γ·∏_{i≠j} ψ_i              [L]
  -> high-conductor component power saving                [A]
  -> + main term + low/mid conductors + conductor window
  -> FULL routed piece: LOG saving only (not power saving) [A]
  -> routable long-Möbius F1 migration                    [A/L]

exact next wall
  -> TWO_OUTER_VARIABLE_F3_KERNEL                          [OPEN]
      -> balanced/unroutable fixed-depth F3, unroutable F1, larger full F3
```

## Ford/F1/F2 conservative update

```text
F1_GLOBAL_CENTERING_IDENTITY [LEAN_PROVED_CORE]
  -> F1_COMPARISON_SEQUENCE_AXIOMS [OPEN_INPUT]
  -> F1 aggregate off-diagonal [OPEN_INPUT]

F2_DOUBLE_MELLIN_PRIME_UNIT [SOURCE_PENDING]
  -> F2_PP_MAIN / F2_PN_SINGLE_SPECTRAL / F2_NP_SINGLE_SPECTRAL [SOURCE_PENDING]
  -> F2_NN_RECIPROCAL_TENSOR [OPEN_INPUT]
       -> RECIPROCAL_CHARACTER_TENSOR_LARGE_SIEVE [OPEN_INPUT]
  -> F2_COMPOSITE_GCD_REASSEMBLY [OPEN_INPUT]
  -> FULL_F2 [OPEN_INPUT]

FULL_F1 + FULL_F2 + FULL_F3
  -> UNIFORM_PROJECT_TYPE_II [OPEN_INPUT]
  -> Ford transference [CONDITIONAL_INTERFACE]
  -> FORD_MAYNARD_POSITIVITY_INTERFACE [SOURCE_PENDING]
```
