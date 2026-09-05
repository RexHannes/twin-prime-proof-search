# GATE1B / R11 — CANONICAL KERNEL BANK REPORT

Append-only delta. Nothing pre-existing was edited, renamed or deleted.

## 1. Lean files created

| File | Module | Content |
|---|---|---|
| `Gate1B/R11/CanonicalSource.lean` | `Gate1B.R11` | label layer, Möbius sign of squarefree prime products, collision decomposition, rational exponent metadata |
| `Gate1B/R11/Card5.lean` | `Gate1B.R11` | CARD5 selectors, `C(10,5) = 252`, sign `+1`, equal-`n` collapse |
| `Gate1B/R11/Factor542.lean` | `Gate1B.R11` | ordered `4\|4\|2` allocations, count `3150`, normalization, factorial ledger |
| `Gate1B/R11/ComparisonTyping.lean` | `Gate1B.R11` | `bFull` / `bLoc` typed placements and the exact pairing identity |
| `Gate1B/R11/MobiusLogSplit.lean` | `Gate1B.R11` | `Λ = μ * log` pointwise, cutoff split, `V* = 2` support observation |
| `Gate1B/R11/LongMobius.lean` | `Gate1B.R11` | divisor involution `k = N/d`, long-Möbius reindexing, weighted corollary |
| `Gate1B/R11/Determinant.lean` | `Gate1B.R11` | `AB − kd = −2`, four cross gcds, Bézout parametrization + uniqueness |
| `Gate1B/R11/Bank.lean` | `Gate1B.R11` | residual/tail definitions, conditional Pascadi-type interface, coverage firewall, internal bank completeness |
| `Gate1B/R11/AxiomAudit.lean` | `Gate1B.R11` | `#print axioms` for every principal theorem |

Individual build: **PASS** for all nine modules (`lake build Gate1B.R11.<Module>`).
Repository-wide `lake build` still stops at the *pre-existing* baseline failure
(`RequestProject/FixedCertificateAlgebra.lean` missing); this delta does not affect it.

## 2. Theorems proved (kernel-checked, sorry-free)

**Canonical source / labels**
`R11Labels.atoms_zero`, `R11Labels.atoms_succ`, `R11Labels.atoms_injective`,
`R11Labels.atoms_injective_of_admissible`, `R11Labels.atoms_prime_of_admissible`,
`moebius_prod_primes`, `squarefree_prod_primes`.

**Collisions**
`crossGroupPairs_count` (`4·4 + 4·2 + 4·2 = 32`), `sfIndicator_of_squarefree`,
`sfIndicator_of_not_squarefree`, `omegaSquarefree_eq_free_sub_collision` (unconditional),
`sum_omegaSquarefree_eq`, `canonical_source_from_free_of_collision_bound` (conditional wrapper).

**Rational metadata**
`centers_sum_to_one`, `p0_plus_four_large`, `four_large`, `two_large`, `six_large`,
`split_227_273`, `gap_23_250`.

**CARD5**
`choose_ten_five`, `card_card5Selectors`, `card5Selectors_card_eq`, `selectedDivisor_eq_prod`,
`selectedDivisor_squarefree` (six distinct prime atoms), `moebius_selectedDivisor` (`= +1`),
`card5_equal_n_collapse`, `card5_equal_n_collapse_of_blind`, `card5Coefficient_eq`.

**5|4|2**
`choose_ten_four`, `choose_six_four`, `choose_mul_choose_442`, `card_Alloc442` (`= 3150`),
`mem_Alloc442`, `card_residual_of_mem_Alloc442`, `grouped_prod_recombines`,
`factor542_normalization_mul`, `factor542_normalization` (averaged, over a char-0 field),
`factorial_ten_split`, `factorial_quotient_eq_3150`,
`factorial_normalization_no_extra_multiplicity`, `card5_outer_coefficient_ledger`
(`252`, and `252 ≠ 252·3150`), `ratio_252_3150` (`252/3150 = 2/25`).

**Comparison typing**
`comparison_weight_typing`, `comparison_weight_typing_sum`, `bFull_ne_bLoc`,
`bFull_eq_bLoc_iff`.

**Möbius–log**
`vonMangoldt_eq_sum_moebius_mul_log`, `vonMangoldt_split`, `longMobiusLog_eq_sub`,
`odd_of_dvd_odd`, `divisors_filter_le_two_of_odd`, `vonMangoldtTrunc_two_eq_zero_of_odd`.

**Long-Möbius reindexing**
`divisor_involution_bijOn`, `sum_long_divisors_reindex`, `longMobiusLog_reindex`,
`reindexed_term_one_eq_zero`, `odd_divisor_and_complement`, `weighted_longMobius_reindex`.

**Determinant / Bézout**
`determinant_eq_neg_two`, `eq_one_of_dvd_two_of_odd`, `odd_of_dvd_odd'`, `cross_coprime_aux`,
`determinant_pairwise_cross_coprime` (all four gcds), `determinant_solution_parametrization`,
`determinant_solution_parametrization_unique`, `isCoprime_of_nat_gcd_eq_one`.

**Bank**
`longMobiusTail_eq_sum_longMobiusLog`, `r11_low_closed_implies_longMobius_residual`
(CONDITIONAL: takes the low-`d` discrepancy bound as an explicit hypothesis),
`r11_low_closed_implies_longMobius_residual_with_collision` (CONDITIONAL),
`internal_bank_does_not_entail_coverage`, `canonical_internal_bank_complete`.

## 3. Theorems NOT proved (deliberately)

* `CanonicalCoversFullR11` — *defined only*, never inhabited, never concluded. There is **no**
  theorem named or implying `fullPhysicalR11_eq_canonicalR11`.
* `LowDivisorDiscrepancyBound` / `PascadiOwner` — interfaces only; the analytic estimate is
  never postulated and never proved. It occurs solely as a hypothesis.
* The long-Möbius analytic cancellation — not attempted; no asymptotic bound is encoded in
  any core statement.
* No analytic support statement is derived from the rational exponent metadata.

## 4. Axiom audit

`Gate1B/R11/AxiomAudit.lean` prints axioms for all principal theorems. Every one depends on a
subset of `{propext, Classical.choice, Quot.sound}`; several (`choose_ten_five`,
`factorial_ten_split`, `card5_outer_coefficient_ledger`) depend on no axioms at all.

## 5. Confirmation

* no `sorry`;
* no `admit`;
* no custom `axiom`;
* no `native_decide`, no `@[implemented_by]`;
* finite checks use kernel-checked `decide` / `norm_num` / `ring` / `omega` only.

Machine-checked with `rg -n "sorry|admit|^axiom |native_decide|implemented_by" Gate1B/R11/`
(only the prose line in the `Bank.lean` header matches).

## 6. Status ledger

| Item | Status |
|---|---|
| CARD5 252 | KERNEL-PROVED |
| 5\|4\|2 3150 | KERNEL-PROVED |
| FACTORIAL NORMALIZATION | KERNEL-PROVED |
| COLLISION DECOMPOSITION | KERNEL-PROVED (unconditional; analytic bound only as hypothesis) |
| COMPARISON bFull/bLoc TYPING | KERNEL-PROVED |
| MOBIUS-LOG DIVISOR SPLIT | KERNEL-PROVED |
| LONG-MOBIUS REINDEXING | KERNEL-PROVED |
| AB−kd = −2 | KERNEL-PROVED |
| FOUR CROSS-GCD IDENTITIES | KERNEL-PROVED |
| BEZOUT PARAMETRIZATION | KERNEL-PROVED (existence + uniqueness) |
| CANONICAL → FULL HISTORICAL R11 | NOT PROVED |
| PASCADI ANALYTIC OWNER | EXTERNAL / CONDITIONAL ONLY |
| LONG-MOBIUS ANALYTIC CANCELLATION | OPEN / NOT ATTEMPTED |
| R11 FULL PHYSICAL ROW | OPEN |
| GLOBAL GATE1B | OPEN |
| TWIN PRIME | OPEN |
