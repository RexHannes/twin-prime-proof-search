# TWIN GATE1B / R11 — UNMODIFIED-ROW FORMAL SYNC REPORT

Append-only formal frontier sync of the Twin Gate1B / R11 bank.
Nothing pre-existing was deleted, renamed or weakened; the earlier frontier modules
(`MatchedLine`, `GcdDescent`, `MeanZeroFourier`, `LowHighProjection`, `RoughConductorDescent`,
`AuditCorrections`, `RoughModulusInterface`, `StatusBank`) and the earlier layers
(`VaughanCharts`, `Polytope611`, `CutoffConservation`, `Reciprocity`, `Bruhat`,
`AffineParametrization`, `HilbertHMRD`) are **reused**, not duplicated: the mean-zero projection
`bPerp`, the finite Fourier apparatus (`ez`, `fcoef`, `sum_ez_orth`), the first-moment functionals
`Rtotal / Rlo / Rhi`, and the status type `FrontierStatus` are all imported from them.

---

## 1. FILES ADDED

| File | Content |
|---|---|
| `Gate1B/R11/Frontier/OccupiedRowKernel.lean` | The exact original occupied-row arithmetic source: `rowAverage` (`A_i(ξ)` over the *actual* row interval), `freqMask`, the two arithmetic modes (`far` progression / `medium` `η_q/φ(q)`), the actual arithmetic phase, the row endpoint, mean subtraction, `D_i(v) = ∑_n μ_odd(n) Γ_i(v,n)`, and the finite-sum reassembly. |
| `Gate1B/R11/Frontier/ProductFibrePushforward.lean` | `b = N·w`, `‖w‖ ≤ 1`, equal-product merging, and the tuplewise firewall. |
| `Gate1B/R11/Frontier/EmptySiteRepairTransfer.lean` | The old empty-site repair: source preservation, principal cancellation, and the transfer identity `L_nonprincipal(repair) = L_principal(original row)`, with the principal-transfer firewall. |
| `Gate1B/R11/Frontier/UnmodifiedRowInterpolation.lean` | The unmodified-row compiler: cardinal interpolation object, exact sample recovery, "no synthetic values", the Fourier-transform **interface** (hypotheses, not axioms), and the width/Mellin-height scale identities. |
| `Gate1B/R11/Frontier/CriticalMixedIncidence.lean` | The modular relation `q_i A ≡ q_j B (mod k) → ∃ ℓ, q_i A − q_j B = ℓ k`, its converse, descent, and the no-size-bound firewall. |
| `Gate1B/R11/Frontier/RealOverlapSupport.lean` | The logarithmic support condition and the explicit conversion `|log(x/y)| ≤ δ ⟹ |x − y| ≤ 2 δ max(x,y)` (no `O(·)`). |
| `Gate1B/R11/Frontier/CriticalMaskFirewall.lean` | Full character orthogonality vs. a critical mask; masked frequency sum vs. a point mass; explicit finite counterexamples. |
| `Gate1B/R11/Frontier/NewCritStatusBank.lean` | Status ledger of the delta, re-ascription of every kernel-proved row, the exact finite definition of `R_newcrit`, the `CriticalMixedIncidenceHypothesis` **theorem parameter**, and the downstream conditional implication. |
| `TWIN_GATE1B_R11_UNMODIFIED_ROW_FORMAL_SYNC_REPORT.md` | This report. |

## 2. FILES MODIFIED

| File | Change |
|---|---|
| `Gate1B/R11/Frontier/Bank.lean` | Added imports of the eight new modules and the marker `newcrit_bank_loaded`. No existing declaration touched. |
| `Gate1B/R11/Frontier/AxiomAudit.lean` | Appended `#print axioms` for every new principal theorem. No existing line touched. |

No other repository file was modified.

## 3. BUILD STATUS

* **DEDICATED R11 FRONTIER BUILD: PASS.**
  `lake build Gate1B.R11.Frontier.Bank Gate1B.R11.Frontier.AxiomAudit` succeeds, as does each new
  module built individually. No errors and no warnings.
* **REPOSITORY-WIDE BUILD: PRE-EXISTING FAILURE.**
  `lake build` still stops at the unchanged baseline problem
  `no such file or directory … RequestProject/FixedCertificateAlgebra.lean`.
  This is outside scope, was not repaired, and no new failure was introduced.

## 4. THEOREM-BY-THEOREM STATUS

### 4.1 Original occupied-row source — KERNEL-PROVED

| Theorem | Statement |
|---|---|
| `rowAverage_zero` | `A_i(0) = 1` on a nonempty actual row interval. |
| `Dpre_eq_mask_mul` | The frequency mask factors out of the `n`-sum. |
| `Dpre_far` | Far mode: the arithmetic factor is exactly the progression restriction `n ≡ a_i (mod q_i)`. |
| `Dpre_medium` | Medium mode: the arithmetic factor is exactly `η_q(n)/φ(q_i)`. |
| `Dpre_odd_support` | Only odd `n` contribute (`μ_odd`). |
| `Drow_mean_zero` | The mean-subtracted row kernel has zero mean over the actual row interval. |
| `Drow_off_row`, `Drow_on_row` | The row kernel vanishes off the row and equals source minus row mean on it. |
| `freqMask_univ` | With the **full** mask, `∑_ξ A_i(ξ) e_Q(ξ v) = (Q/|I|)·1_I(v)`. |
| `DpreTotal_eq_double_sum` | **Reassembly**: the total source is the finite double sum, in either order. |
| `DrowTotal_of_common_interval` | Mean-subtracted reassembly for rows sharing a row interval. |
| `reassembly_has_no_free_cancellation` | Explicit admissible data attaining the trivial triangle bound: **no analytic cancellation is assumed**. |

### 4.2 Product-fibre pushforward — KERNEL-PROVED

`pushforward_factorisation` (`b v = N v · w v`), `fibreWeight_of_occupied` (equality at occupied
source positions), `norm_fibreWeight_le_one` (`‖w‖ ≤ 1`),
`norm_pushforward_le_fibreCount` and `merged_pushforward_factorisation` (the identity **after
equal-product merging**), and the firewalls
`productFibre_equality_ne_tuplewise_equality`, `fibreWeight_does_not_determine_selector`:
product-fibre equality is strictly weaker than tuplewise selector equality.
No historical selector predicate is formalised.

### 4.3 Old empty-site repair — KERNEL-PROVED (algebra) / RETIRED (free removal)

| Theorem | Statement |
|---|---|
| `Lphys_repair_zero` | **Full physical functional of `a` is `0`** — the repair is source-preserving. |
| `Lprin_repair`, `Lprin_repair_eq_neg_original` | `L_principal(a) = − L_principal(d0)`. |
| `Lnonprin_repair_eq_Lprin_original` | **`L_nonprincipal(repair) = L_principal(original row)`.** |
| `L_decomposition` | `L_all = L_principal + L_nonprincipal`. |
| `Lprin_repairedRow`, `Lphys_repairedRow`, `Lnonprin_repairedRow` | The repaired row has zero principal functional, unchanged physical functional, and carries the whole mass in the nonprincipal functional. |
| `principal_cancellation_is_not_removal`, `repair_transfers_rather_than_removes` | **Firewall**: cancelling the principal component does *not* remove the corresponding contribution from the complete spectrum. |

Status recorded: `emptySiteRepairAlgebra = kernelProved`,
`emptySiteRepairFreePrincipalRemoval = retiredNonclosing`, the two rows are provably distinct and
the retired one is provably not `kernelProved` (`empty_site_repair_firewall`).
No universal impossibility theorem is stated.

### 4.4 Unmodified-row compiler — KERNEL-PROVED (exact) / CONDITIONAL (transform)

`CardinalInterpolation.z_injective` (distinct centres derived from disjoint supports),
`interpolant_sample` (**exact sample recovery** `H(z_u) = d_i^0(u)`),
`interpolant_eq_sum_support` and `interpolant_of_zero` (**no synthetic values** at target-zero
positions), `interpolant_compiledRow` (`d_i^0 = w_i D_i` recovered exactly).
`interpolant_transform` is proved **from the explicit `FourierInterface` hypotheses** — the
Fourier-transform statement is a theorem interface, not an axiom.

### 4.5 Width scaling — KERNEL-PROVED (scale only)

`widthOf_scale` (`h_i = θ k_i /(C Y)` scales linearly in `θ`),
`mellin_height_scale` (`θ = L^{−m}`, `T₁ = P θ^{−1} L³` ⟹ **`T₁ = P L^{m+3}`**),
`energy_height_product_invariant` (narrowing divides the row interpolation energy and multiplies
the Mellin height by the same factor; the product is invariant),
`narrow_interpolation_no_free_saving` (**firewall**: the scale algebra leaves `T₁` unbounded, so it
creates no arithmetic cancellation).

### 4.6 Critical mask — KERNEL-PROVED firewall

`maskedSum_univ`, `full_character_sum_is_indicator` (the **full** sum gives the standard congruence
indicator), `abstract_full_orthogonality` (same statement from an abstract orthogonality
hypothesis), `proper_mask_not_congruence_indicator` and `masked_frequency_sum_not_point_mass`
(explicit finite counterexamples for a proper mask), `unmasked_frequency_sum_is_point_mass`.

### 4.7 Mixed incidence — KERNEL-PROVED modular relation

`mixedIncidence_relation`, `mixedIncidence_relation_converse`, `mixedIncidence_dvd`,
`mixedIncidence_witness_unique`, `MixedIncidenceData.relation`, `mixedIncidence_descent`, and
`mixedIncidence_no_size_bound` (no heuristic size bound is encoded).

### 4.8 Real-overlap support — KERNEL-PROVED

`ratio_bounds_of_log_le`, `abs_sub_le_of_log_le`, `exp_sub_one_le_two_mul`,
`abs_sub_le_two_mul_of_log_le`, `overlap_abs_sub_le`
(`logOverlap` ⟹ `|A B_{j,v} − B B_{i,u}| ≤ 2 Cp (h_i + h_j)`, all constants explicit),
`overlap_bound_is_not_o_delta`.

### 4.9 `R_newcrit`

`RnewcritSource` is the exact finite first moment of the **original occupied arithmetic rows**
(mean-subtracted, **no empty-site correction**).
`RnewcritEstimate` is defined and **never inhabited**.
`CriticalMixedIncidenceHypothesis` is an ordinary `Prop`-valued theorem parameter (not an axiom),
and only the downstream conditional implication is kernel-proved:
`bound_of_criticalMixedIncidence` and `Rnewcrit_estimate_of_hypothesis`.

## 5. EXACT AXIOM DEPENDENCIES

`Gate1B/R11/Frontier/AxiomAudit.lean` prints axioms for every new principal theorem.
Result: each depends only on a subset of `{propext, Classical.choice, Quot.sound}`; the purely
decidable status theorems (`empty_site_repair_firewall`, `retired_mechanisms`,
`conditional_analytic_rows`, `rhi_superseded_as_current_coordinate`, `newcrit_open_rows`,
`Rnewcrit_row_open`, `newCritKernelProved_correct`) depend on **no axioms at all**, and
`no_newcrit_owner`, `newCritKernelProved_excludes_open` only on `propext`.
No `sorryAx`. A machine search over `Gate1B/R11/Frontier/` finds no `sorry`, no `admit`, no custom
`axiom`, no `native_decide`, no `@[implemented_by]`, no `unsafe`, no `opaque`.

## 6. OLD EMPTY-SITE REPAIR STATUS

* **ALGEBRAIC SOURCE PRESERVATION: KERNEL-PROVED** (`Lphys_repair_zero`, `Lphys_repairedRow`).
* **FREE PRINCIPAL REMOVAL: RETIRED** (`retiredNonclosing`, provably not `kernelProved`).
* **REPAIR TRANSFER: KERNEL-PROVED** — `L_nonprincipal(repair) = L_principal(original row)`.
* It is **not** evidence of critical-spectrum smallness: the mass is transferred, not removed.

## 7. NEW UNMODIFIED-ROW COMPILER STATUS

Exact and algebraic parts kernel-proved (sample recovery, no synthetic values, scale identities).
The Fourier transform is an explicit interface; the arbitrary-log analytic principal estimate is
**not** formalised as a theorem and is recorded as conditional analytic only.

## 8. CURRENT FORMAL FRONTIER

`R_newcrit`: **CURRENT FRONTIER, OPEN** — exact original occupied arithmetic rows, no empty-site
correction, high conductor / moderate target amplitude, mixed signed covariance unresolved.
The previous coordinate `R_hi` is **HISTORICAL / SUPERSEDED AS CURRENT COORDINATE**
(`superseded`), *kept and still valid*: its exact high-pass reduction is re-ascribed as
`newbank_rhi_still_valid`.

## 9. ANALYTIC ASSUMPTIONS NOT PROVED (external / conditional inputs)

* primitive multiplicative large sieve;
* Gallagher / logarithmic localization;
* Chen–Gupta–Li large-values theorem;
* Maynard–Pandey–Radziwiłł analytic inputs;
* the narrow-interpolation arbitrary-log principal estimate;
* conductor / time tail estimates;
* the critical signed mixed-covariance estimate (`CriticalMixedIncidenceHypothesis`);
* the Fourier transform of the interpolation kernel (`FourierInterface`).

All are theorem hypotheses / structure fields. None is a Lean axiom, and none is inhabited.

## 10. PRECISE OPEN NODES

`R_newcrit`, `R11`, Global Gate 1B, `HSTAR`, Twin Prime — all `openRow`, with no proved owner
(`newCritOwners = []`, `no_newcrit_owner`).

---

## STRICT FINAL STATUS

```
OLD EMPTY-SITE REPAIR:
    ALGEBRAIC SOURCE PRESERVATION:
        KERNEL-PROVED

    FREE PRINCIPAL REMOVAL:
        RETIRED

REPAIR TRANSFER:
    L_nonprincipal(repair)
      =
    L_principal(original):
        KERNEL-PROVED

ORIGINAL OCCUPIED ROW SOURCE:
    KERNEL-PROVED

PRODUCT-FIBRE PUSHFORWARD:
    KERNEL-PROVED

CRITICAL MASK FULL-ORTHOGONALITY FIREWALL:
    KERNEL-PROVED

MIXED INCIDENCE MODULAR RELATION:
    KERNEL-PROVED

NARROW-INTERPOLATION SCALE:
    KERNEL-PROVED

NARROW-INTERPOLATION ANALYTIC PRINCIPAL BOUND:
    CONDITIONAL

R_newcrit:
    OPEN

R11:
    OPEN

GLOBAL GATE1B:
    OPEN

HSTAR:
    OPEN

TWIN PRIME:
    OPEN

DEDICATED BUILD:
    PASS

AXIOM AUDIT:
    PASS
```

STOP.
