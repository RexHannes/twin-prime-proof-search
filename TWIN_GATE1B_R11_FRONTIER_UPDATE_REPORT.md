# TWIN GATE1B R11 — FRONTIER UPDATE (append-only formal layer)

Hilbert-caller graveyard · matched-line two-copy determinant · mean-zero finite Fourier ·
high-pass first-moment reassembly · rough-conductor finite skeleton · current `R_hi` status bank.

Nothing pre-existing was edited, renamed or deleted.  `VaughanCharts`, `Polytope611`,
`CutoffConservation`, `Reciprocity`, `Bruhat`, `AffineParametrization`, `HilbertHMRD/Fourier`,
`HilbertHMRD/OperatorStability`, `HilbertHMRD/Core` are reused, not duplicated.

---

## FILES ADDED

* `Gate1B/R11/Frontier/MatchedLine.lean`
* `Gate1B/R11/Frontier/GcdDescent.lean`
* `Gate1B/R11/Frontier/MeanZeroFourier.lean`
* `Gate1B/R11/Frontier/LowHighProjection.lean`
* `Gate1B/R11/Frontier/RoughConductorDescent.lean`
* `Gate1B/R11/Frontier/AuditCorrections.lean`
* `Gate1B/R11/Frontier/RoughModulusInterface.lean`
* `Gate1B/R11/Frontier/StatusBank.lean`
* `Gate1B/R11/Frontier/Bank.lean`  (dedicated aggregation target)
* `Gate1B/R11/Frontier/AxiomAudit.lean`
* `TWIN_GATE1B_R11_FRONTIER_UPDATE_REPORT.md` (this file)

## FILES MODIFIED

None.

---

## STRICT OUTPUT

**DEDICATED R11 FRONTIER BUILD:** PASS
(`lake build Gate1B.R11.Frontier.Bank Gate1B.R11.Frontier.AxiomAudit`, plus every new module
built individually; no errors, no warnings.)

**REPOSITORY-WIDE BUILD:** PRE-EXISTING-FAILURES.
`lake build` stops at the unchanged baseline failure
`error: no such file or directory … RequestProject/FixedCertificateAlgebra.lean`.
No unrelated repository code was repaired, and no new failure was introduced.

**ABSTRACT HILBERT-HMRD:** KERNEL-PROVED.
Re-ascribed in `Frontier/StatusBank.lean` as `bank_abstract_hilbert_hmrd` from the existing
`Gate1B.R11.bank_hilbert_hmrd`; a regression in the abstract theorem would break this build.

**PHYSICAL DELTA+SINGLE-POISSON CALLER:** RETIRED / FIREWALLED.
`frontierStatus .physicalHilbertCallerDeltaSinglePoisson = .retiredNonclosing`
(`physical_caller_retired`), it is a distinct row from the abstract theorem and its status is
provably not `kernelProved` (`physical_caller_firewall`), and `physicalR11Owners = []` with
`no_physical_R11_owner`.  No analytic impossibility theorem is asserted.

**TWO-COPY DETERMINANT 2h:** KERNEL-PROVED (`twoCopy_det`;
`d_t B_{t+h} − d_{t+h} B_t = 2h`, with `dLine_shift`, `BLine_shift`, `matched_det_line`).

**HECKE MATRIX FACTORISATION:** KERNEL-PROVED
(`vVec_shift`, `det_Nmat = 2`, `Mmat_factorisation : M_{t,h} = N_t · [[1,1],[0,h]]`,
`det_Mmat = 2h`, `det_Mmat_via_factorisation`).

**GCD DESCENT:** KERNEL-PROVED.
`gcd(d_t, d_{t+h}) = gcd(d_t, A h)` unconditionally; `= gcd(d_t, h)` under `gcd(d_t, A) = 1`,
which is *derived* (`coprime_d_A`) from the determinant plus oddness of `d_t` rather than
assumed silently; symmetric statement on the `B`-side (`coprime_B_k`, `gcd_BLine_two_copy`);
exact determinant descent `d' B_{t+h} − d'' B_t = 2h'` (`twoCopy_det_descent`).
`Int.gcd` is the `ℕ`-valued Mathlib normalisation, so there is no sign ambiguity.

**MEAN-ZERO:** KERNEL-PROVED (`sum_bPerp_interval`, `sum_bPerp_univ`, `fcoef_bPerp_zero`).

**FINITE FOURIER INVERSION:** KERNEL-PROVED (reused `Gate1B.HilbertHMRD.fourier_inversion`,
re-ascribed as `bank_fourier_inversion`).

**PARSEVAL:** KERNEL-PROVED (reused `fcoef_parseval`, re-ascribed as `bank_parseval`).

Mean-zero firewall: `meanZero_does_not_kill_high_frequencies` and
`bPerp_high_frequency_not_zero` exhibit finite data with `f̂(0) = 0` and `f̂(ξ) ≠ 0` for `ξ ≠ 0`.
Mean zero alone therefore gives no quantitative high-frequency saving.

**LOW/HIGH FIRST-MOMENT REASSEMBLY:** KERNEL-PROVED
(`low_add_high`, `Rtotal_eq_Rlo_add_Rhi`, and `fcoef_lowProj` showing `P_lo` is the exact
spectral cutoff).

**MIXED-QUADRATIC FIREWALL:** KERNEL-PROVED.
The recorded identity is `‖z+w‖² = ‖z‖² + ‖w‖² + 2 Re(z · conj w)` (`norm_sq_add`);
`mixed_term_not_deletable` and `Rtotal_sq_ne_sum_of_squares` show Pythagoras is false for
explicit first-moment data, so the cross term may never be deleted.

**IMPRIMITIVE CHARACTER DESCENT:** KERNEL-PROVED (not library-blocked).
`changeLevel_natCast`, `imprimitive_factorisation` (`χ(n) = χ*(n)·1_{gcd(n,r)=1}` for
`q = f·r`), inclusion–exclusion `1_{(n,r)=1} = ∑_{e ∣ (n,r)} μ(e)`
(`indicator_coprime_eq_sum_moebius`), the finite descent with explicit interval support
(`conductor_descent`), and the Dirichlet-character form (`dirichlet_conductor_descent`).

**PRINCIPAL 2^j CORRECTION:** KERNEL-PROVED.
`subset_cost_identity : ∑_{S ⊆ [j]} c = 2^j c`; the literal `j(D/P+1)` is refuted for `j = 5`
(`literal_j_cost_insufficient`), and `fixed_j_cost_constant` records that with `j = 5` fixed the
correction is a bounded constant factor, so no exponent changes.

**LEDGER 114 CORRECTION:** KERNEL-PROVED.
`ledgerExponent b = 114 + 3b/2`, `staleLedgerExponent b + 1 = ledgerExponent b`,
`staleLedgerExponent b < ledgerExponent b`, `ledgerExponent 0 = 114`.

**CELL Qmin/H_C FIREWALL:** KERNEL-PROVED.
`QminCell C hC Q = min_{A ∈ C} Q_A`; `cell_cap_uniform : 2H < Qmin_C → ∀ A ∈ C, 2H < Q_A`;
`QminCell_mem` (the minimum is attained, so the cap is sharp); `representative_Q_unsound`
exhibits a two-point cell where an unspecified representative `Q_C` fails.

**ROUGH-MODULUS ANALYTIC THEOREM:** CONDITIONAL ON EXPLICIT LARGE-SIEVE INPUT.
Option **B** was taken.  `PrimitiveLargeSieveInput` and `SparseRemainderInput` are explicit
hypotheses; `rough_modulus_variance_of_input` kernel-proves the downstream finite reduction
`total ≤ D·R + D²/P` conditionally on them.  No custom axiom is declared, the primitive
multiplicative large sieve is *not* postulated, and `largeSieve_input_load_bearing` shows the
analytic hypothesis is genuinely load-bearing (without it the reduction is false).
Research-status metadata only: `ROUGH-MODULUS VARIANCE : OPUS-AUDITED ANALYTIC BANK`
(`frontierStatus .roughModulusVariance = .researchBank`, provably `≠ kernelProved`).

**OLD SECTOR A:** CLOSED — AUDITED ANALYTIC BANK.
Recorded as `closedConditional`, provably not `kernelProved` (`oldSectorA_conditional`); the
enlarged low-frequency region is recorded under the same conditional status
(`roughConductorLowFrequencyClosure`).  No analytic `X L^{-B}` estimate is encoded as proved.

**OLD FSHC:** SUPERSEDED (`oldFSHC_superseded_not_open`: status `superseded`, provably not
`openRow`, so it cannot reappear as an open requirement).

**AUTHORITATIVE FRONTIER:** `R_hi`.
Exact finite source definition: `RhiFrontier S I w b = Rhi S w (bPerp I b)` — the high-frequency
first-moment projection of the mean-zero target against the coordinate weight `w` — with the
kernel-proved reduction `highPass_reduction : R_total = R_lo + R_hi`.  The analytic estimate is
recorded as the proposition `RhiAnalyticEstimate` and is never inhabited.

**R_hi:** OPEN · **R11:** OPEN · **GLOBAL GATE1B:** OPEN · **HSTAR:** OPEN ·
**TWIN PRIME:** OPEN · **r ≥ 8 CENSUS:** NOT STARTED
(`rhi_row_open`, `frontier_chain_statuses`, `global_rows_open`, `no_global_claim`).

**AXIOM AUDIT:** `Gate1B/R11/Frontier/AxiomAudit.lean` prints axioms for all new principal
theorems.  Every one depends only on a subset of `{propext, Classical.choice, Quot.sound}`;
several status/firewall theorems depend on no axioms at all.  Machine-checked over the new
directory: no `sorry`, no `admit`, no custom `axiom`, no `native_decide`, no
`@[implemented_by]`, no `unsafe`, no `opaque`.

---

## DEPENDENCY / GRAVEYARD CHAIN

```
ABSTRACT HILBERT-HMRD                      : KERNEL-PROVED     (unchanged)
PHYSICAL DELTA + SINGLE-POISSON CALLER     : RETIRED / NONCLOSING, firewalled

audited rough-conductor low-frequency closure   (closedConditional)
      ->
exact first-moment high-pass reduction          (KERNEL-PROVED)
      ->
R_hi                                            (OPEN)
      ->
R11                                             (OPEN)
```

`frontierChain = [roughConductorLowFrequencyClosure, firstMomentHighPassReduction,
rhiResidual, R11]` with the statuses above verified by `decide`.

STOP.
