# UNIVERSAL v8 — SAFE FORMAL BANK EXTENSION: FINAL REPORT

```text
LEAN VERSION:   leanprover/lean4:v4.28.0
MATHLIB COMMIT: 8f9d9cff6bd728b17a24e163c9402775d9e6a365
LAKE BUILD:     PASS (whole project, 8368 jobs, 0 errors)
```

The existing Gate 1A / Gate 1B safe-algebra bank was rebuilt **from source** (every
`.lean` file is recompiled by `lake build`; nothing is taken from a precompiled report)
and re-audited before any new file was written.  No existing theorem was altered,
renamed, weakened or duplicated.

---

## 1. FINAL LEDGER (requested form)

```text
OLD GATE1A/GATE1B SAFE ALGEBRA REGRESSION:      PASS
DISCRETE ABEL IDENTITY:                         PROVED
ABSTRACT BV BOUND:                              PROVED
PIECEWISE ROUTING JUMP -> BV:                   PROVED
SYNTHESIS / BLOCK GRAM:                         PROVED
ACTUAL-VECTOR TRANSPORT:                        PROVED
UNWEIGHTED SCHUR:                               PROVED (stronger: no sign assumption on x)
WEIGHTED SCHUR:                                 PROVED (repaired: symmetry is load-bearing)
BUDGETED SYNTHESIS PRINCIPLE:                   PROVED
DIAGONAL/OFF-DIAGONAL DECOMPOSITION:            PROVED
NO-FREE-FAMILY COUNTERMODEL:                    PROVED
NO-FREE-SIGN COUNTERMODEL:                      PROVED
DEFECT CAPACITY:                                PROVED (repaired: coprimality not needed
                                                for the product-divides form)
GATE 1A BP EXPONENT REPAIR:                     PROVED EXACTLY OVER ℚ
GATE 1A WORST ENERGY SURPLUS:                   1/72
GATE 1A AMPLITUDE TAX:                          1/144
CF-BP1A:                                        INTERFACE ONLY — OPEN
GATE 1B NO-WRAP EXPONENT LEDGER:                PROVED
GATE 1B DIAGONAL EXPONENT FLOOR:                1/18
ABSTRACT SAME-CONDUCTOR DIAGONAL REDUCTION:     PROVED
GATE 1B X/Q = R BUDGET:                         PROVED
ROUTE-BV45:                                     INTERFACE ONLY — OPEN
NPL-OFF45:                                      INTERFACE ONLY — OPEN
ANALYTIC CLAIMS BANKED:                         NONE
GATE 1A CLOSED:                                 NO
GATE 1B CLOSED:                                 NO
SORRY COUNT:                                    0
USER AXIOM COUNT:                               0
OPAQUE COUNT:                                   0
NATIVE_DECIDE COUNT:                            0  (two pre-existing uses repaired)
IMPLEMENTED_BY COUNT:                           0
MOST IMPORTANT REPAIR:                          two pre-existing `native_decide` proofs in
                                                RequestProject/NANC/PatternCount69.lean are
                                                now kernel-checked `decide`
MOST IMPORTANT NEW SAFE THEOREM:                UniversalV8.normalizedSynthesisBound
                                                (local packet control + synthesis
                                                congestion ⇒ global bound), together with
                                                its guard
                                                UniversalV8.identical_packets_have_family_congestion
```

---

## 2. WHAT IS PROVED (statement by statement)

### UniversalV8 Module A — exact discrete Abel summation (`UniversalV8/DiscreteAbel.lean`)

* `partialSum m a t = ∑_{m ≤ k ≤ t} a k` (over `ℂ`).
* `local_sum_by_parts_succ` : for `m ≤ n`,
  `∑_{m ≤ k < n+1} a_k w_k = P(n) w_n − ∑_{m ≤ k < n} P(k)(w_{k+1} − w_k)` — an exact
  identity, no error term.
* `local_sum_by_parts` : the `(ABEL)` form with `n − 1`, for `m < n`.
* `norm_sum_le_partialSumBound_mul_variation` : `(ABEL-BV)`
  `|∑ a_k w_k| ≤ Δ (|w_{n−1}| + Var(w))` whenever `|P(t)| ≤ Δ` on `m ≤ t < n`.

No Mertens estimate is involved anywhere.

### Module B/C — discrete BV and routing jumps (`UniversalV8/BoundedVariation.lean`)

* `variation m n w = ∑_{m ≤ k < n} ‖w(k+1) − w(k)‖`, `dBV M m n w = M + variation`.
* Closure rules: `variation_const`, `variation_smul` (exact equality `‖c‖ · Var`),
  `variation_add`, `variation_sub`, `variation_mul` (with supplied uniform bounds),
  `variation_concat` (exact additivity along a split point), `variation_mono`
  (restriction), `variation_piecewise_const`.
* `weighted_sum_le_partialSum_mul_dBV` : `|∑ a_k w_k| ≤ Δ · dBV`.
* `jumpSet m n w = {k ∈ Ico m n | w(k+1) ≠ w k}`;
  `variation_le_two_mul_bound_mul_jumpCount` : `(PC-BV)` `Var ≤ 2 M J`;
  `dBV_le_of_jumpCount` : `(PC-dBV)` `dBV ≤ M (1 + 2J)`.
* `Universal.SafeAlgebra.variation_indicator_le`: an interval indicator is `O(1)` in dBV.

**The antecedent about the actual Gate routing is not declared anywhere.**

### Modules D/E/F — synthesis, transport, Schur

(`UniversalV8/Synthesis.lean`, `UniversalV8/BlockGram.lean`)

* `blockGramIdentity` : `⟪S f, S g⟫ = ∑_{γ,γ'} ⟪f_γ, (B_γ* ∘ B_γ')(g_γ')⟫` — the genuine
  operator-adjoint block form of `S*S`.
* `synthesis_norm_sq` : `‖S f‖² = ∑_{γ,γ'} re ⟪B_γ f_γ, B_γ' f_γ'⟫` (type-correct real
  form of the quadratic identity).
* `normalizedSynthesisBound` : local packet control `‖B_γ* B_γ'‖ ≤ k(γ,γ')` **together
  with** congestion control (symmetric nonnegative `k`, row sums `≤ η`) gives
  `‖S f‖² ≤ η ∑ ‖f_γ‖²`.
* `inner_apply_le_of_apply_norm_le` : `(AVT)` `|⟪z, G z⟫| ≤ η ‖z‖²` from `‖Gz‖ ≤ η‖z‖`
  (no PSD needed); `actualVectorTransport` : `re ⟪z, G z⟫ ≤ ‖z‖ ‖G z‖`.
* `unweightedSchur` : `(SCHUR-0)`.  **Repair/strengthening**: the nonnegativity of `x` in
  the requested statement is unnecessary; the theorem is banked for arbitrary real `x`.
* `weightedSchur` : symmetric nonnegative kernel with `∑_j k_{ij} w_j ≤ η w_i` gives
  `∑_{i,j} k_{ij} x_i x_j ≤ η ∑ x_i²`.
  **Repair**: the one-sided weighted criterion is FALSE without symmetry (or a column
  condition).  The countermodel is banked as `weightedSchur_needs_symmetry`
  (a `5×5` nonsymmetric kernel with all weighted row sums `≤ 1` whose form exceeds
  `1 · ∑ x_i²`).

The retracted identity `‖∑ b_γ T_γ‖² = ∑ b_γ b̄_{γ'} ⟪T_γ, T_γ'⟫` for arbitrary bounded
operators is **not** stated anywhere.

### Module G — budgeted synthesis (`UniversalV8/Budget.lean`)

`budgetedSynthesis`, `budgetedSynthesis_closes`, `budgetedSynthesis_ratio`.
`C = o(1)` is deliberately NOT part of any statement.

### Module H — diagonal baseline (`UniversalV8/DiagonalBaseline.lean`)

* `sum_sum_eq_diag_add_offDiag` (general double-sum splitting),
* `gram_expand`, `gram_eq_diag_add_offdiag` : `‖∑ z_γ v_γ‖² = D + O` with
  `D = ∑ |z_γ|²‖v_γ‖²`,
* `diagOffDiag_budget`, `diagOffDiag_budget_remaining` (only the remaining budget must be
  supplied by the off-diagonal estimate),
* `quadraticForm_eq_diag_add_offDiag` (matrix version).

### Module I — countermodels (`UniversalV8/Countermodels.lean`)

* `identical_packets_have_family_congestion` (+ strict gap `identical_packets_gap`):
  `N` identical contractions, input energy `N`, synthesis square `N²`.
* `signs_do_not_force_cancellation`, `signed_family_can_attain_maximum`.
* `dBV_needs_partialSum_bound`: without the partial-sum bound the backend-dual-norm
  conclusion fails (weighted sum `N`, dBV factor `1`).

### Module J — defect capacity (`UniversalV8/DefectCapacity.lean`)

* `nat_prod_dvd_of_pairwiseCoprime`, `defectValuation_product_le`,
* `defectCapacity` : `∏_{i∈I} m_i ∣ D`, `D > 0`, `m_i ≥ Y` ⇒ `Y^{|I|} ≤ D`.
  **Repair**: pairwise coprimality is NOT needed for this form; it is needed only to get
  the product divisibility from `m_i ∣ D` (`pow_card_le_of_pairwiseCoprime_product_dvd`).
* `defectCapacity_pow` (exponents), `defectCapacity_log` (`|I| log Y ≤ log D`).

### Gate 1A — corrected BP exponent ledger (`Gate1A/SafeAlgebra/BPExponentRepair.lean`)

Exact `ℚ`, `m = 1/3`, `σ(h,m) = h/16 − 5m/32`, `ρ = 2σ = h/8 − 5m/16`, `τ = h − m`:

```text
h1 = 5/18 :  ρ = −5/72     τ = −1/18   surplus 1/72
h2 = 11/36:  ρ = −19/288   τ = −1/36   surplus 11/288
h3 = 7/24 :  ρ = −13/192   τ = −1/24   surplus 5/192
min{1/72, 11/288, 5/192} = 1/72        amplitude tax = 1/144
```

All three vertex values verified exactly; nothing about the Blomer–Pascadi estimate, the
Gate-to-BP dictionary, common-frame synthesis or Gate 1A closure is proved.

### Gate 1B — exponent / no-wrap ledger (`Gate1B/SafeAlgebra/NPLBudget.lean`)

`u = 4/9`, `v = 5/9`, `u + v = 1`, `ω + r = 1`, `u < v`;
`nearPrimitiveNoWrapExponent` : `ω ≥ 13/18`, `0 < η < 1/6` ⇒ `ω − η > 5/9 = v`;
`diagonal_exponent_identity` : `(u+v+ω)/2 = (1+ω)/2 = 1 − r/2`;
`gate1B_R_exponent_lower` : `ω ≤ 8/9 ⇒ r ≥ 1/9`;
`npl_diagonal_saving_floor` : `r/2 ≥ 1/18` (endpoint value exactly `1/18`);
`X_div_Q_eq_R`, `npl_allowedCongestion`.

### Gate 1B — abstract diagonal reduction and budget

(`Gate1B/SafeAlgebra/NPLDiagonalReduction.lean`, `Gate1B/SafeExtensions/*`)

* `sameConductorDiagonal_le` : `(DIAG-RED)` `T₂(g) ≤ g²B₂` and `∑ g²|Z(g)|² ≤ K C₂` give
  `∑ |Z(g)|² T₂(g) ≤ K B₂ C₂`.
* `sum_le_of_injOn` (injective-restriction inequality),
  `nearPrimitive_diag_energy_bound`, and
  `Gate1B.SafeExtensions.nearPrimitive_diag_energy_bound_restricted` (no-wrap form).
  `nearPrimitive_needs_injectivity` shows the injectivity hypothesis is load-bearing.
* `gate1B_congestionBudget`, `gate1B_congestionBudget_closes`,
  `Gate1B.SafeExtensions.gate1B_sufficient_congestion`.
* `Gate1B.SafeExtensions.squarefree_moebius_remove_prime` : `μ(q/p) = −μ(q)` on squarefree
  `q`; `fixedQ_weightedSignCollapse` : `∑_{p∣q} μ(q/p) f(p) = −μ(q) ∑_{p∣q} f(p)`;
  `squarefree_hypothesis_load_bearing` : the countermodel `q = 4`, `p = 2`.
* `Gate1B.SafeExtensions.primitiveConductorTrichotomy` and
  `primitiveConductor_cases_disjoint` : the divisor partition of `d p` into
  (`p ∤ c`, `c ∣ d`) / (`c = p`) / (`c = p h`, `h ∣ d`, `h > 1`).
* `Gate1B.SafeAlgebra.routed_weighted_sum_bound` : the abstract routed backend-dual bound
  `|∑ a w| ≤ Δ M (1 + 2J)`.

### Universal safe-algebra layer (`Universal/SafeAlgebra/`)

Re-export modules (no proof duplication) plus genuinely new items:
`backendDualNorm_discreteBV`, `variation_indicator_le`, `weightedBlockSchur`,
`openChain_two` (`(re⟪z,Gz⟫)² ≤ ‖z‖² re⟪z,G²z⟫` for self-adjoint `G`),
`closedCycle_trace_invariant` (outer signs cannot change trace moments),
`closedCycle_sign_telescopes`.

---

## 3. REUSE (no duplication)

* The centered factorisation identity `ρ_{dp} = ρ_d ρ_p + ρ_d/p + ρ_p/d` for coprime
  `d, p` already exists in this project as `Gate01Consolidation.rho_mul_coprime`
  (`RequestProject/NANC/Gate01Consolidation/CRTCentering.lean`, definition
  `ρ_m(y) = 1_{m∣y} − 1/m`).  It was checked to be exactly the requested statement and is
  therefore **not** duplicated; the reuse is recorded in
  `Gate1B/SafeExtensions/Interfaces.lean`.
* The Gate 1B anti-Cartesian counterexample is reused, not duplicated
  (`Gate1B.shell_sum_ne_cartesian_sum`).
* `Gate1B/SafeExtensions/NearPrimitiveDiagonal.lean` and `.../Budget.lean` build on
  `Gate1B/SafeAlgebra/NPLDiagonalReduction.lean` rather than restating it.

---

## 4. INTERFACE-ONLY CHECK

`UniversalV8/Interfaces.lean`, `Universal/SafeAlgebra/Interfaces.lean`,
`Gate1B/SafeExtensions/Interfaces.lean`, `Gate1A/SafeAlgebra/UniversalV8Bridge.lean`,
`Gate1B/SafeAlgebra/UniversalV8Bridge.lean` contain **no declarations at all** — verified
by inspection: they consist of a single block comment each.  Therefore no analytic
interface (`MERTENS_VINOGRADOV_KOROBOV`, `ROUTE_BV45`, `NPL_OFF45`,
`BLOMER_PASCADI_APPLICATION`, `PASCADI_*`, `DRAPPEAU_*`, `E(q)`, `Z_E(q)`, `KAPPA4`,
`CF_BP1A`, `GATE1A_CLOSED`, `GATE1B_CLOSED`, `FULL_TYPE_II`, `TWIN_PRIMES`,
`ERDOS_287_CLOSED`, …) can be inhabited or invoked.

---

## 5. FALSE / REPAIRED STATEMENTS FOUND

1. **One-sided weighted Schur without symmetry is FALSE.**  Countermodel banked
   (`weightedSchur_needs_symmetry`); the banked theorem carries the symmetry hypothesis.
2. **Defect capacity does not need pairwise coprimality** in the product-divides form.
   Repaired to the strongest clean statement, with the coprime version kept as a
   corollary.
3. **Unweighted Schur does not need `x ≥ 0`.**  Banked in the stronger form.
4. Two pre-existing `native_decide` proofs (`RequestProject/NANC/PatternCount69.lean`)
   were replaced by kernel-checked `decide`; the statements are unchanged and still hold.

No existing Gate 1A / Gate 1B theorem was found to be false, and none was found to differ
from its prose description.

---

## 6. AXIOM AUDIT

`#print axioms` is run on every principal new theorem in

* `UniversalV8/Status.lean` (61 principal declarations),
* `Universal/SafeAlgebra/Status.lean` (6),
* `Gate1B/SafeExtensions/Status.lean` (8),

in addition to the pre-existing `Gate1A/Status.lean`, `Gate1A/SafeAlgebra/Status.lean`,
`Gate1A/Delta4/Status.lean`, `Gate1B/Status.lean`, `RequestProject/Status.lean`.
Every report is `[propext, Classical.choice, Quot.sound]` or a subset; several report no
axioms at all.  No `Lean.ofReduceBool` appears anywhere (this is what the `native_decide`
repair removed).

Token scan of all new and touched files for
`sorry`, `admit`, `axiom`, `opaque`, `native_decide`, `implemented_by`:
the only hits are inside documentation comments (e.g. "sorry-free", the audit paragraphs
of the `Status.lean` files, and the repair note in `PatternCount69.lean`).

---

## 7. FILES

```text
ADDED:
  UniversalV8/DiscreteAbel.lean
  UniversalV8/BoundedVariation.lean
  UniversalV8/Synthesis.lean
  UniversalV8/BlockGram.lean
  UniversalV8/DiagonalBaseline.lean
  UniversalV8/Budget.lean
  UniversalV8/DefectCapacity.lean
  UniversalV8/Countermodels.lean
  UniversalV8/Interfaces.lean            (comments only)
  UniversalV8/Status.lean
  Universal/SafeAlgebra/FiniteAbel.lean
  Universal/SafeAlgebra/DiscreteVariation.lean
  Universal/SafeAlgebra/SynthesisBudget.lean
  Universal/SafeAlgebra/Gram.lean
  Universal/SafeAlgebra/WeightedSchur.lean
  Universal/SafeAlgebra/OpenChain.lean
  Universal/SafeAlgebra/DefectCapacity.lean
  Universal/SafeAlgebra/Counterexamples.lean
  Universal/SafeAlgebra/ExponentLedger.lean
  Universal/SafeAlgebra/Interfaces.lean  (comments only)
  Universal/SafeAlgebra/Status.lean
  Gate1A/SafeAlgebra/BPExponentRepair.lean
  Gate1A/SafeAlgebra/UniversalV8Bridge.lean   (comments only)
  Gate1B/SafeAlgebra/RouteVariation.lean
  Gate1B/SafeAlgebra/NPLBudget.lean
  Gate1B/SafeAlgebra/NPLDiagonalReduction.lean
  Gate1B/SafeAlgebra/UniversalV8Bridge.lean   (comments only)
  Gate1B/SafeExtensions/SourceWeightCollapse.lean
  Gate1B/SafeExtensions/PrimitiveConductorRouter.lean
  Gate1B/SafeExtensions/NearPrimitiveDiagonal.lean
  Gate1B/SafeExtensions/Budget.lean
  Gate1B/SafeExtensions/Interfaces.lean       (comments only)
  Gate1B/SafeExtensions/Status.lean
  UNIVERSAL_V8_SAFE_FORMAL_REPORT.md

MODIFIED:
  lakefile.toml                          (two new libraries: UniversalV8, Universal)
  LEDGER.md                              (appended, never overwritten)
  RequestProject/NANC/PatternCount69.lean (native_decide -> decide)

UNCHANGED:
  every pre-existing Gate1A/*, Gate1B/*, Gate04Root/*, RequestProject/* module
  (other than the PatternCount69 repair above), and ARISTOTLE_SUMMARY.md
```

---

## 8. STATUS

```text
GATE1A STATUS: OPEN / UNCHANGED
GATE1B STATUS: OPEN / UNCHANGED
ANALYTIC CLAIMS BANKED: NONE
```

The purpose of this extension is met: the parts of Universal v8 that are genuinely
mathematics independent of the unresolved analytic source — backend partial-sum control
plus dual BV coefficient norm; local packet control plus synthesis congestion plus
application budget; diagonal baseline plus the *necessary* off-diagonal estimate — are now
frozen as sorry-free Lean theorems, together with the finite countermodels that make the
invalid implications impossible to repeat silently.
