# TWIN GATE1B / R11 — residue-aware, modulus-3 lifting and generated-grammar formal sync

Append-only formal frontier sync.  **Gate1A was not touched.**  Nothing pre-existing in
`Gate1B/R11/Frontier/` was rewritten, renamed, deleted or weakened: `OccupiedRowKernel.lean`,
`ProductFibrePushforward.lean`, `EmptySiteRepairTransfer.lean`, `UnmodifiedRowInterpolation.lean`,
`CriticalMixedIncidence.lean`, `RealOverlapSupport.lean`, `CriticalMaskFirewall.lean`,
`NewCritStatusBank.lean` and every earlier exact R11 module are unchanged, and `R_hi`,
`R_newcrit`, the old firewalls, the unmodified-row source and the empty-site repair transfer
remain in the bank as historical/banked coordinates.

---

## FILES ADDED

| File | Contents |
| --- | --- |
| `Gate1B/R11/Frontier/ThreeFactorSelectedOwner.lean` | `lambdaStar` (three-factor selected coefficient), support/coprimality algebra, `τ₃` divisor bound; the centered kernel `δ_d`, `u_d`, `centered_d`; the finite selected consumer; `PascadiRectangularInput` (external analytic interface, uninhabited). |
| `Gate1B/R11/Frontier/ResidueModulusLift.lean` | CRT multiplicativity of `δ` and `u`, the **modulus-lifting identity**, `LocalPrincipalCorrection` and its non-erasure firewall, the exact logarithm split. |
| `Gate1B/R11/Frontier/Mod3TargetAlgebra.lean` | residue selectors, the **mod-3 selector identity**, `χ₃` (completely multiplicative) and the `χ₃` form, the mod-3 caller as a *derived* caller via modulus lifting, `Mod3CenteredCaller` (external interface, uninhabited), the **direct-residue firewall** (finite countermodel). |
| `Gate1B/R11/Frontier/ResidueAwareProjection.lean` | `coordAvg`, `P_j = binAvg`, `T_j = resAvg`; `P² = P`, `T² = T`, `P T = P`, `T P = P`; commutation of independent coordinates; `Q_old`, `Q₃`; **`Q₃ Q_old = Q₃`**; "already removed stays removed". |
| `Gate1B/R11/Frontier/ResidueAwareTopTelescoping.lean` | the **residue-aware telescoping identity** (recursive and literal indexed form), no-double-charge decomposition, the selected centered functional `E_λ*`, the exact source definition of **`R_loc-top,3`**, and `RLocTop3Bound` (never inhabited). |
| `Gate1B/R11/Frontier/GeneratedGrammarFreshPrime.lean` | divisors of a fresh-prime multiple, the **unshifted fresh-prime convolution identity** `(f∗g)(pR) = ∑_{e|R}[f(pe)g(R/e) + f(e)g(pR/e)]`, and its form for the repository's `semExpr (.conv …)`. |
| `Gate1B/R11/Frontier/GeneratedGrammarVariation.lean` | amplitude budget `a(E)` and its structural recursion + soundness; `pathVar`, `scaledVar`, `divVar`; constants / sharp intervals / monotone ramps / products / sums / scalar multiples / **convolution**; the structural bound `v(E) ≤ a(E)·T(E)`; **zero-extension cost** `≤ 2ω(R)a(E)` (and the eleven-prime specialisation); the **evaluation-point firewall**. |
| `Gate1B/R11/Frontier/HistoricalFordGrammarInterface.lean` | `RealFordGrammarCertificateData` (wraps the repository's existing `RealFordGrammarCertificate`, **not inhabited**, not an axiom); `W_hist`, `W_rec`, `Δ`; the exact linear identities; the **`Q₃`-provenance quotient** and `ConditionalConsumerComparison` (evidence object, uninhabited). |
| `Gate1B/R11/Frontier/ResidueAwareStatusBank.lean` | the **disconnected-hypergraph firewall**, the **mod-3 / mod-5 firewall**, the status taxonomy with every `kernelProved` row re-ascribed to an actual theorem, and the current frontier object `residueAwareHistorical_open_frontier`. |
| `TWIN_GATE1B_R11_RESIDUE_AWARE_GRAMMAR_FORMAL_SYNC_REPORT.md` | this report. |

## FILES MODIFIED

* `Gate1B/R11/Frontier/Bank.lean` — imports of the nine new modules and the aggregation marker
  `residueAware_bank_loaded`.  Nothing else changed.
* `Gate1B/R11/Frontier/AxiomAudit.lean` — `#print axioms` for every new principal theorem.

No other repository file was touched.  Gate1A is untouched.

---

## THEOREM-BY-THEOREM EVIDENCE LEVEL

### KERNEL_PROVED

**Selected three-factor source algebra.**
`lambdaStar_apply` (triple-sum form), `lambdaStar_zero`, `lambdaStar_one`, `lambdaStar_support`
(exact support law), `threeFactor_pairwise_coprime` (pairwise coprimality and squarefreeness of
the three factors on squarefree moduli), `abs_lambdaStar_le_tau3` (divisor bound),
`centeredSel_one`, `selectedConsumer_add`, `selectedConsumer_smul`.

**Modulus lifting (§4).**
`deltaSel_mul_of_coprime` (CRT), `uSel_mul`, `modulus_lift_identity`:

```
I_h(n)(δ_d(n) − u_d(n)/φ(d)) = (δ_{hd}(n) − u_{hd}(n)/φ(hd)) + LocalPrincipalCorrection h d n
```

with `LocalPrincipalCorrection h d n = u_d(n)/φ(d) · (u_h(n)/φ(h) − I_h(n))`.
`modulus_lift_identity_odd` is the same statement carrying the research note's oddness
hypothesis on `h`; the proof does not need it — only `gcd(h,d) = 1` — and this is recorded in
the docstring.  Firewall: `modulus_lift_does_not_erase_localPrincipalCorrection` and
`lifted_kernel_ne_naive_product` exhibit explicit finite data with a nonzero correction, so
modulus lifting provably does **not** erase the local principal correction.

**Logarithm split (§5).** `log_split`, `log_split_shift`.

**Mod-3 selector algebra (§6).** `mod3_selector_identity`

```
1_{p ≡ a (3)} b(R) = b_{3−a}(R) + I₃(pR)(b_a(R) − b_{3−a}(R))      (a ∈ {1,2}, 3∤p, 3∤R),
```

`chi3_mul`, `indMod3_one_eq_chi3`, `indMod3_two_eq_chi3`, `mod3_selector_chi3_form`,
`mod3_caller_via_modulus_lifting` (the mod-3 caller is *derived* from the lifting identity at
`h = 3`, correction included).

**Direct-residue firewall (§7).** `residue_restriction_can_destroy_mean_zero`,
`restricted_residue_not_automatically_meanZero`: an explicit finite coefficient with total mass
`0` and mass `1` on the class `n ≡ 1 (3)`.

**Projection algebra (§8–9).** `binAvg_idem`, `resAvg_idem`, `resAvg_binAvg`, `binAvg_resAvg`
(`P T = P` via the fibrewise decomposition), `binAvg_comm`, `binAvg_resAvg_comm`, `resAvg_comm`
(independent coordinates), `subT_subP_self`, `subT_subP_comm`, `Q3_subP_comm`, and
**`Q3_Qold : Q₃ Q_old = Q₃`**.

**Telescoping (§10).** `Qold_sub_Q3_eq_telescope` (exactness) and `telescope_explicit`

```
Q_old W − Q₃ W = ∑_{t<r} (∏_{s<t}(I−T_{j_s})) (T_{j_t} − P_{j_t}) (∏_{s>t}(I−P_{j_s})) W .
```

`suffix_stays_P_centered` (`P_k Q_old W = 0` for every removed coordinate — no term reintroduces
an already removed ordinary component) and `residual_stays_T_centered`
(`T_k Q₃ W = 0`: `Q₃ W` remains centered under every `T_j`).

**§11–12.** `Wres3 = Q₃ W`, `RlocTop3` and `RlocTop3_def` (source definition only),
`no_double_charge`, `no_double_charge_middle`, `selectedCenteredFunctional_add`,
`selectedConsumer_three_component` (the ordinary owned component, the residue-refinement
difference and `R_loc-top,3` add up exactly; nothing is charged twice).

**Generated grammar (§13–18).** `divisors_mul_prime`, `divisors_mul_prime_disjoint`,
`dconv_fresh_prime`, `dconv_fresh_prime_squarefree`, `semExpr_conv_fresh_prime`;
`ampBudget_nonneg`, `ampBudget_add_le`, `ampBudget_mul_le`, `ampBudget_smul_le`,
`ampBudget_conv_le`, `norm_semExpr_le_ampBudget`; `pathVar_add_le`, `pathVar_sub_le`,
`pathVar_smul`, `pathVar_mul_const`, `pathVar_const_sub`, `pathVar_mul_le`, `pathVar_sum_le`,
`pathVar_of_monotone_le`, `boxCutoff_eq_sub`, `rampR_antitone`, `scaledVar_atom_le`;
`scaledVar_dconv_le` (convolution, sharp divisor-sum form), `scaledVar_dconv_le_two_pow`,
`scaledVar_semExpr_le` (`v(E) ≤ a(E)·T(E)` on the declared variation-controlled sub-grammar);
`pathVar_supported`, `pathVar_zero_extension_le`, `countP_dvd_le_omega`,
`zero_extension_cost_omega` (`≤ 2ω(R)A`), `zero_extension_cost_eleven` (`≤ 22A`);
`unshifted_variation_does_not_imply_shifted` and `semExpr_shift_not_universal`
(**evaluation-point firewall**: `E(pR)` versus `E(pR+2)`).

**Firewalls (§22–23).** `disconnected_hypergraph_firewall`,
`disconnected_does_not_kill_top_interaction`; `finrank_units_mod3 = 2`,
`finrank_units_mod5 = 4`, `mod3_unit_span`, `mod5_unit_two_function_span_fails`,
`mod3_to_mod5_not_automatic`.

**Ledger re-ascriptions.** `bank_modulus_lifting`, `bank_local_principal_correction`,
`bank_log_split`, `bank_mod3_selector`, `bank_mod3_derived_caller`,
`bank_direct_residue_firewall`, `bank_q3_qold`, `bank_residue_aware_telescoping`,
`bank_fresh_prime_convolution`, `bank_amplitude_recursion`, `bank_evaluation_point_firewall`,
`bank_disconnected_gate_firewall`, `bank_mod3_mod5_firewall`, plus
`frontier_open_rows_not_proved`, `rlocTop3_analytic_bound_open`,
`realFordGrammarCertificate_open`, `downstream_all_open`.

### CONDITIONAL_ANALYTIC / EXTERNAL_ANALYTIC (defined, never inhabited, never an axiom)

* `PascadiRectangularInput` — the numerical rectangular estimate for the three-factor selected
  owner.  Its only consequence drawn here is `selectedConsumer_bound_of_pascadi`.
* `Mod3CenteredCaller` — the modulo-3 centered analytic caller (arbitrary-log saving).
* `LargeSquarefullTailBound`-style usage is unchanged from the earlier delta; no new analytic
  proposition is inhabited.
* `ConditionalConsumerComparison` — the conditional consumer comparison of the current analytic
  report; its only consequence is `consumer_difference_reduces_to_Q3`.
* The local principal analytic estimate is **not** formalised: only the exact algebraic
  decomposition that isolates it is.

### OPEN

`RealFordGrammarObligation` / `RealFordGrammarCertificateData` (historical realisation),
the exact historical weighted pushforward, the actual expression parameter/cost certificate,
the `Q₃ Δ` analytic bound, `RLocTop3Bound` (`R_loc-top,3`), `R_newcrit`, `R11`, global Gate 1B,
HSTAR, twin prime.

---

## AUDIT NOTES (corrections recorded, not silently absorbed)

1. **Oddness of `h` is not needed** for the modulus-lifting identity; `gcd(h,d)=1` suffices.  The
   research-note form with `Odd h` is kept as `modulus_lift_identity_odd`.
2. **Convolution variation constant.**  The research bank states
   `v_r(f ∗ g) ≤ 2^{r−1}(a(g)v(f) + a(f)v(g))`.  What is kernel-proved here is the sharp
   divisor-sum inequality `scaledVar_dconv_le` (no constant loss) and the corollary with constant
   `2^r`.  The literal `2^{r−1}` is **not** proved with this normalisation and is not claimed.
3. **Variation-controlled sub-grammar.**  The structural bound `v(E) ≤ a(E)T(E)` is proved for
   the declared sub-grammar whose atoms are constants, sharp boxes and ramps.  The Möbius atom,
   the Mellin twist and the perfect-power pullback are explicitly excluded: they carry no bounded
   finite path variation, and no claim about them is made.
4. **`Q₃ Δ` is a definition, not an estimate.**  Its analytic bound is not inhabited anywhere.

---

## MODULUS-LIFTING STATUS

KERNEL-PROVED, with the local principal correction named, isolated, and *proved not to vanish in
general*.  The firewall "modulus lifting does not erase the local principal correction" is a
theorem, not a comment.

## LOCAL PRINCIPAL STATUS

Algebra: KERNEL-PROVED.  Analytic estimate: EXTERNAL, not formalised, not inhabited.

## RESIDUE-AWARE PROJECTION BANK

`P² = P`, `T² = T`, `PT = P`, `TP = P`, coordinate commutation, `Q₃ Q_old = Q₃`, exact
telescoping, `P`-centering of the suffix factors and `T`-centering of `Q₃ W`: all KERNEL-PROVED.

## GENERATED GRAMMAR BANK

Fresh-prime convolution identity, amplitude recursion with soundness, the finite variation
calculus, the structural budget bound, the zero-extension cost, and the evaluation-point
firewall: all KERNEL-PROVED at the declared finite-algebra scope.  The repository's actual
`V11FMPerronGrammar` / `V11GeneratedExpression` definitions are reused, not re-created.

## HISTORICAL REALISATION OBLIGATION

`RealFordGrammarCertificateData` carries packet, normalisation, sign, multiplicity, parameter
values and evaluation point, and wraps the repository's existing `RealFordGrammarCertificate`.
It is **not inhabited** and **not an axiom**.  Status: OPEN.

## CURRENT EXACT FRONTIER

`R_loc-top,3` — kernel-proved *source definition* (`RlocTop3`), analytic bound OPEN
(`RLocTop3Bound` never inhabited).

## ANALYTIC RESULTS DELIBERATELY NOT KERNEL-PROVED

The Pascadi rectangular estimate; the modulo-3 centered analytic caller; the average-variation
closing theorem; the local principal analytic estimate; any arbitrary-log bound for the canonical
selected target; the `Q₃ Δ` error estimate.

## DEDICATED BUILD

`lake build Gate1B.R11.Frontier.Bank` and `lake build Gate1B.R11.Frontier.AxiomAudit`: **PASS**,
no errors and no warnings.  Every new module also builds individually.

## REPOSITORY-WIDE DIAGNOSTIC BUILD

`lake build`: **PRE-EXISTING FAILURE**, unchanged from the baseline — the package still refers to
`RequestProject/FixedCertificateAlgebra.lean`, a file that does not exist in the repository and
never has (it is absent already in the initial commit).  Unrelated to this work; not repaired, no
new failure introduced.

## AXIOM AUDIT

Every new principal theorem depends only on a subset of `{propext, Classical.choice, Quot.sound}`
(several on none).  A machine search over `Gate1B/R11/Frontier/` finds no `sorry`, no `admit`, no
custom `axiom`, no `native_decide`, no `@[implemented_by]`, no `unsafe`, no `opaque`.

---

## STRICT FINAL OUTPUT

```
UNMODIFIED-ROW BANK:                PRESERVED
MODULUS-LIFTING IDENTITY:           KERNEL-PROVED
LOCAL PRINCIPAL CORRECTION:         KERNEL-PROVED
MOD-3 SELECTOR ALGEBRA:             KERNEL-PROVED
MOD-3 ANALYTIC CALLER:              EXTERNAL-ANALYTIC / CONDITIONAL (not banked)
RESIDUE-AWARE PROJECTIONS:          KERNEL-PROVED
Q3 * Qold = Q3:                     KERNEL-PROVED
RESIDUE-AWARE TELESCOPING:          KERNEL-PROVED
R_loc-top,3:                        KERNEL-PROVED DEFINITION
R_loc-top,3 ANALYTIC BOUND:         OPEN
FRESH-PRIME GRAMMAR CONVOLUTION:    KERNEL-PROVED
GRAMMAR AMPLITUDE RECURSION:        KERNEL-PROVED
GRAMMAR VARIATION RECURSION:        KERNEL-PROVED (convolution constant 2^r; 2^{r-1} not claimed)
UNSHIFTED / SHIFTED FIREWALL:       KERNEL-PROVED
RealFordGrammarCertificate:         OPEN (defined, never inhabited, not an axiom)
HISTORICAL WEIGHTED PUSHFORWARD:    OPEN
Q3 PROVENANCE RESIDUAL:             OPEN
DISCONNECTED-GATE FIREWALL:         KERNEL-PROVED
MOD3 -> MOD5 AUTOMATIC EXTENSION:   REJECTED_FALSE
CURRENT FORMAL FRONTIER:            R_loc-top,3
MAJOR NEW TYPE-II NECESSITY:        NOT ESTABLISHED
R11:                                OPEN
GLOBAL GATE1B:                      OPEN
HSTAR:                              OPEN
TWIN PRIME:                         OPEN
DEDICATED BUILD:                    PASS
REPOSITORY BUILD:                   PRE-EXISTING FAILURE
AXIOM AUDIT:                        PASS
```

STOP.
