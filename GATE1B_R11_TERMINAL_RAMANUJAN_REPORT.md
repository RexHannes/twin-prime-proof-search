# GATE 1B / R11 — TERMINAL RAMANUJAN (EP-M2) FORMAL SYNC REPORT

Append-only run. Canonical-root-sync state preserved. No new axiom, no `sorry`, no `admit`,
no `native_decide`, no `unsafe`, no `opaque`, no `@[implemented_by]`.

## PREVIOUS BANK

PRESERVED. Nothing pre-existing was deleted, renamed, weakened or re-proved. The two designated
aggregators are the only pre-existing files touched:

* `Gate1B/R11/Frontier/Bank.lean` — thirteen imports plus one aggregation marker
  (`terminalRamanujan_bank_loaded`);
* `Gate1B/R11/Frontier/AxiomAudit.lean` — `#print axioms` lines only.

In particular `J2ResidualCenteredBound`, the three missing exact bridges
(`rootChartRealisation`, `rankDecompositionRealisation`, `j2CenteredSplitRealisation`), the
canonical-sync ten-node cut, `r11_of_canonical_route`, the `RLocTop3` re-ascription and the
legacy twelve-owner bank are all untouched and still open.

## FILES ADDED

`Gate1B/R11/Frontier/CanonicalRootSync/TerminalRamanujan/`

1. `TruncatedMobius.lean` — cutoffs, `λ(d)`, support, `λ ≠ μ*μ`, packetwise firewall
2. `RamanujanFinite.lean` — `c_q(N)` and the divisor identity
3. `RamanujanCoeff.lean` — `a(q)`, `F(N)`, the finite Ramanujan expansion, support of `a(q)`
4. `CofactorAllocation.lean` — `D₁D₂ = qt`, `μ(D₁)μ(D₂)μ(t) = μ(a)`, `H_D(I/d)`, extraction lemma
5. `PrimeAllocation.lean` — allocation kernel, prime-allocation identity, `b`-twisted form
6. `CoefficientFormula.lean` — the exact cofactor-allocation coefficient formula
7. `TerminalSplit.lean` — `F = F_low + F_top` at a parametric cutoff `q₀`
8. `ComplementaryQuotient.lean` — TC1, TC2, TC3, terminal small-complement lemma
9. `RowOperator.lean` — the EP-M2 row operator, raw moment, exact moment split, budget layer
10. `TerminalOwner.lean` — `EPM2Bound`, `EPM2TopBound`, `LowRamanujanBudget`, `CrossTermBudget`
11. `CanonicalBridge.lean` — `epM2Realisation` and the bridges to the canonical `j = 2` owner
12. `Firewall.lean` — exponent predicates, `.624 < 5/8`, Pascadi/Yang firewall
13. `TerminalCut.lean` — route-level cut recomputation
14. `AxiomAudit.lean` — `#print axioms` for all 82 theorems of the layer

Plus this report.

## FILES MODIFIED

`Gate1B/R11/Frontier/Bank.lean` (imports + one marker), `Gate1B/R11/Frontier/AxiomAudit.lean`
(`#print axioms` lines). Nothing else.

## LAKE BUILD

PASS — full repository build, all default targets, 8839 jobs, 0 errors.

## AXIOM AUDIT

PASS. 82 theorems in the new directory: 81 report exactly
`[propext, Classical.choice, Quot.sound]`, one (`unique_new_bridge`) depends on no axioms.
A machine scan of the directory finds no `sorry`, `admit`, custom `axiom`, `native_decide`,
`unsafe`, `opaque` or `@[implemented_by]`.

## TRUNCATED MÖBIUS

PROVED / EXACT. `lam I d = ∑_{uv = d, u ∈ I₁, v ∈ I₂, u,v odd} μ(u)μ(v)`, the two sharp cutoffs
being fields of `Cutoffs`, present in every statement. Support facts: `lam I 0 = 0`,
`lam I d = 0` for `d > Q_max = B₁B₂`, `lam I d = 0` for even `d`. The unrestricted convolution is
*not* substituted: `lam_ne_muConv` kernel-computes `λ = 0 ≠ −2 = (μ*μ)(3)` for `I₁ = I₂ = (0,1]`.
Firewall: `assembled_bound_does_not_imply_packetwise` and `assembled_zero_with_large_packets` —
assembled coefficients can cancel exactly while the packetwise `ℓ¹`/`ℓ²` masses stay bounded
below, so an assembled-cutoff norm bound never implies the packetwise one.

## RAMANUJAN DIVISOR IDENTITY

PROVED. `∑_{q ∣ d} c_q(N) = d · 1_{d ∣ N}` for `d > 0` (`sum_ram_divisors`), via the antidiagonal
form `c_q(N) = ∑_{uv=q} μ(u) v 1_{v ∣ N}` and Möbius inversion.

## FINITE RAMANUJAN EXPANSION

PROVED. `F(N) = ∑_{d ∣ N} λ(d) = ∑_{0 < q ≤ Q_max} a(q) c_q(N)` with `Q_max = B₁B₂`
(`Fsum_eq_ramanujan_expansion`). Exact rational layer; no asymptotics anywhere.

## COEFFICIENT FORMULA

PROVED. `a(q) = ∑_{u ∈ I₁, v ∈ I₂ odd, q ∣ uv} μ(u)μ(v)/(uv)` with its divisor form
`a(q) = ∑_{q ∣ d ≤ Q_max} λ(d)/d` (`aCoeff_eq_aDiv`). Support: `a(q) = 0` for even `q`
(`aCoeff_eq_zero_of_even`) and for `p³ ∣ q` (`aCoeff_eq_zero_of_cube_dvd`).

## COFACTOR ALLOCATION

PROVED, in full, not only prime-wise:

* `D1_mul_D2` : `D₁D₂ = (a b²) t = q t`;
* `moebius_D1_mul_D2` : `μ(D₁) μ(D₂) μ(t) = μ(a)`;
* `harm A B d D` : the finite harmonic Möbius interval sum, division-free (`A < d n ≤ B`);
* `moebius_interval_extraction` : `∑_{u ∈ (A,B], u odd, D ∣ u} μ(u)/u = (μ(D)/D) H_{2D}(I/D)`
  for odd `D > 0`;
* `alloc_indicator` : `∑_{r s t = a} μ(t) 1_{rt ∣ u} 1_{st ∣ v} = 1_{a ∣ uv}` for squarefree `a`
  (proved through the multiplicative allocation kernel `1_{·∣u} * 1_{·∣v} * (μ·1_{·∣u}·1_{·∣v})`);
* `alloc_indicator_with_b` : its `b`-twisted form `= 1_{a b² ∣ uv}` for squarefree `u, v`;
* `aCoeff_cofactor_allocation` :
  `a(q) = (μ(a)/q) ∑_{r s t = a} (1/t) H_{2D₁}(I₁/D₁) H_{2D₂}(I₂/D₂)`, `q = a b²`,
  `a, b` squarefree, coprime, odd.

`t` is the designated inclusion–exclusion variable: the harmonic factors carry coprimality to
`2Dᵢ` only, so the residual cofactors may still share primes with the opposite variable. `t` is
**not** formalised as a gcd anywhere.

## ROW OPERATOR

DEFINED / EXACT. `rowOp Z β₅ F e s = ∑_{z ∈ Z, e ∣ sz+2} β₅(z) F((sz+2)/e)`; `β₅` abstract, no
analytic property proved or assumed. `rowOp_add` (additivity in `F`), `rowOp_arg_pos`
(`(sz+2)/e ≥ 1` whenever the divisibility holds — so the split needs no side condition) and
`rowOp_terminal_split` (`R = R_low + R_top`).

## RAW MOMENT

DEFINED / EXACT. `moment E S W R = ∑_{e,s} W(s) |R(e,s)|²` and `crossTerm`.
`moment_split` : `𝔐_raw = 𝔐_top + 2𝔠 + 𝔐_low` — pure algebra, no estimate.

## LOW/TOP SPLIT

PROVED. `Fsum_eq_low_add_top` : `F = F_low + F_top` for every admissible cutoff `0 ≤ q₀ ≤ Q_max`,
with the degenerate cases `q₀ = 0` and `q₀ = Q_max`. The moment-level statement is deliberately
*not* an asymptotic identity: `raw_moment_budget` has the shape *supplied inequalities ⇒
raw-to-top reduction*, and `moment_algebra_does_not_bound` shows the algebra alone gives nothing.

## COMPLEMENTARY QUOTIENT TC1

PROVED. `a(q) = ∑_{0 < m ≤ Q_max/q} λ(qm)/(qm)` (`aCoeff_complementary_quotient`), plus the
widened form `aCoeff_sum_over_quotients` used by TC2.

## TC2

PROVED. `F_top(N) = ∑_m (1/m) ∑_{q₀ < q ≤ Q_max, qm ≤ Q_max} (λ(qm)/q) c_q(N)`.

## TC3

PROVED. `F_top(N) = ∑_{0 < d ≤ Q_max} (λ(d)/d) ∑_{q ∣ d, q > q₀} c_q(N)`.

## TERMINAL SMALL-COMPLEMENT LEMMA

PROVED, cutoff-parametric, in both the integer form (`Q_max ≤ q₀ R_cut`, `q > q₀`, `qm ≤ Q_max`,
`m > 0` ⇒ `m < R_cut`) and the rational form `q₀ = Q_max / R_cut`. No `R_cut = x^{o(1)}` claim is
formalised; `L^{A+200} exp(2(log L)³)` does not occur.

## EP-M2 FORMAL OBJECT

`EPM2Bound M S0 : Prop` — the raw EP-M2 moment budget, an uninhabited interface.

## EP-M2-TOP FORMAL OBJECT

`EPM2TopBound Mtop S0 : Prop` — the single new terminal analytic owner, uninhabited, not an
axiom. `unique_new_bridge` / `terminal_owner_below_j2` certify that it is the only new terminal
owner and that it sits strictly below the retained `j = 2` owner.

## LOW-BAND BUDGET STATUS

`LowRamanujanBudget` — OPEN (uninhabited interface; consumed only as a hypothesis).

## CROSS-TERM STATUS

`CrossTermBudget` — OPEN (uninhabited interface; consumed only as a hypothesis).

## EPM2TopBound STATUS

OPEN. `terminal_owner_still_open` exhibits a family violating it, so it is not a theorem and is
load-bearing (`epM2_needs_terminal_owner`).

## BRIDGE TO J2

`j2_of_epM2` : `epM2Realisation DB M → EPM2Bound M S0 → J2ResidualCenteredBound DB S0`.
`j2_of_terminal_route` : realisation + `EPM2TopBound` + `CrossTermBudget` + `LowRamanujanBudget`
⇒ `J2ResidualCenteredBound`. `dbRaw_budget_of_terminal_route` continues along the pre-existing
adapter to the raw `j = 2` operator budget, so the chain
`canonical root → j = 2 → EP-M2 → EP-M2-top` is machine-checked arrow by arrow, with the
analytic endpoint visibly open.

## EXACT REALISATION MISSING?

YES — exactly one: `epM2Realisation DB M`, the statement that the canonical centered `j = 2`
residual family *is* the EP-M2 row moment family. It is a proposition, never inhabited, not an
axiom, and it is not a duplicate of the three pre-existing missing bridges: those identify the
canonical root, the rank decomposition and the centered `j = 2` chart, all *above* the `j = 2`
owner, whereas this one identifies the object *below* it (minimal non-duplicating placement).
`epM2Realisation_load_bearing` shows the bridge cannot be dropped.

## CANONICAL CUT BEFORE

Ten nodes: `rootChartRealisation`, `rankDecompositionRealisation`, `j2CenteredSplitRealisation`,
`canonicalRootErrorBudget`, `branchBound1/3/4/5`, `principalBudget`, `j2ResidualCenteredBound`.

## CANONICAL CUT AFTER

UNCHANGED — the same ten nodes (`canonical_cut_retained`, `canonical_cut_length_retained`
re-ascribe the previous computation verbatim). Because no exact realisation is established,
`J2ResidualCenteredBound` is **retained** and `EPM2TopBound` is recorded as a **subordinate
experimental route**, not a replacement (`tcutSet_r11`, `terminal_nodes_offroute`). The price of
that subordinate route is computed: `tcutSet_j2ViaTerminal = [EPM2TopBound, CrossTermBudget,
LowRamanujanBudget, epM2Realisation]`.

## RLocTop3 STATUS

Unchanged: proved independent of the canonical root identity and proved off the canonical-sync
route. Nothing in this run touches it.

## R11 STATUS

OPEN.

## HSTAR STATUS

OPEN.

## GATE1B STATUS

OPEN.

## TWIN PRIME CLAIM

NONE.

## MINIMUM FORMAL OPEN CUT

Route level (unchanged): the ten canonical-sync nodes, of which exactly one,
`J2ResidualCenteredBound`, is the `j = 2` owner.

Terminal route (new, subordinate, four nodes): `epM2Realisation` (missing exact identification),
`EPM2TopBound`, `CrossTermBudget`, `LowRamanujanBudget`.

## NEXT ARISTOTLE TARGET

`epM2Realisation`: identify, in the existing Lean objects, the canonical centered `j = 2`
residual family with the EP-M2 row moment family — i.e. prove that the packet/common-`e`
residual operator of `J2ResidualOperator.lean` equals `moment` of `rowOp` for an explicit choice
of `Z`, `β₅`, `W`, `E`, `S`. Until that identity is proved, the terminal route cannot shrink the
canonical cut, no matter what is proved about `EPM2TopBound`.

## FIREWALL

No external analytic theorem is formalised from an informal range description. Only exponent
predicates and exact rational inequalities are proved (`.624 < 5/8`, `.624` and `.621` in the
Pascadi window). `TerminalTriplyFactorableHypothesis` is defined as a purely structural cutoff
statement; its only proved consequence is the small-complement relation, and
`factorable_structure_does_not_imply_topBound` records that it does **not** imply the terminal
analytic owner. No `PascadiBound`-style theorem is created or assumed.

## SUCCESS CRITERIA

GOLD A: met — all finite truncated-Möbius / Ramanujan / complementary-quotient identities are
Lean-proved and sorry-free, and the cofactor-allocation formula is proved in full generality.

GOLD B: met — EP-M2 and EP-M2-top are exact formal objects with algebra, analytic hypotheses and
budget implication kept in three separate layers.

GOLD C: not claimed — no exact realisation of the canonical `j = 2` operator as the EP-M2 row
moment is established, so the canonical cut is not shrunk.

GOLD D: met — exactly one minimal bridge proposition (`epM2Realisation`) is isolated, and every
theorem around it is proved.
