# CURRENT PROGRAMME — MASTER CONTINUATION REPORT

Append-only continuation of `/workspace/request-project`.
New material lives entirely in `RequestProject/CurrentProgramme/` under the Lean
namespace `TwinPrimeProject.CurrentProgramme`. **No pre-existing file was
deleted, renamed, weakened, or restated.**

Machine-readable counterparts of everything below:

* `RequestProject/CurrentProgramme/CurrentStatus.lean` — the status ledger, with
  `Ledger.no_closed_rows`, `Ledger.ledger_is_honest`, `Ledger.end_of_run_nonclaims`
  kernel-proved.
* `RequestProject/CurrentProgramme/DependencyGraph.lean` — the master DAG.
* `RequestProject/CurrentProgramme/AxiomAudit.lean` — `#print axioms` on every
  principal new declaration.
* `CURRENT_GATE_ARCHITECTURE_AND_STATUS.md` — the drafter-facing architecture file.

If this document and the Lean ledger ever disagree, **the Lean ledger is
authoritative.**

---

## A. BASE COMMIT / WORKSPACE GUARD

| item | value |
|---|---|
| working directory | `/workspace/request-project` |
| branch | `main` |
| base commit at start of run | `b366f7c` (single historical commit) |
| baseline `lake build` | PASSED, 8594 jobs |
| final full `lake build` | PASSED, 8610 jobs, `grep -cE '^error'` = 0 |
| `lakefile.toml` defaultTargets | `RequestProject`, `Gate04Root`, `Gate1A`, `Gate1B`, `UniversalV8`, `Universal` |

The library globs are of the form `RequestProject.+`, so every new module under
`RequestProject/CurrentProgramme/` is inside a default target and is covered by
the full build. This was checked rather than assumed.

### Frontier reset (performed)

The v13 human ledger entry

```
FIRST GATE1B ANALYTIC OPEN : SHIFT-SOURCE-LINKED-CHAR45
```

is recorded in `Ledger.gate1B` with status
`supersededAsControllingFrontier` — **not** as false, and the original v13 text
is untouched. The current controlling first analytic open is
`RANKONE-ENDPOINT-U-OFFDIAG45`.

`TWO_OUTER_VARIABLE_F3_KERNEL` was **not** reopened. It is recorded as
`notCurrentlyRequired` with the explicit comment that it remains a genuine open
research object; per the priority order it becomes current only if the literal
Ford packet census demands it, and the census is unpopulated (Section K).

### Census of named objects (literal `rg` search of the repository)

**Present and reused:** `Gate1BClosed` and `FullTypeIIBound`
(`RequestProject/NANC/Gate1BDet2/Gate1BInterfaces.lean`), the v10 leaf bridge
`gate1B_closed_of_exact_inputs`, `RealFordGrammarCertificate` (v11, uninhabited),
`TwinPrimeProject.FixedCertificate.k0EqualFactorR9Value70`
(`RequestProject/FixedCertificateAlgebra.lean`),
`RequestProject.UnconditionalRankinRadical`, the Gate01 / Gate04Root / Gate1A /
Gate1B / Universal / UniversalV8 banks, QK56 and Shifted-TT\* machinery,
`FMToGate` census types, SHAPE counterguards.

**Absent** (verified absent, therefore *not* reconstructed from prose):
`Erdos287`, `WindowPairSupply`, `BalancedSeven`, `AffineMuLog`, `Omega7`,
`Factorial`, `Motohashi`, `PURE5`, `RANKONE`, `FCL`, Ford's `Proposition 7.22`,
`equation (7.23)`, `C(R)`, `R(P)`, `G(d;n)`.

---

## B. REUSED BANKS

Nothing in Sections C–Q duplicates existing mathematics. Concretely reused:

* `TwinPrimeProject.FixedCertificate.k0EqualFactorR9Value70` — reused verbatim to
  discharge `R9LeakageArithmetic.r9_H_value_seventy`. The alternating sum
  `Σ_{j=0}^{4} (−1)^j C(9,j) = 70` was **not** re-proved.
* `Gate1BClosed` / `FullTypeIIBound` — used as the *existing* targets. No stronger
  target was invented; in particular `FullFMTypeII_OneSixth` was **not** created.
* the v10/v11/v12 QK56 and leaf-bridge compilers — referenced by name from the
  ledger, not re-derived.
* Mathlib's `Finset.sum_range_by_parts` (discrete Abel), `ZMod.dft` and its
  Parseval/inner-product API, `Finset.sum_powerset_neg_one_pow_card`.

New-layer size: 18 modules, 3171 lines, 209 top-level declarations.

---

## C. GATE1B ENDPOINT SOURCE

### C1. Normalisation firewall — `NormalisationFirewall.lean`

The physical defect is defined literally:

```
defect W Y n = (Λ n − 1) · W (n / Y) / Real.log n
```

Kernel-proved:

* `defect_prime` : for `p` prime, `defect W Y p = (1 − 1/log p) · W (p/Y)`
  — the exact prime specialisation.
* `defect_prime_ge_half` : a quantitative lower bound at large primes
  (via `two_lt_log_eleven`).
* `prime_defect_refutes_pointwise_log_bound` : **the claim
  `‖delta_i‖_∞ ≪ (log X)^{-1}` is false.** The prime-supported part is `O(1)`,
  not `o(1)`.

This is a *counterguard*: it blocks the false implication
`prime-supported defect ⇒ pointwise log^{-1}`. No asymptotic `L¹`/`L²` estimate
was formalised, because the required prime-counting input is not kernel-proved
in this repository; those remain human/externally-audited rows.

### C2. Motohashi — interface only

`AnalyticInterfaces.MotohashiABCInput` is a structure whose fields state the
literal A/B/C propositions (divisor-type growth; Siegel–Walfisz for
nonprincipal small-conductor characters; Bombieri–Vinogradov with
`Σ_q max_{y≤x} max_{(a,q)=1} |E_f(y;q,a)|`). It is **uninhabited**: the module
contains no constructor application and no `Classical.choice`-based inhabitant.
Motohashi's analytic theorem is *not* proved in Lean.

`MotohashiFamilyUniformity` is a separate uninhabited interface carrying the
publication pin: the family `Δ_{i,Y,τ}(n) = δ_i(n) n^{iτ}` needs *uniform*
constant dependence in `(Y, τ)`. It is recorded as
`MOTOHASHI-FAMILY-UNIFORMITY45 : EXTERNALLY_AUDITED`, and separating it does
**not** downgrade the polylog-`k` interior row.

### C3. Smooth localisation compiler — `SmoothLocalisation.lean`

Source-independent finite algebra, fully kernel-proved:

* `wDiscrepancy_abel` — discrete Abel summation for the weighted discrepancy.
* `wDiscrepancy_le` / `wDiscrepancy_le_uniform` — if
  `max_y max_a |E(y;q,a)| ≤ T q`, then
  `max_a |weighted discrepancy| ≤ (‖F‖_∞ + Var F) · T q`.
* `supNorm_alone_insufficient` — the variation term cannot be dropped.

This is the Lean-safe core underlying `LOCALIZED-FIVEFOLD-MOTOHASHI45`. The BV
estimate itself is **not** claimed; the row is `CONDITIONAL_COMPILER`.

### C4. Exact rank-one line source — `RankOneLineAlgebra.lean`

Over `ℤ`, with `v_t = v₀ + ℓ t`, `z_t = z₀ + u t`:

* `lineDet2_propagates` : `u·v₀ + 2 = ℓ·z₀ → u·v_t + 2 = ℓ·z_t`.
* `endpoint_residue_zmod` : `v₀ ≡ −2·u⁻¹ (mod ℓ)`.
* `negTwoInv` : `u ↦ −2·u⁻¹` is an involution and hence a **bijection of the unit
  group mod ℓ** (packaged as an `Equiv`).
* an explicit **counterguard** proving that bijectivity mod `ℓ` does **not** give
  bounded multiplicity for integers `u` in a long interval — the fibre is
  retained explicitly everywhere downstream.

### C5. Finite line Fourier — `FiniteLineFourier.lean`

`lineZ`, `lineB` are defined through `ZMod.dft`, keeping the normalisation
explicit. Proved: `sum_stdAddChar_mul`, `dft_inner` (finite Parseval),
`parseval_lineZ`, `parseval_lineB`, and the mixed moment
`M_{u,ℓ} = (1/H) Σ_k Z(k) conj(B(k))`. **No analytic Fourier estimate** is
formalised, and no pointwise `L^{-5}` bound on `b5` is asserted anywhere.

---

## D. ENDPOINT DIAGONAL / OFFDIAGONAL

### D1. Exact bilinear parent — `EndpointBilinear.lean`

The weighted residue source is defined with the load-bearing weight retained:

```
A_{ℓ,a,k} = Σ_{u ~ U, u ≡ −2 a⁻¹ (mod ℓ)}  a4(u) · Z_{u,ℓ}(k)
```

The weight `a4(u) Z_{u,ℓ}(k)` is never replaced by an unweighted average over
`a`; a counterguard records that substitution as invalid.

`endpointBilinearParent` is the exact finite bilinear form
`(1/H) Σ_k Σ_ℓ Σ*_{a mod ℓ} A_{ℓ,a,k} conj(E_{ℓ,a,k})` — an **identity / source
dictionary only**, carrying no bound.

Expanding `Σ_a |A|²` produces the pair condition `u₁ ≡ u₂ (mod ℓ)`, split
*exactly* and disjointly into `u₁ = u₂` and `u₁ ≠ u₂`:

* `residueEnergy_split` : `residueEnergy = diagEnergy + offdiagEnergy`, exact.
* `diagEnergy_eq_sum_sq` : the diagonal child in closed form.
* `congruentPairs_split`, `congruentPair_param` (in `RankOneLineAlgebra`) give
  the exact parametrisation `u₂ = u₁ + jℓ`.

### D2. Endpoint U-diagonal exponent bank — `EndpointExponentBank.lean`

Exact `ℚ` arithmetic, kernel-checked, with `U = Y⁴, V = Y⁵, R = Y^{5/2},
H = Y^{5/2}, X = Y⁹`:

```
eDiag     = 5 + (5/2 + 4)/2 = 33/4
X         = Y^{36/4}
eMargin_Y = 36/4 − 33/4 = 3/4
eMargin_X = (3/4)/9 = 1/12
```

`diag_scale_rpow` and `diag_scale_relative_X` give the `rpow` translation for
`X > 0`; `margin_lt_one` records `1/12 < 1`. Label
`RANKONE-ENDPOINT-U-DIAGONAL45 : CAPACITY_ONLY`. The analytic
large-sieve/BDH variance input is **not** encoded as proved; it is the
uninhabited `RankOneEndpointUDiagonalInput`, exposed as a field of the endpoint
compiler.

### D3. Endpoint U-offdiagonal — the load-bearing algebra (PRIORITY 2, DONE)

Kernel-checked over `ℤ` in `RankOneLineAlgebra.lean`:

* `offdiag_basepoint_shift` : `z₀(u + jℓ) − z₀(u) = j·v₀`.
* **`offdiag_line_difference`** :

  ```
  z₂(t₂) − z₁(t₁) = u·(t₂ − t₁) + j·(v₀ + ℓ t₂)
                  = u·Δt + j·v_{t₂}
  ```

  This is the identity the prompt flags as current load-bearing source algebra.
  It is proved by integer ring algebra (no `decide`, no numerics), and a separate
  numeric instance is checked as a sanity guard. `#print axioms` reports
  `[propext]` for it.

The exact off-diagonal energy

```
Σ_ℓ Σ_{j ≠ 0} Σ_u  a4(u) conj(a4(u + jℓ)) Z_{u,ℓ}(k) conj(Z_{u+jℓ,ℓ}(k))
```

is defined as `offdiagEnergy` — a **finite source object with no estimate**.
The requirement is isolated as the uninhabited interface
`RankOneEndpointUOffdiagInput`, whose target is the source-minimal
`OffdiagEnergy ≤ T_off`. The desired natural-scale statement
`A_off(k) ≪_A U² H² (log X)^{-A}` is recorded here in prose only; it is **not**
a Lean theorem, because the project's asymptotic framework does not safely
support that logarithmic asymptotic.

```
RANKONE-ENDPOINT-U-OFFDIAG45 : ANALYTIC_OPEN     ← first analytic priority
```

---

## E. BETA SOURCE DICTIONARY

Searched first, per the instruction. **No physical `β = μ_D * Λ_P` definition
exists in this repository.** It was therefore *not* invented from prose.

Banked instead: `AnalyticInterfaces.EndpointBetaSourceDictionary`, a
SOURCE-OPEN uninhabited interface whose fields state exactly what a literal
transcription would have to provide (the factorisation `z = d·p`, the dyadic
support restrictions, and the induced rewriting of the off-diagonal difference
as `d₂p₂ − d₁p₁ = u(t₂−t₁) + j v_{t₂}`).

```
FIRST SOURCE BLOCK: physical beta = mu_D * Lambda_P dictionary.
```

Per the prompt, the off-diagonal theorem is **not** marked false on account of
the missing transcription. Nothing was estimated.

### E1. What *was* bankable without the source — `SourceStrata.lean`

The partition machinery the dictionary will plug into is source-neutral, so it
is proved now rather than deferred:

* `sum_stratified` — exhaustive partition of a finite sum into the fibres of an
  arbitrary label map, with `strata_disjoint` and `strata_cover` proving the
  strata are pairwise disjoint and exhaust the index set. This is the shape
  every gcd / repeated-prime / prime-power stratum decomposition must take.
* `offdiagEnergy_stratified` — the same, instantiated at the endpoint
  off-diagonal index set `offdiagIndex`.
* **`offdiagEnergy_prime_split`** — for *any* prime label `plab : ℤ → ℕ`, the
  exact `p₁ = p₂` versus `p₁ ≠ p₂` split of `offdiagEnergy`, with
  `prime_split_disjoint` proving nothing is double counted or dropped.

When the literal `β = μ_D * Λ_P` dictionary arrives, only the label map
`plab z = p` (from `z = d·p`) has to be supplied; the partition identity is
already kernel-checked. No arithmetic content is claimed in the meantime.

---

## F. COMPARISON LOCAL-DENSITY PIN

### F1. Zero principal mode NOT banked

The unit-restricted defect mean is generally **not** zero. The approximate
analytic formula
`Σ_{(n,ℓ)=1} δ_i(n) ~ (1 − φ(ℓ)/ℓ)(Y/log Y)∫W`
is **not** Lean-proved (its analytic input is not formalised). What *is* banked
is the logical firewall:

> residue discrepancy ≠ physical source after main-term subtraction, unless the
> comparison main term is identified.

### F2. Physical comparison source

Searched. **Absent.** No retrospective main term was selected to match
Motohashi, and no equality was fabricated.

```
PURE5-COMPARISON-MAINTERM-PIN : SOURCE_OPEN
SOURCE BLOCKED: exact physical comparison definition / source decomposition missing.
```

`Pure5ComparisonMainTermPin` exists as an uninhabited interface only.

---

## G. HIGH-k

`FiniteLineFourier.lean` banks the exact finite Parseval identities
(`parseval_lineZ`, `parseval_lineB`). No false pointwise `L^{-5}` estimate for
`b5` appears.

The current source-minimal residual `R_hi` (the `|k| > log^C` tail of the mixed
moment) is isolated behind the uninhabited
`RankOneHighKJointPhaseInput`.

Banked firewall: `separate_energy_gives_no_cancellation` — a finite countermodel
showing that separate energy control over the β-source sign, the five-defect
signs, and the shared `k`-phase need **not** produce signed cancellation.
Separate Parseval/Cauchy is therefore explicitly *not* a closure mechanism. No
analytic high-`k` cancellation was invented.

```
RANKONE-HIGHK45 : ANALYTIC_OPEN
```

---

## H. PURE5 / LOWER DEFECT / NEARPRIM

The actual source decomposition for the defect orders was searched for and is
absent. **No blanket monotonicity assumption was made**: closing `|J| = 5` is
not assumed to close `|J| = 4,3,2,1`.

| order | status | note |
|---|---|---|
| `|J| = 5` | SOURCE_OPEN | `PURE5-DP-SIGNED45`; compiler shape only |
| `|J| = 4` | SOURCE_OPEN | separate provider pin; no literal source map |
| `|J| = 3` | SOURCE_OPEN | separate provider pin |
| `|J| = 2` | SOURCE_OPEN | separate provider pin |
| `|J| = 1` | SOURCE_OPEN | separate provider pin |

For each order the implication from the `|J| = 5` provider was **not** proved,
because the source map is not literal. `NEARPRIM-DP-SIGNED45` is likewise
`SOURCE_OPEN`; it was *not* inferred from naming.

Banked in `SourceStrata.lean` (`LOWER-DEFECT-ORDER-CENSUS`, PROVED_ALGEBRAIC):
the five-row census type `DefectOrder` with `allDefectOrders_complete`, plus two
counterguards — **`no_blanket_monotonicity`**, exhibiting an assignment that
holds at `|J| = 5` and fails at every lower order, and
`specialisation_not_automatic`, showing no specialisation map between distinct
orders is derivable without a literal source map.

---

## I. r>1 / TRANSITION / RECURSION

Handled as three separate items, all `SOURCE_OPEN`:

1. `R>1-SQUARE-CHARACTER-FAMILY` — existing finite conductor/CRT/Gauss banks are
   reused by reference; the literal source packet is absent.
2. `CSTAR-CNW-TRANSITION-STRIP` — source packet absent.
3. proper-divisor recursion — the **termination measure is now banked**
   (`SourceStrata.lean`, `PROPER-DIVISOR-RECURSION-MEASURE`, PROVED_ALGEBRAIC):
   `ProperDvd`, `properDvd_lt`, **`properDvd_wf`** (well-foundedness, via
   `Subrelation.wf` over `Nat.lt_wfRel`), `properDvd_irrefl`, `one_properDvd`.
   Per the prompt, having the measure is a *precondition* for formalising the
   recursion, not a closure: **no recursive closure is stated**, because the
   recursion's content still needs the missing source packets.

No analytic estimate was inhabited in this phase.

---

## J. QK56 / SHIFTED TT\* / GATE1B COMPILER

### J1–J2. QK56

The v13 machinery (same-`q` Gram split, product-residue kernel, cross-`q` theta
spread criterion, qk56 conditional compiler, v10 leaf bridge, SHAPE
counterguards, weight-dependence compiler, FM→Gate census type) is **reused by
reference and not duplicated**. The ledger repoints the QK56 parent's leaves at
the current source providers rather than the old v13 placeholder priorities.

```
QK56-FULL-PARENT   : CONDITIONAL_COMPILER   (leaves not supplied)
QK56-EXHAUSTIVENESS: SOURCE_OPEN            (no literal source enumeration in repo)
```

### J3. Shifted TT\*

`ShiftTTStarLiteralSourceCertificate` **remains uninhabited**. The physical
cycle source is not present, so no dictionary inhabitant was constructed, and no
injectivity or source equality was inferred from prose.
`SHIFTED-TTSTAR : SOURCE_OPEN`.

### J4. Gate1B current endpoint compiler — `Gate1BEndpointCompiler.lean`

`EndpointInputs` bundles exactly the real antecedents:

* localized fivefold discrepancy bound (`LocalizedFivefoldDiscrepancyInput`),
* endpoint diagonal bound (`RankOneEndpointUDiagonalInput`),
* endpoint off-diagonal bound (`RankOneEndpointUOffdiagInput`),
* literal β/source dictionary (`EndpointBetaSourceDictionary`),
* physical comparison / local-density match (`Pure5ComparisonMainTermPin`).

Proved: `endpointEstimate_of_inputs` — the deterministic compiler. Also proved:

* **non-circularity** — the input structure does not contain the target
  proposition as a field;
* **non-automaticity** — a toy model in which the target fails, so the
  conclusion is not vacuous;
* `endpointEstimate_does_not_give_gate1BClosed` — the endpoint estimate alone
  does **not** yield the existing project target `Gate1BClosed`.

Since none of the five inputs has a proof inhabitant:

```
GATE1B-REASSEMBLY : CONDITIONAL_COMPILER
GATE1B            : OPEN
```

---

## K. FORD-GENERATED PACKET CENSUS

`FordGeneratedCensus.lean` defines the provider enum
(`Gate0Provider`, `Gate1AProvider`, `Gate1BProvider`, `Gate2Direct`,
`SourceOpen`, `AnalyticOpen`, `NoProviderYet`), the `Packet` and `PacketCensus`
types, and `CensusExhaustive`.

Ford's literal objects — `Proposition 7.22`, equation `(7.23)`, `C(R)`, `R(P)`,
`G(d;n)`, the fixed certificate — are **absent from the repository** and were
**not reconstructed from memory**. Consequently `repositoryCensus` is the
**empty** census: it contains no fabricated packet.

```
FORD-GENERATED-PACKET-CENSUS : SOURCE_BLOCKED
RealFordGrammarCertificate   : SOURCE_BLOCKED   (v11 type, kept uninhabited)
```

`GATE1A_REQUIRED` is defined as a **derived predicate of the actual census**
(`Gate1ARequired census ↔ ∃ p ∈ census, p.provider = Gate1AProvider`), not
assumed globally. On the empty census it is not derivable, so the row is
`SOURCE_OPEN` — *not* "false" and *not* "required". Nothing was forced through
Gate1A.

Cheap finite repairs (G5) are banked with their exact domains and no analytic
interpretation: `q ≥ 5`; the sign-sensitive minus endpoint `q ≤ ⌊M/2⌋`; the
`M ∈ {q, 2q}` divisor blocker.

---

## L. R9 / G(d;n) / PROP 7.22–7.23

### L1. R9 direction — CORRECTED, not resurrected

The false R9 death certificate is **not** resurrected.
`R9LeakageArithmetic.r9_death_certificate_refuted` records the correction, and
`balancedR9_is_leakage` states the corrected direction through the
`R9LeakageDirection` dictionary:

* `R(P)` consists of vectors with **no** proper subsum in the Type-II window;
* the balanced R9 coordinate `1/9` **lies** in that window;
* hence the balanced R9 vector is **not** in `R(P)`, hence outside `C(R(P))`;
* that is precisely **leakage**, not disqualification from leakage;
* R9 is therefore a Ford-generated leakage packet entering the
  Prop 7.22 / (7.23) route.

Because `R(P)`, `C(R(P))` and the leakage set are not literally present, this is
banked as a **source-pending dictionary** recording the corrected direction, not
as a proved membership. No unbalanced-1/5 redesign was attempted.

```
R9-LEAKAGE-MEMBERSHIP : SOURCE_OPEN  (direction corrected)
```

### L2. P_ε / R9 finite arithmetic — PROVED_FINITE

With `Params` carrying `ν = 1/6`, `ε ≤ 1/600`, `η < 1/90`, kernel-proved exact
rational facts:

* `r9_coordinate_not_tiny` — `1/9 ± η` is not small enough to be assembled from
  the total tiny mass;
* `r9_coordinate_not_large` — nor large enough to contain a large component;
* `r9_four_below_cut` : `4(1/9 + η) < 1/2 − ε`;
* `r9_five_above_cut` : `5(1/9 − η) > 1/2 − ε`;
* `r9_H_value_seventy` : `Σ_{j=0}^{4} (−1)^j C(9,j) = 70`, discharged by reusing
  the existing bank `k0EqualFactorR9Value70`;
* `seventy_depends_on_cutoff` — the value `70` is a function of the cutoff and
  is **not** identified with any physical Ford coefficient.

### L3. G(d;n) specialization

`G(d;n)` is **absent**. The `GdnSpecialization` structure states what a literal
transcription must check (divisor cutoff, Möbius sign, support, local weights,
normalisation, ordered/distinct conventions), and
`gdn_balancedValue_determined` proves only that *given* such a specialization the
balanced value is determined. No connection of `H(n) = 70` to a physical packet
was made.

```
R9-GDN-SPECIALIZATION : SOURCE_OPEN   (source promotion stopped)
```

---

## M. GATE1A PROVIDER STATUS

The existing Gate1A safe bank is preserved untouched. The historical facts
(authoritative direct source pinned; physical `W_D` common for the canonical
direct source; all-`m` row family/energy constructed; BPP finite compiler
proved; external BPP analytic input unformalised; edge-dependent-D2 a
Gate0/source-adapter obligation; rootdefect secondary open; Gate0→Gate1A
compiler open) all remain as recorded.

**Gate1A is not declared closed.**

* H1 — `TWO_OUTER_VARIABLE_F3_KERNEL` was **not** automatically reopened. Since
  the Phase-G census is empty, nothing shows it is required for the current
  Ford/#287 route. Recorded `NOT_CURRENTLY_REQUIRED`, explicitly as a genuine
  open research object rather than a dead one. `F3_SINGLE_OUTER_UNROUTABLE_CORE`,
  `FULL_F1_MIGRATION_OPEN`, `HYBRID_MQ_KLOOSTERMAN_LARGE_SIEVE`,
  `BALANCED_TII_CORE`, `PARITY_OPEN` are likewise untouched and still open.
* H2 — the theorem-strength firewall is preserved: high-conductor power saving
  `X^{1−η}` is **never** promoted to whole-piece power saving (which is only
  `X log^{-B}`). `FULL_ROUTED_PIECE_POWER_SAVING_REFUTED_AS_STATED` is retained
  as `FALSE_ROUTE`.
* H3 — no packet was routed into edge-dependent D2, so no common-weight theorem
  was applied there and no functional-analytic commonisation was attempted.
* H4 — no provider theorem was built, because the census does not require one.

```
GATE1A : OPEN     GATE1A_REQUIRED : SOURCE_OPEN
```

---

## N. GATE0 / GATE2

### N1. Gate 0

Gate01 finite banks are reused by reference. The literal exhaustive source
coverage across the direct / switched / prime-power / repeated-prime / generic /
zero- and nonzero-frequency strata was audited; **no missing face was invented**.
The exhaustive source-partition identity is not proved.

```
GATE0 : OPEN  (exhaustive coverage open)
```

In the DAG, `gate0_is_a_source` is proved: no edge points into Gate 0.

### N2. Gate 2

The actual project target was searched for. `FullFMTypeII_OneSixth` does **not**
exist and was **not** invented; the strongest existing target
(`FullTypeIIBound` / `Gate1BClosed` in `Gate1BInterfaces.lean`) is used instead.
The reassembly compiler is conditional on Gate-0 exact coverage, the generated
packet census, provider outputs, comparison/source matches, and finite
nuclear/template costs — **all exposed as explicit antecedents**, with no
analytic input hidden inside.

```
GATE2 : CONDITIONAL_COMPILER      FULL_FM_TYPEII : OPEN
```

---

## O. ERDŐS 287 FACTORIAL EULER BANK

`RequestProject/Erdos287/` does **not exist** in this repository, and neither
does `WindowPairSupply`. The prompt's instruction to preserve the finite theorem
(no exact counterexample for `3 ≤ M ≤ 4·10⁹`) and the exact conditional
(`WindowPairSupply ⇒ final theorem`) was honoured vacuously: there was nothing
to alter, and nothing was fabricated in their place.

```
WINDOWPAIRSUPPLY : SOURCE_BLOCKED
  — no WindowPairSupply object exists here; the #287 finite compiler is absent.
ERDOS287 : OPEN
```

### O1. Factorial-Euler polarization — PROVED_ALGEBRAIC

`FactorialEulerPolarization.lean`, over `Fin 7` labels with
`a_z(p) = (1/7) Σ_{i=1}^{7} z_i ω_i(p)` and `F_z(p^e) = a_z(p)^e / e!`:

* `alternating_polarization` — the full inclusion–exclusion identity, proved
  from `Finset.sum_powerset_neg_one_pow_card` with an explicit `ℂ` cast wrapper.
* `factorialEulerPolarization_general` and
  **`factorialEulerPolarization_seven`** :

  ```
  7^7 [z1…z7] F_z(n) = Σ_{p1…p7 = n, ordered} Π_i ω_i(p_i)     for Ω(n)=7
  ```

  valid **including repeated primes**.
* `no_extra_inverse_factorial_correction` — the false extra `Π_p 1/e_p!` is
  explicitly refuted. The factorial cancellation is proved in the exact form
  `[Π_{i∈S} z_i](Σ_i z_i ω_i(p))^e = e! Π_{i∈S} ω_i(p)`, which cancels the
  `1/e!` in `F_z(p^e)`.

### O2. Local Euler algebra — PROVED_ALGEBRAIC (`LocalEulerAlgebra.lean`)

With `localF a e = a^e / e!` the single-prime local factor:

* `succ_mul_localF` : `(e+1)·F(e+1) = a·F(e)` — the factorial cancellation
  isolated at one prime.
* `localEuler_tsum` : `∑'_e F(e)·T^e = exp(a·T)`, stated with Mathlib's `tsum`
  so **no extra analytic convergence obligation is manufactured**.
* `lambdaLocal a e = if e = 1 then a else 0`, with
  `lambdaLocal_recursion` proving it satisfies the logarithmic-derivative
  recursion `e·F(e) = Σ_{j=1}^{e} Λ(j)·F(e−j)`, `F(0) = 1`, and
  **`lambdaLocal_unique`** proving the recursion determines `Λ` uniquely (strong
  induction). This is what makes the pattern a *derived* fact rather than a
  definitional stipulation.
* Hence, in `log p`-carrying form: `LambdaF_prime` : `Λ_F(p) = a_z(p)·log p`,
  and `LambdaF_prime_power` : `Λ_F(p^e) = 0` for `e ≥ 2`.
* `lambdaLocal_injective_in_a` — counterguard: nothing here supplies arithmetic
  information about `a_z(p)`.

The project has no "class C" definition, so class-C nomenclature is labelled a
**DEFINITION PIN** and no membership was claimed. No analytic property of `Λ_F`
(mean value, Siegel–Walfisz, BV) follows from this module.

### O3. Expected-term linearity — PROVED_ALGEBRAIC

`coeffExtract_linear` : coefficient extraction commutes with a linear map,
`[z1…z7] E(F_z) = E([z1…z7] F_z)`. **`M_fac = M_phys` is NOT concluded** — it
remains a source identity.

### O4. Pascadi parameter ledger — PROVED_FINITE

Exact rational arithmetic in `PascadiParameterLedger.lean`:

* `3/5 ≤ 5/8 − 100η ⇒ η ≤ 1/4000`;
* `1/7 > 1/4000`;
* hence **no** `η` satisfies `η ≥ 1/7` and `3/5 ≤ 5/8 − 100η` simultaneously.

Labelled `PASCADI-PROOF-PARAMETER-NOGO`. `nogo_is_parameter_specific` is proved
alongside it, recording that this audits the *supplied proof parameters* and is
**not** a claim that the Pascadi theorem is impossible.

---

## P. BALANCED7 / FIXED-DEGREE STATUS

Uninhabited: `FactorialOmega7SignedEndpointInput`
(= `AFFINE287-FACTORIAL-OMEGA7-SIGNED-ENDPOINT45`) and
`MuLogComparisonLowCondMatch`
(= `AFFINE287-MULOG-COMPARISON-LOWCOND-MATCH45`), kept separate.

Proved: the deterministic compiler
`balanced7_modulusAverage_of_inputs` — factorial endpoint input **+** comparison
input ⇒ balanced-seven modulus-average target. No analytic inhabitant.

Source-neutral finite structures for the `2+2+2+1` and `3+2+1+1` block
partitions are banked (exponent arithmetic and exact finite regrouping only). No
Pascadi/Kuznetsov analytic theorem was formalised, and no fixed-degree-seven
post-dispersion geometry was asserted.

### K1 (generated V-cell census)

Not performable: the actual V-branch generated cells are absent from the
repository. **No claim that Balanced7 closes the V branch** was made. The census
slot exists and is empty.

---

## Q. K0 / FCL / POSITIVE MASS / WINDOWPAIR

* **K2, M/singleton branch** — the exact `Λ = μ * log` bank and the
  singleton/Ford fragmentation compilers are preserved. The V14 Vaughan source is
  recorded as a valid but nonminimal alternative; it is **not** marked false.
  Whether the source-minimal route still needs an M/singleton analytic theorem
  cannot be determined while the census is empty.
* **K3, K0 smooth parity** — fixed-certificate finite algebra, canonical
  singleton structural routing, the R9 leakage correction and source-pin status
  are all preserved. Banked firewall: **structural fragmentation does not supply
  analytic parity cancellation.** `K0-SMOOTH-PARITY : SOURCE_OPEN`.
* **K4, FCL** — the precise fixed-certificate leakage target requires the actual
  source, which is absent. Ford-generated leakage is **not** treated as universal
  Type II; provider assignment stays proof-specific. `FCL : SOURCE_OPEN`.
* **K5, positive affine mass** — not constructed. No positivity conclusion is
  drawn from isolated packet estimates. `POSITIVE-AFFINE-MASS : OPEN`.
* **K6, WindowPair** — the final compiler does not exist here (see Section O);
  nothing was reproved and nothing was invented.

---

## R. MASTER DAG

`DependencyGraph.lean` defines `Node`, `edge`, `reachIn`/`reach`, and proves:

* `spine_present` — the canonical architecture is present as a reachability
  chain:

```
finite source / Gate0
      → generated packet census
           ↙            ↘
      Gate1A          Gate1B          (proved parallel, not sequential)
           ↘            ↙
              Gate2
                → Ford-generated packet / leakage reassembly
                → fixed-certificate leakage + comparison + effectivity
                → positive affine mass
                → WindowPairSupply
                → existing finite Lean compiler
                → Erdős #287
```

* `providers_are_parallel` — Gate1A and Gate1B are siblings.
* `providerArrowIsConditional` — provider arrows are census-determined; **not**
  every packet is forced through every Gate.
* `gate0_is_a_source` — no edge enters Gate 0.
* **`no_cross_implication`** — there is no path `Erdős #287 → Twin Primes` and no
  path in the reverse direction. The twin-prime programme's downstream graph is
  preserved as a separate component.

---

## S. RETRACTIONS / SUPERSEDED ROUTES

| item | disposition |
|---|---|
| `SHIFT-SOURCE-LINKED-CHAR45` as first Gate1B analytic open | `SUPERSEDED_AS_CONTROLLING_FRONTIER` — historical text untouched |
| `‖δ_i‖_∞ ≪ (log X)^{-1}` | **REFUTED** by `prime_defect_refutes_pointwise_log_bound`; retained as a counterguard, original statement not silently edited |
| R9 "death certificate" | **CORRECTED** direction (outside `C(R(P))` = leakage), banked as `r9_death_certificate_refuted`; not resurrected |
| extra `Π_p 1/e_p!` in the factorial Euler identity | **REFUTED** by `no_extra_inverse_factorial_correction` |
| whole-piece power saving for the full routed piece | `FALSE_ROUTE` preserved as `FULL_ROUTED_PIECE_POWER_SAVING_REFUTED_AS_STATED` |
| separate Parseval/Cauchy as a high-`k` closure mechanism | rejected; finite countermodel banked |
| zero principal mode for the unit-restricted defect mean | **not banked**; explicitly recorded as generally nonzero |
| `TWO_OUTER_VARIABLE_F3_KERNEL` | `NOT_CURRENTLY_REQUIRED`, still a genuine open object |

No historical bank was deleted or weakened. Every correction is an added
regression theorem plus a status row, with provenance preserved.

---

## T. TRUST AUDIT

| check | result |
|---|---|
| focused build, `CurrentProgramme` modules | PASSED |
| full `lake build` | PASSED, 8610 jobs |
| `grep -cE '^error'` on the full build log | 0 |
| `sorry` / `admit` in new Lean code | **none** (only the two documentation lines in `AxiomAudit.lean` describing the scan) |
| user `axiom` | **none** |
| `opaque`, `unsafe`, `native_decide`, `@[implemented_by]` | **none** |
| `#print axioms` on principal new theorems | 122 declarations audited |
| axioms observed | only `propext`, `Classical.choice`, `Quot.sound`, or none |
| `sorryAx` / `Lean.ofReduceBool` anywhere in the build log | **none** |

No analytic source interface has a `Classical.choice`-based inhabitant: every
interface in `AnalyticInterfaces.lean` is a bare structure with no constructor
application anywhere in the project.

---

## U. FIRST FORMAL BLOCKER

**None in the new layer.** Every retained module elaborates and the full project
builds. There is no `sorry`, no failed elaboration, and no pending obligation of
a purely Lean-technical nature.

---

## V. FIRST SOURCE BLOCKER

```
SOURCE BLOCKED: physical endpoint beta source dictionary,  beta = mu_D * Lambda_P.
```

Location of the empty slot:
`RequestProject/CurrentProgramme/AnalyticInterfaces.lean`,
`EndpointBetaSourceDictionary`.

Immediately behind it, in order: the physical comparison source
(`PURE5-COMPARISON-MAINTERM-PIN`), then the Ford literal grammar
(`Prop 7.22`, `(7.23)`, `C(R)`, `R(P)`, `G(d;n)`), then the missing
`Erdos287` / `WindowPairSupply` modules.

---

## W. FIRST ANALYTIC BLOCKER

```
OPEN_ANALYTIC: RANKONE-ENDPOINT-U-OFFDIAG45
```

Minimal statement: a bound `OffdiagEnergy ≤ T_off` for the exact finite object
`EndpointBilinear.offdiagEnergy`, i.e. for

```
Σ_ℓ Σ_{j ≠ 0} Σ_u  a4(u) conj(a4(u+jℓ)) Z_{u,ℓ}(k) conj(Z_{u+jℓ,ℓ}(k)),
```

with the desired natural scale `A_off(k) ≪_A U² H² (log X)^{-A}` (or an
averaged-`k` equivalent). Everything deterministic around it is already proved:
the exact split `residueEnergy_split`, the parametrisation
`congruentPair_param`, and the load-bearing identity `offdiag_line_difference`.

Second analytic blocker: `RANKONE-HIGHK45`.

---

## X. NEXT EXACT ACTION

1. Supply the literal `β = μ_D * Λ_P` endpoint source definition into
   `EndpointBetaSourceDictionary` (`AnalyticInterfaces.lean`) — from actual
   source text, not from prose.
2. Instantiate the already-proved `Strata.offdiagEnergy_prime_split` with the
   label `plab z = p` coming from `z = d·p`, and combine with
   `offdiag_line_difference : z₂ − z₁ = u·Δt + j·v_{t₂}` to obtain the literal
   source relation `d₂p₂ − d₁p₁ = u(t₂−t₁) + j v_{t₂}`. Any further gcd /
   repeated-prime / prime-power strata go through `Strata.sum_stratified` —
   **partition identities only**, no estimate.
3. Only then attack `RankOneEndpointUOffdiagInput`.

Do **not** advance to Gate1A/F3 objects: the packet census is empty and does not
require them.

---

## Y. FINAL STATUS

Verdict for the run: **BANKED_LEDGER_CREATED.**

### Literal status table

| label | status |
|---|---|
| GATE0 | OPEN |
| GATE1A | OPEN |
| GATE1B | **OPEN** |
| GATE2 | CONDITIONAL_COMPILER |
| FULL_FM_TYPEII | **OPEN** |
| | |
| MOTOHASHI-FAMILY-UNIFORMITY45 | EXTERNALLY_AUDITED |
| RANKONE-POLYLOGK-INTERIOR45 | EXTERNALLY_AUDITED |
| RANKONE-ENDPOINT-U-DIAGONAL45 | CAPACITY_ONLY |
| RANKONE-ENDPOINT-U-OFFDIAG45 | ANALYTIC_OPEN |
| PURE5-COMPARISON-MAINTERM-PIN | SOURCE_OPEN |
| RANKONE-HIGHK45 | ANALYTIC_OPEN |
| ENDPOINT-OFFDIAG-STRATIFICATION-SHAPE | PROVED_ALGEBRAIC |
| PURE5-DP-SIGNED45 | SOURCE_OPEN |
| LOWER-DEFECT-ORDER-CENSUS | PROVED_ALGEBRAIC |
| PROPER-DIVISOR-RECURSION-MEASURE | PROVED_ALGEBRAIC |
| NEARPRIM-DP-SIGNED45 | SOURCE_OPEN |
| R>1-SQUARE-CHARACTER-FAMILY | SOURCE_OPEN |
| CSTAR-CNW-TRANSITION-STRIP | SOURCE_OPEN |
| QK56-FULL-PARENT | CONDITIONAL_COMPILER |
| QK56-EXHAUSTIVENESS | SOURCE_OPEN |
| SHIFTED-TTSTAR | SOURCE_OPEN |
| GATE1B-REASSEMBLY | CONDITIONAL_COMPILER |
| | |
| FORD-GENERATED-PACKET-CENSUS | SOURCE_BLOCKED |
| GATE1A_REQUIRED | SOURCE_OPEN |
| R9-LEAKAGE-MEMBERSHIP | SOURCE_OPEN |
| R9-GDN-SPECIALIZATION | SOURCE_OPEN |
| FCL | SOURCE_OPEN |
| | |
| OMEGA7-FACTORIAL-EULER-POLARIZATION45 | PROVED_ALGEBRAIC |
| OMEGA7-LOCAL-EULER-VONMANGOLDT-PATTERN | PROVED_ALGEBRAIC |
| POLARIZED-EXPECTED-TERM-LINEARITY45 | PROVED_ALGEBRAIC |
| PASCADI-PROOF-PARAMETER-NOGO | PROVED_FINITE |
| AFFINE287-FACTORIAL-OMEGA7-SIGNED-ENDPOINT45 | ANALYTIC_OPEN |
| AFFINE287-MULOG-COMPARISON-LOWCOND-MATCH45 | SOURCE_OPEN |
| AFFINE287-BALANCED7-MODULUS-AVERAGE45 | CONDITIONAL_COMPILER |
| | |
| K0-SMOOTH-PARITY | SOURCE_OPEN |
| POSITIVE-AFFINE-MASS | OPEN |
| WINDOWPAIRSUPPLY | SOURCE_BLOCKED |
| ERDOS287 | **OPEN** |
| | |
| TWIN_PRIME_CONJECTURE | **OPEN** |

Additional current rows (also in `Ledger.full`):

| label | status |
|---|---|
| MOTOHASHI-ABC-EXACT-PIN45 | EXTERNALLY_AUDITED |
| TWISTED-DEFECT-ABC45 | EXTERNALLY_AUDITED |
| FIVEFOLD-MOTOHASHI-ITERATION45 | EXTERNALLY_AUDITED |
| LOCALIZED-FIVEFOLD-MOTOHASHI45 | CONDITIONAL_COMPILER |
| NORMALISATION-FIREWALL-DELTA-I | LEAN_PROVED |
| RANKONE-LINE-SOURCE-ALGEBRA | PROVED_ALGEBRAIC |
| R9-PEPSILON-FINITE-ARITHMETIC | PROVED_FINITE |
| SHIFT-SOURCE-LINKED-CHAR45 | SUPERSEDED_AS_CONTROLLING_FRONTIER |
| FULL_ROUTED_PIECE_POWER_SAVING_REFUTED_AS_STATED | FALSE_ROUTE |
| TWO_OUTER_VARIABLE_F3_KERNEL | NOT_CURRENTLY_REQUIRED |
| RealFordGrammarCertificate | SOURCE_BLOCKED |

No row is `CLOSED`; this is not merely an editorial convention but is
kernel-proved by `Ledger.no_closed_rows`.

### End-of-run non-claim

```
GATE1B:                  OPEN
FULL FM TYPE II:         OPEN
ERDOS287:                OPEN
TWIN PRIME CONJECTURE:   OPEN
```

Also proved in Lean as `Ledger.end_of_run_nonclaims`.

---

## CHECKPOINT

* **Last completed phase:** P (all of A–P attempted; A, C–G, J–P completed to
  the extent the literal sources in this repository allow).
* **First unfinished theorem / source field:**
  `AnalyticInterfaces.EndpointBetaSourceDictionary` — the physical
  `β = μ_D * Λ_P` transcription.
* **Exact next file / theorem:**
  `RequestProject/CurrentProgramme/SourceStrata.lean`, instantiating
  `offdiagEnergy_prime_split` with the physical label map, then the literal
  source relation `d₂p₂ − d₁p₁ = u(t₂−t₁) + j v_{t₂}` built on the
  already-proved `RankOneLineAlgebra.offdiag_line_difference`.
* No drift to another old programme branch occurred.
