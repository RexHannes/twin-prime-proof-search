# CURRENT GATE ARCHITECTURE AND STATUS

*Source of truth for the V16.1 / V17 drafter.  Append-only: nothing in this file
supersedes or deletes an existing report; older reports remain valid records of
their own runs.  The public PDF was not touched.*

**Nothing in this document authorises a claim of Gate 0, Gate 1A, Gate 1B or
Gate 2 closure, of Full Ford–Maynard Type II, of fixed-certificate leakage
closure, of `WindowPairSupply` for all large `M`, of Erdős Problem #287, of the
Twin Prime Conjecture, or of Hardy–Littlewood.**

---

## 1. Gate 0 — exact role and status

**Role.** The finite source layer.  It must produce an *exhaustive disjoint
partition* of the physical source into the direct / switched / prime-power /
repeated-prime / generic / zero-frequency / nonzero-frequency strata, so that
the generated packet census downstream is provably complete.

**Status: OPEN.**

* The existing finite banks (`RequestProject/NANC/Gate01`,
  `Gate01Consolidation`, `Gate01Switch`, `Gate01Root`, `Gate04Root`) are reused,
  not duplicated.
* `GATE0 EXHAUSTIVE COVERAGE` remains open: the repository does not contain a
  proved source-partition identity.  No missing face was invented.

## 2. Gate 1A — exact role and status

**Role.** Provider layer for the packets whose literal source structure is the
Gate-1A direct / all-`m` row family.

**Status: OPEN.**  Preserved and unchanged:

* authoritative direct source pinned;
* physical `W_D` common for the canonical direct source;
* all-`m` row family / energy constructed;
* BPP finite compiler proved; the external BPP analytic input is unformalised;
* `edgeDependent-D2` is a Gate-0 / source-adapter obligation;
* rootdefect secondary open; Gate 0 → Gate 1A compiler open.

**`GATE1A_REQUIRED` is not assumed.**  It is a *derived* predicate of the
literal packet census
(`TwinPrimeProject.CurrentProgramme.Ford.Gate1ARequired`).  The census present
in the repository is empty, so the requirement is neither derived nor denied;
its status is `SOURCE_OPEN`.

**Theorem-strength firewall preserved.**  High-conductor component: power
saving `X^(1-η)`.  Full routed piece: only `X log^{-B}`.  The former is never
promoted to the latter; `FULL_ROUTED_PIECE_POWER_SAVING_REFUTED_AS_STATED`
stands.

## 3. Gate 1B — exact role and status

**Role.** Provider layer for the rank-one / determinant-2 endpoint family.

**Status: OPEN.**

### 3.1 Frontier reset

The old v13 human ledger entry

    FIRST GATE1B ANALYTIC OPEN: SHIFT-SOURCE-LINKED-CHAR45

is `SUPERSEDED_AS_CONTROLLING_FRONTIER` — **not** false.  Its bank is intact.

The current first analytic open is

    RANKONE-ENDPOINT-U-OFFDIAG45.

### 3.2 What is now kernel-proved (new this run)

| item | file | content |
| --- | --- | --- |
| normalisation firewall | `NormalisationFirewall.lean` | exact prime specialisation `δ(p) = (1 − 1/log p)·W(p/Y)`; the pointwise `(log X)^{-1}` claim is **refuted** |
| smooth-localisation compiler | `SmoothLocalisation.lean` | finite Abel/BV transfer `\|weighted\| ≤ (‖F‖∞ + Var F)·T`, uniform in a residue parameter |
| rank-one line algebra | `RankOneLineAlgebra.lean` | `u·v_t + 2 = ℓ·z_t`; endpoint residue map is an involution on units; **`z₂(t₂) − z₁(t₁) = u(t₂−t₁) + j·v_{t₂}`** |
| finite line Fourier | `FiniteLineFourier.lean` | exact `ZMod H` orthogonality, mixed moment, Parseval, with the `1/H` normalisation explicit |
| endpoint bilinear split | `EndpointBilinear.lean` | `∑_a \|A_{ℓ,a,k}\|²` expands to the congruent-pair condition and splits **exactly** into the two energy children |
| endpoint exponent bank | `EndpointExponentBank.lean` | `33/4` in `Y`, margin `3/4` in `Y`, i.e. `X^{-1/12}` — `CAPACITY_ONLY` |
| endpoint compiler | `Gate1BEndpointCompiler.lean` | non-circular conditional compiler; all five inputs open |

### 3.3 Open Gate-1B leaves

`PURE5-COMPARISON-MAINTERM-PIN` (source open), `PURE5-DP-SIGNED45`,
`NEARPRIM-DP-SIGNED45`, lower defect orders `|J| = 4,3,2,1`,
`R>1-SQUARE-CHARACTER-FAMILY`, `CSTAR-CNW-TRANSITION-STRIP`, proper-divisor
recursion, `QK56-EXHAUSTIVENESS`, `SHIFTED-TTSTAR`, and the two analytic opens
`RANKONE-ENDPOINT-U-OFFDIAG45`, `RANKONE-HIGHK45`.

## 4. Gate 2 — exact role and status

**Role.** Reassembly of the provider outputs into the routed Type-II statement.

**Status: CONDITIONAL_COMPILER.**  The strongest *existing* project targets are
used (`TwinPrimeProject.Gate1BDet2.Gate1BClosed`, `FullTypeIIBound`, and the v10
`gate1B_closed_of_exact_inputs`).  `FullFMTypeII_OneSixth` was **not** invented;
it is absent from the repository.

## 5. Ford-generated packet / provider census

**Status: SOURCE_BLOCKED.**

Literal search result over all `.lean` sources:

| object | present? |
| --- | --- |
| `RealFordGrammarCertificate` | present as a v11 type, recorded there as uninhabited / repo data absent |
| FMPerron grammar | present (`V11FMPerronGrammar.lean`) |
| Proposition 7.22 | **absent** |
| equation (7.23) | **absent** |
| `C(R)`, `R(P)`, leakage set | **absent** |
| `G(d;n)` | **absent** |

No Ford definition was reconstructed from memory.  The provider enum and census
type exist (`FordGeneratedCensus.lean`); the census itself is empty and does
**not** claim exhaustiveness.

Cheap finite repairs banked with exact domains: `q ≥ 5`; the sign-sensitive
minus endpoint `q ≤ ⌊M/2⌋`; the `M ∈ {q, 2q}` divisor blocker (with a proof that
the blocker is a genuine restriction).

## 6. Current #287 factorial endpoint

**Kernel-proved (new this run):**

* `alternating_polarization` — `∑_{A ⊆ [n]} (−1)^{n−|A|}(∑_{i∈A} wᵢ)^n = n!·∏ wᵢ`;
* `factorialEulerPolarization_general` — `n^n · [z₁⋯z_n](a_z^n/n!) = ∏ ωᵢ`;
* `factorialEulerPolarization_seven` — the balanced-seven case, **including the
  fully repeated prime cell `n = p^7`**;
* `no_extra_inverse_factorial_correction` — the false extra `∏_p 1/e_p!` is
  refuted;
* `coeffExtract_linear` — expected-term linearity (Phase J3).  **`M_fac = M_phys`
  is NOT concluded**; it remains a source identity.
* `pascadi_parameter_nogo` — audit of the *supplied* parameters only.

**Open:** `AFFINE287-FACTORIAL-OMEGA7-SIGNED-ENDPOINT45` (analytic),
`AFFINE287-MULOG-COMPARISON-LOWCOND-MATCH45` (source),
`AFFINE287-BALANCED7-MODULUS-AVERAGE45` (conditional compiler only).

**Source block.** No `Erdos287`, `WindowPairSupply`, `BalancedSeven`,
`AffineMuLog`, `Omega7` or `Factorial` module exists in this repository.  The
finite range check `3 ≤ M ≤ 4·10⁹` and the `WindowPairSupply ⇒ #287` compiler
named in the continuation prompt are **not present here** — they were neither
altered nor reconstructed.

## 7. R9 / FCL status

* `R9-LEAKAGE-MEMBERSHIP` — **direction corrected**: the balanced R9 vector has
  a coordinate `1/9` in the Type-II window, is therefore **not** in `R(P)`,
  hence outside `C(R(P))`, hence **in** the leakage set.  This is leakage, not
  disqualification.  The false R9 death certificate is not resurrected.  Status
  `SOURCE_OPEN` (the literal `R(P)`, `C(R(P))` and leakage set are absent); a
  source-pending dictionary with the corrected direction is banked.
* `R9-GDN-SPECIALIZATION` — `SOURCE_OPEN`.  `G(d;n)` is absent, so `70` is
  **not** identified with a physical Ford coefficient.  The alternating value
  `∑_{j=0}^{4}(−1)^j C(9,j) = 70` is reused from the existing bank, and its
  dependence on the cutoff convention is recorded.
* `P_ε` finite arithmetic is proved: `1/9 ± η` is neither tiny nor large, and
  `4(1/9+η) < 1/2−ε < 5(1/9−η)` for `ε ≤ 1/600`, `η < 1/90`.
* `FCL` — `SOURCE_OPEN`.  Ford-generated leakage is **not** treated as universal
  Type II; provider assignment must be proof-specific.

## 8. Public Lean-checked items (this layer)

All under `RequestProject/CurrentProgramme/`:

`StatusTypes`, `NormalisationFirewall`, `SmoothLocalisation`,
`RankOneLineAlgebra`, `FiniteLineFourier`, `EndpointBilinear`,
`EndpointExponentBank`, `AnalyticInterfaces`, `Gate1BEndpointCompiler`,
`FactorialEulerPolarization`, `PascadiParameterLedger`, `R9LeakageArithmetic`,
`FordGeneratedCensus`, `LocalEulerAlgebra`, `SourceStrata`, `CurrentStatus`,
`DependencyGraph`, `AxiomAudit`.

Additionally kernel-proved:

* `LocalEulerAlgebra` — `∑'_e (a^e/e!) T^e = exp(aT)`; the generalized von
  Mangoldt pattern `Λ_F(p) = a·log p`, `Λ_F(p^e) = 0` for `e ≥ 2`, *pinned* by
  the logarithmic-derivative recursion together with a uniqueness theorem.
  Class-C nomenclature remains a DEFINITION PIN.
* `SourceStrata` — exhaustive disjoint stratification of the endpoint
  off-diagonal energy by an arbitrary label map, and the `p₁ = p₂` vs
  `p₁ ≠ p₂` split for an arbitrary prime label (awaiting the β dictionary);
  the `|J| = 5..1` defect-order census with a no-blanket-monotonicity
  counterguard; and the well-founded proper-divisor recursion measure.

122 principal declarations pass `#print axioms` with only
`propext` / `Classical.choice` / `Quot.sound` (most with fewer).  No `sorry`,
`admit`, user `axiom`, `opaque`, `unsafe`, `native_decide` or
`@[implemented_by]`.

## 9. Externally audited items (metadata only — NOT Lean)

`MOTOHASHI-ABC-EXACT-PIN45`, `MOTOHASHI-FAMILY-UNIFORMITY45`,
`TWISTED-DEFECT-ABC45`, `FIVEFOLD-MOTOHASHI-ITERATION45`,
`LOCALIZED-FIVEFOLD-MOTOHASHI45` (BV side), `RANKONE-POLYLOGK-INTERIOR45`.

## 10. Open source pins

`PURE5-COMPARISON-MAINTERM-PIN`; physical `β = μ_D * Λ_P` dictionary;
`FORD-GENERATED-PACKET-CENSUS`; `RealFordGrammarCertificate`;
`R9-LEAKAGE-MEMBERSHIP`; `R9-GDN-SPECIALIZATION`; `FCL`; `QK56-EXHAUSTIVENESS`;
`SHIFTED-TTSTAR`; `WINDOWPAIRSUPPLY`; the `|J| = 4,3,2,1` source packets;
`NEARPRIM`; the `r>1` and transition-strip source packets.

## 11. Open analytic leaves

`RANKONE-ENDPOINT-U-OFFDIAG45` (first priority), `RANKONE-HIGHK45`,
`AFFINE287-FACTORIAL-OMEGA7-SIGNED-ENDPOINT45`, the BV/large-sieve input behind
`RANKONE-ENDPOINT-U-DIAGONAL45`, external BPP.

The source-neutral partition and recursion machinery these leaves will plug into
is already kernel-proved (see §8), so supplying a literal source now requires
only the label/measure data, not new finite algebra.

## 12. Superseded / false routes

* `SHIFT-SOURCE-LINKED-CHAR45` — `SUPERSEDED_AS_CONTROLLING_FRONTIER`.
* pointwise `‖δᵢ‖_∞ ≪ (log X)^{-1}` — **FALSE on primes**, refuted in Lean.
* the extra `∏_p 1/e_p!` factorial correction — **FALSE**, refuted in Lean.
* the R9 "death certificate" (outside `C(R(P))` ⇒ disqualified from leakage) —
  direction reversed.
* separate Parseval/Cauchy as a high-`k` closure mechanism — finite countermodel
  banked.
* `FULL_ROUTED_PIECE_POWER_SAVING_REFUTED_AS_STATED` — preserved from the
  earlier bank.

## 13. Master architecture (unchanged, and machine-checked)

```
finite source / Gate 0
      -> generated packet census
           -> Gate 1A     (census-conditional arrow)
           -> Gate 1B     (census-conditional arrow)
      -> Gate 2
      -> Ford-generated packet / leakage reassembly
      -> fixed-certificate leakage + comparison + effectivity
      -> positive affine mass
      -> WindowPairSupply
      -> existing finite compiler
      -> Erdős #287
```

Twin primes sits on a **separate** downstream branch under Full FM Type II.
`Graph.no_cross_implication` proves that neither of `#287` and twin primes
reaches the other.

## 14. Final status

    GATE1B: OPEN
    FULL FM TYPE II: OPEN
    ERDOS287: OPEN
    TWIN PRIME CONJECTURE: OPEN
