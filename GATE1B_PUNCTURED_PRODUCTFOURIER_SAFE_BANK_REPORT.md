# GATE 1B · PUNCTURED PRODUCT-FOURIER SAFE BANK REPORT

Append-only delta.  No historical mathematical module was edited or deleted.
Everything banked below is **exact finite linear algebra, exact arithmetic, or
a purely logical implication**.  No analytic estimate is proved, none is
assumed, no analytic interface is inhabited, and Gate 1B closure is **not**
claimed.

---

## FILES ADDED

| File | Content |
|---|---|
| `Gate1B/PuncturedFourierFrame.lean` | §1 punctured finite Fourier frame, §2 unit-dilated frame, §5 finite product-Fourier operator |
| `Gate1B/PrimitiveDeterminantProductPhase.lean` | §3 primitive determinant arithmetic, §4 product phase factorisation, §6 gcd Möbius identities, §7 prime divisor router, §8 original-zero / cyclic-zero firewall, §11 conditional compiler |
| `Gate1B/CurrentStatusGate1BPuncturedProductFourier.lean` | §9 append-only Gate 1B status layer with a separate research-only status datatype |
| `Gate1B/AxiomAuditGate1BPuncturedProductFourier.lean` | §12 `#print axioms` for all 72 principal new declarations |
| `GATE1B_PUNCTURED_PRODUCTFOURIER_SAFE_BANK_REPORT.md` | this report |

## FILES MODIFIED

* `Main.lean` — **imports appended only** (four `import Gate1B.…` lines and a
  comment).  No other file in the repository was modified.

Note on build targets: the new modules are in the `Gate1B` library, which is a
default target of `lakefile.toml`, so they are built by the default target
independently of `Main.lean`.

---

## KERNEL-CHECKED ARITHMETIC

`Gate1B/PrimitiveDeterminantProductPhase.lean`, namespace
`TwinPrimeProject.CurrentProgramme.PrimitiveDeterminant`:

* `doubleGcd_dvd_shift` / `doubleGcd_dvd_shift_gcd` — with `X₁ = d a`,
  `X₂ = d b`, `Z₁ = e c`, `Z₂ = e f`, `X₂Z₂ − X₁Z₁ = ℓ r` and `gcd(de, ℓ) = 1`
  (both `IsCoprime` and `Int.gcd`-forms), one gets `de ∣ r`.
* `primitiveDeterminant_factor` — for `d ≠ 0`, `e ≠ 0` and `r = (de) r₀`:
  `b f − a c = ℓ r₀`.  The residual variables are exactly the ones produced by
  the factorisation; no coprimality of `a, b, c, f` is assumed or claimed.
* `primitiveDeterminant_nonzero_of_shift_nonzero` — `ℓ ≠ 0`, `r₀ ≠ 0` imply
  `bf − ac ≠ 0`.
* `sameX_semidiagonal_impossible`, `sameZ_semidiagonal_impossible` — the
  semi-diagonal exclusions.  The physical bounds `r ≠ 0` and `|r| < |d|`
  (resp. `|r| < |e|`) are **explicit hypotheses**; no analytic inequality is
  derived here.
* `determinant_phase_factorization`, `determinant_phase_factorization_int` —
  from `bf − ac = ℓ r₀`: `e_M(k ℓ r₀) = e_M(k b f) · e_M(−k a c)`; the integer
  version takes the integral determinant identity and factors the mod-`M`
  phases.
* `divisors_filter_dvd`, `sum_moebius_divisors`, `coprime_indicator_mobius`,
  `double_coprime_indicator_mobius` — the finite gcd Möbius identities
  `1_{gcd(a,b)=1} = ∑_{ρ ∣ a, ρ ∣ b} μ(ρ)` and its two-variable form, built on
  Mathlib's Möbius inversion.  **No analytic divisor moment is formalised.**
* `prime_dvd_mul_router`, `le_of_dvd_pos`, `prime_dvd_mul_router_ge` — for
  prime `M`, `M ∣ ρσ → M ∣ ρ ∨ M ∣ σ`, and the arithmetic consequence that a
  positive variable divisible by `M` is `≥ M`.  This supports the analytic
  large-divisor router; **the analytic estimate itself is not formalised.**

## FINITE LINEAR ALGEBRA

`Gate1B/PuncturedFourierFrame.lean`, namespace
`TwinPrimeProject.CurrentProgramme.PuncturedFourier`
(`e_M = ZMod.stdAddChar`, `nzFreq M = {k : ZMod M | k ≠ 0}`):

* `punctured_char_sum` — `∑_{k ≠ 0} e_M(k b) = M·1_{b=0} − 1`.
* **`puncturedFourier_gram`** — `∑_{k ≠ 0} e_M(kr) conj e_M(kr') =
  M·1_{r=r'} − 1`, i.e. the Gram identity of the punctured frame.
* `puncturedFourier_gram_matrix` — the matrix form
  `V Vᴴ = M · 1 − J` for `V : Matrix ↥I ↥(nzFreq M) ℂ`, `V(r,k) = e_M(k r)`.
* `frame_energy_identity` / `frame_energy_real` — the exact energy identity
  `∑_{k≠0} |c(k)|² = M ∑_{r∈I} |y(r)|² − |∑_{r∈I} y(r)|²` for `c = Vᴴy`.
* **`puncturedFourier_posDef`** — `(M − #I)‖y‖² ≤ ∑_{k≠0} |c(k)|²`;
  `puncturedFourier_posDef_of_two_card_lt` gives the source form `(M/2)‖y‖² ≤ …`
  under `2#I < M`; `puncturedFourier_posDef_strict` gives strict positivity for
  `#I < M` and `y ≠ 0` on `I`.
* **`puncturedFourier_surjective`** — every `F` on `I` is realised with
  frequencies away from `0`.
* **`puncturedFourier_fullRowRank`** — `rank V = #I` for `#I < M`.
* **`puncturedFourier_minNorm_coeff_bound`** (and its divided form
  `puncturedFourier_minNorm_div`) — the requested coefficient theorem: for
  `#I < M` and any `F` there is `c` with `c 0 = 0`,
  `F(r) = ∑_{k≠0} c(k) e_M(k r)` on `I`, and
  `‖c‖₂² (M − #I) ≤ ‖F‖₂²`, i.e. `‖c‖₂² ≤ ‖F‖₂²/(M − #I)`.
  This is proved as an exact finite identity plus Cauchy–Schwarz — the explicit
  minimiser is `c = Vᴴ(V Vᴴ)^{-1}F`, whose energy is exactly
  `‖F‖²/M + |∑F|²/(M(M − #I))`.  No axiom, no Hilbert-space abstraction.
* Dilated frame: `puncturedFourier_unitDilate_gram`,
  `puncturedFourier_unitDilate_gram_matrix`,
  `puncturedFourier_unitDilate_gram_eq` (Gram literally equal to the undilated
  one for a unit `ℓ`), `puncturedFourier_unitDilate_surjective`,
  **`puncturedFourier_unitDilate_rank`** (`rank V_ℓ = #I`).
* Product-Fourier operator `T_λ(r,s) = e_M(λ r s)`:
  **`productFourier_orthogonality`**, **`productFourier_gram`**
  (`T_λᴴ T_λ = M · 1` for a unit `λ`), **`productFourier_norm_sq`**
  (exact Plancherel: `∑_s |∑_r c(r) e_M(λ r s)|² = M ∑_r |c(r)|²`).
  The operator-norm statement `‖T_λ‖ = √M` is an **analytic consequence
  recorded here in the report only**; it is not a Lean theorem of this bank.

### ORIGINAL-ZERO / CYCLIC-ZERO FIREWALL

* `originalZero_preserved` — `bf − ac = 0` implies `(bf − ac : ZMod M) = 0`.
  This is the only implication proved.
* `cyclicZero_not_identified` — explicit countermodel (`M = 5`, `bf − ac = 5`):
  a cyclic zero is **not** an original determinant zero.
* `cyclicZero_ne_originalZero` — the two predicates are not equivalent, as a
  theorem.  **No false equality is encoded anywhere.**
* `puncturedFrame_uses_nonzeroOnly`, `puncturedSynthesis_indep_of_zero_freq` —
  the punctured frame avoids the auxiliary zero frequency entirely: the zero
  frequency is not in the index set, and the synthesis operator does not see a
  coefficient at `0`.

## CONDITIONAL ANALYTIC COMPILERS

* `PrimitiveDeterminant.conditional_net_compiler` — purely logical: from
  `hSupport : A ≤ C·T/√E`, `hProduct : B ≤ A/√M`, `hScale : M = T/E`
  (with `0 < E`, `0 < T`) it derives `B ≤ C·√T`.
  **Its antecedents are hypotheses, not theorems of this repository, and are
  not supplied anywhere.**  The ledger row is `conditionalCompiler`, which by
  the repository firewall (`not_closed_of_conditionalCompiler`) is never
  `closed`.

## RESEARCH-ONLY STATUS

Recorded in `Gate1B/CurrentStatusGate1BPuncturedProductFourier.lean` through a
**separate datatype** `ResearchStatus` (constructors
`candidateResearchClosedExternally`, `researchOpen`), which is *not* a `Status`
and maps only to non-kernel-proved statuses.  The Lean firewalls
`researchStatus_never_kernelProved` and `researchStatus_never_closed` make the
confusion impossible.

```
SOURCE-EXACT / FORMAL BANK
  DoubleGcdPrimitiveDet         : PASS   (kernel-checked)
  PuncturedFourierFrame         : PASS   (kernel-checked)
  ProductFourierGram            : PASS   (kernel-checked)
  PrimitiveGcdMobiusIdentity    : PASS   (kernel-checked)

RESEARCH STATUS ONLY
  HZeroPrimitiveDetNonzeroFull      : candidateResearchClosed / externally
                                      closed under frozen source bank
  HZeroHighHighAnalytic             : candidateResearchClosed / externally
                                      closed under frozen source bank
  HNeSawtoothAPReciprocalMismatch   : OPEN
  TopBandBroadMajorTreeMatch        : OPEN
  Gate1B                            : OPEN
```

## NOT FORMALISED

No Lean theorem was invented for any of the following; each is recorded as an
open ledger row and, where used, appears only as a named hypothesis of a
conditional compiler:

* E-cell `T/√E` support estimate;
* fixed-depth `α`/`γ` divisor moments;
* net analytic `M^{-1/2}` compiler;
* `h ≠ 0` reciprocal closure;
* local broad-major tree match;
* Gate 1B closure;
* the operator norm `‖T_λ‖ = √M` (only the exact Gram / Plancherel identities
  are proved).

## AXIOM AUDIT

`Gate1B/AxiomAuditGate1BPuncturedProductFourier.lean` runs `#print axioms` on
all **72** principal new declarations.  Result:

* 7 declarations depend on **no axioms**;
* 65 depend on a subset of `{propext, Classical.choice, Quot.sound}`;
* union over all new declarations: exactly
  `{propext, Classical.choice, Quot.sound}`;
* `sorryAx` occurrences: **0**.

No new custom axiom is declared anywhere in this delta.

## UNSAFE TOKEN AUDIT

Token grep over the four new `.lean` files for
`sorry`, `admit`, `axiom`, `unsafe`, `native_decide`, `opaque`,
`implemented_by`: **no occurrence** (the only matches anywhere are the words
inside this report and inside documentation comments describing the audit).

## FULL BUILD

* **New modules: PASS, 0 errors.**  Each of
  `Gate1B.PuncturedFourierFrame`,
  `Gate1B.PrimitiveDeterminantProductPhase`,
  `Gate1B.CurrentStatusGate1BPuncturedProductFourier`,
  `Gate1B.AxiomAuditGate1BPuncturedProductFourier`
  was built with `lake build <module>`: zero errors, zero warnings,
  no `sorry`.
* **Default target (`lake build`): FAIL, for pre-existing reasons that predate
  this delta and are untouched by it.**  The repository as supplied is missing a
  number of modules that legacy files import; the corresponding sources exist
  only as flat top-level files, e.g.
  `RequestProject.FixedCertificateAlgebra`, `RequestProject.Options`,
  `RequestProject.FordMaynardInterface`, `RequestProject.VaughanPacketAlgebra`,
  `Gate1A.Exponents`, `Gate1B.AdditiveCoordinate`, `Gate1B.AntiCartesian`,
  `Gate1B.CRTProduct`, `Gate1B.LocalDensity`, `UniversalV8.BlockGram`,
  `UniversalV8.BoundedVariation`, `UniversalV8.Budget`,
  `UniversalV8.Countermodels`, `UniversalV8.DefectCapacity`,
  `UniversalV8.DiscreteAbel`, and the `Universal.SafeAlgebra.*` /
  `RequestProject.NANC.*` modules that depend on them.
  Every failure in the build log is a `bad import` / `no such file` of one of
  those historical modules.  **No new module imports any of them, no new module
  appears in any error, and repairing the historical tree would require editing
  or relocating old modules, which this append-only delta does not do.**

## CURRENT FIRST ANALYTIC RESEARCH RESIDUAL

```
C4SHIFT-SAWTOOTH-APRECIPROCAL-MISMATCH45.
```

## PARALLEL LOCAL RESIDUAL

```
TOPBAND-BROAD-MAJOR-TREE-MATCH45.
```

## GATE1B

```
OPEN.
```

STOP.
