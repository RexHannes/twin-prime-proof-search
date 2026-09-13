# TWIN GATE1B / R11 — MINIMAL-KERNEL FORMAL SYNC REPORT

Programme: TWIN GATE1B / R11 only.
Mode: append-only formal frontier sync; unmodified-row bank preserved; Gate1A untouched.

**No claim is made that R11 is closed, that global Gate1B holds, that HSTAR holds, or that
the twin prime conjecture is resolved.** All analytic/asymptotic inputs are carried as
propositions or interfaces; none is inhabited, and no custom Lean axiom was introduced.

---

## 1. Files added

All under `Gate1B/R11/Frontier/`:

| file | contents |
|---|---|
| `CompleteDivisorFibre.lean` | `radNat`, the sharp divisor fibre `Hdiv z M = Σ_{d|M, d>z} μ(d) log(M/d)`, radical reindexing, coprime splitting, forced-fibre lemma, `Hdiv` at threshold `<1` equals `Λ`, physical source wrappers `Tsource`, `TsourceTotal` |
| `CenteredDivisorSource.lean` | `sourceWeight`, `progIndicator`, `principalIndicator`, `rawProgression` (L_C), `principalAverage` (MAIN_C), `centeredDiscrepancy` (E_C), the exact identity `L_C = E_C + MAIN_C`, and the current exact centered source `E_R11` |
| `PrincipalTailInterface.lean` | `muDivId`, `oneDivId`, `muDivPhi`, local factors `hLocal`, the convolution identity, `piTail` (Π(n;z)), `Ares`, `bigPrimeCount`, `lambdaClass`, owner identity, `mainClass`, principal reassembly, analytic propositions `PrincipalTailBound`, `CompletePrincipalBound` |
| `SquarefullCore.lean` | `sqFullPart`, `sqFreeCore`, `IsSquarefull`, existence and uniqueness of `M = b·a`, explicit firewalls against `M/rad M` and against `b` being a square |
| `SquarefreeCoreReflection.lean` | `reflectedSum`, the exact reflected divisor identity `Hdiv_reflection` (strict inequality preserved), the local `e`-sum and its prime-power / ω ≥ 2 corollaries |
| `SchinzelSzekeresKernel.lean` | `Fgap`, monotonicity, `Fgap_le_iff`, `tailPart`, the structure theorem `Fgap_eq_sup_tail`, the squarefree prime-factor formula |
| `DenseSupportFirewall.lean` | `nextDiv`, `FactorSupport`, `GapBound`, the equivalence `factorSupport_iff_gapBound`, `Fgap_le_of_factorSupport`, the named interface `SchinzelSzekeresSupport`, a concrete instance at `d = 6, Q = 12`, and the well-factorability countermodel |
| `MinimalGapKernel.lean` | `IsMinKernel`, existence of a kernel divisor, `lcm_gt_of_minKernel`, uniqueness per `M ≤ x`, cofactor coprimality/size, bad-divisor classification, kernel-rank cofactor bounds with rank 2 / rank 3 specialisations |
| `BadGapFibreContraction.lean` | `Hbad`, the contraction `Hbad = μ(v)·H_{z/v}(m)`, the collapse to `μ(v)·Λ(m)` when `v > z`, and vanishing for non-prime-power cofactor |
| `ComplementThresholdFibre.lean` | full `p`-adic containment above the complement threshold, large-prime-square vanishing, two-large-prime and one-large-prime fibre identities, prefix-minus-Λ form |
| `PrimeKernelBridge.lean` | `Fgap_prime`, `isMinKernel_prime_iff` (`p` a kernel ⇔ `x < p²`), the exact bridge source formula, short-variable range lemmas, `BridgeExponentRange` interface and transport |
| `MinimalKernelStatusBank.lean` | squarefull mask partition/disjointness, `LargeSquarefullTailBound` proposition, D/P/J divisor tags, the source reassembly `Tsource = Tkernel = 252(D+P+J)`, the OPEN proposition `DPJBalance`, the status taxonomy `MKStatus`/`MKRow`/`mkStatus`, bank re-ascriptions, retired-method firewalls, `omegaC_provenance_improved_partial`, `CanonicalSourceCovers`, `minimalKernel_open_frontier` |

Report file: `TWIN_GATE1B_R11_MINIMAL_KERNEL_FORMAL_SYNC_REPORT.md` (this file).

## 2. Files modified

Only the two permitted aggregators:

* `Gate1B/R11/Frontier/Bank.lean` — added imports of the new modules and `minimalKernel_bank_loaded`.
* `Gate1B/R11/Frontier/AxiomAudit.lean` — appended `#print axioms` lines for all new principal theorems.

Nothing else was edited. **Gate1A is unchanged.** All pre-existing Frontier modules
(`OccupiedRowKernel`, `ProductFibrePushforward`, `EmptySiteRepairTransfer`,
`UnmodifiedRowInterpolation`, `CriticalMixedIncidence`, `RealOverlapSupport`,
`CriticalMaskFirewall`, `NewCritStatusBank`, `StatusBank`, and the earlier exact-source
modules), together with `R_hi`, `R_newcrit` and the character/Mellin definitions, are
retained untouched and re-ascribed historically in the new status bank
(`previous_bank_preserved`).

## 3. Exact kernel-proved mathematics

Every item in this section is a Lean theorem with a complete proof; none uses `sorry`.

1. **Complete divisor fibre.** Definition of `Hdiv`; radical reindexing
   (`Hdiv_eq_sum_radNat`); coprime divisor splitting; forced-fibre identity
   (`Hdiv_forced_fibre`, `sum_fibre_dvd`); `Hdiv z m = Λ m` for `z/… < 1`
   (`Hdiv_of_lt_one`); the abstract physical-source wrapper `T_C = 252 Σ_n Ω_C(n) H_{z_C}(n+2)`.
2. **Centered decomposition.** `L_C = E_C + MAIN_C` as an exact finite identity, and the
   kernel-proved *definition* of the current centered source `E_R11`.
3. **Principal coefficient convolution.** `muDivId * oneDivId = 1`,
   `muDivId * hLocal r = muDivPhi r`, and the coefficientwise form
   `μ(d)/φ(d)·1_{gcd(d,r)=1} = (μ/id ∗ h_r)(d)`, together with the multiplicative local
   factors `h_r(p^a) = p^{-a}` for `p | r` and `h_r(p^a) = -1/(p^a(p-1))` for `p ∤ r`.
4. **Owner identity and reassembly.** `λ₀ − λ₁ + λ₂ = μ` on the declared source domain
   (at most two large divisors), and `MAIN₀ − MAIN₁ + MAIN₂ = Σ_n Ω_C(n) Π(n;z_C)` as a
   conditional finite-sum/source identity.
5. **Squarefull core.** Existence and uniqueness of `M = b·a` with `b = SqFull(M)`
   squarefull, `a` squarefree, `gcd(a,b) = 1`; explicit firewalls: `SqFull(8) = 8 ≠ 8/rad 8`
   and `SqFull(8)` is not a square.
6. **Squarefree-core reflection.** The exact reflected divisor identity for `H_z(ba)` with
   the strict inequality `z·g < a·e` preserved and no multiplicity introduced.
7. **Local e-sum.** `Σ_{e | rad b} μ(e) log(bg/e) = log g` if `b = 1`, `= log p` if
   `b = p^ν` with `ν ≥ 1`, and `= 0` if `ω(b) ≥ 2`. Recorded as an *alternative
   representation only* — it is never subtracted as a second owner.
8. **Schinzel–Szekeres function.** `Fgap(d) = max_{v|d, v>1} v·Pmin(v)`, `Fgap(1) = 1`;
   monotonicity under divisibility; the structure theorem reducing the maximum to prime
   tails; and the exact squarefree prime-factor formula.
9. **Dense support characterisation.** Factor-support feasibility at level `Q` (every
   factorisation `Q₁Q₂ = Q` admits `a | d` with `a ≤ Q₁`, `d/a ≤ Q₂`) is *equivalent* to the
   consecutive-divisor gap bound, and implies `Fgap(d) ≤ Q`.
10. **Minimal bad-gap kernel.** Definition; `v·Pmin(v) > x`; `Fgap(v/p) ≤ x`; existence of a
    kernel divisor; distinct kernels have `lcm > x`; hence **at most one minimal kernel
    divides any `M ≤ x`**.
11. **Bad-divisor classification.** For `M = v·m ≤ x`: `m < Pmin(v)`, `gcd(m,v) = 1`, and the
    bad squarefree divisors of `M` are exactly `v·e` with `e | m` squarefree.
12. **Bad-gap fibre contraction.** `H_bad(z,x,M) = μ(v)·H_{z/v}(m)`; under `v > z`,
    `H_bad = μ(v)·Λ(m)`; hence `H_bad = 0` whenever `m = 1` or `m` is not a prime power.
13. **Kernel-rank cofactor range.** With `r = ω(v)`: `Pmin(v)^r ≤ v`, `x^r < v^{r+1}` and
    `m^{r+1} < x` (integer-power forms of `v > x^{r/(r+1)}`, `m < x^{1/(r+1)}`), with the
    `r = 2` (`m³ < x`) and `r = 3` (`m⁴ < x`) specialisations.
14. **Complement-threshold high fibre.** Every divisor `d > D` contains the full `p`-adic
    part of `M` for `p > K_M = M/D`; a large prime square kills `H_D(M)`; the two-large-prime
    identity `H_D(M) = Λ(m)` and the one-large-prime identity `H_D(pm) = −H_{D/p}(m)` with the
    prefix-minus-Λ form.
15. **Prime-kernel bridge (source algebra).** `Fgap(p) = p²`, `IsMinKernel x p ↔ x < p²`, and
    the exact bridge source formula producing the short variable `e | m`, `e > z/p`.
16. **Prime-power support.** `Λ(m) ≠ 0 ⇒ m = ℓ^j` with `ℓ` prime, `j ≥ 1`.
17. **Source partition and reassembly.** The squarefull mask partition `SqFull(M) ≤ V`
    vs `> V` with disjointness and no double charge; the dense / kernel-prime-power /
    prime-kernel-bridge tag split of the divisor fibre; and
    `T_source = T_kernel = 252 (D + P + J)`.
18. **Well-factorability countermodel.** An explicit finite rank-two signed chart which is
    not a product weight, together with dense factor support in the same example. This
    kernel-proves *dense support does not imply complete signed coefficient
    well-factorability*. No impossibility of expressing the source as an affordable **sum**
    of well-factorable owners is asserted.

## 4. Analytic interfaces (never inhabited, no axiom)

The following are Lean `Prop`-valued definitions or named interfaces. They appear only as
hypotheses in transport lemmas; no term of any of them is constructed anywhere.

* `PrincipalTailBound` — `Π(n;z) ≪ L^{-J}`.
* `CompletePrincipalBound` — combined principal `O(x L^{-S₀-2})`.
* `LargeSquarefullTailBound` — the `SqFull(M) > V` error sector with
  `V = L^{2(S₀+C_Ω+6)}`.
* `SchinzelSzekeresSupport` — the converse direction `Q ≥ Fgap(d) ⇒ FactorSupport d Q`,
  i.e. the classical identity `Fgap = d·G(d)`.
* `BridgeExponentRange` — the research exponent `x^{1/22−ε_safe+o(1)}`, carried as a range
  interface only.
* `DPJBalance` — the analytic balance `|D + P + J| ≪ x L^{-S₀}`. **OPEN.**
* `CanonicalSourceCovers` — the unproved "canonical source covers full physical source"
  statement, carried as a hypothesis of a transport lemma only.

## 5. Evidence levels

* **Principal theorem (complete principal smallness).**
  `EXTERNAL_ANALYTIC / CONDITIONAL_ANALYTIC`. The finite coefficient convolution, local
  factors, owner identity and reassembly are kernel-proved; the arbitrary-log Mertens bound
  and the `O(x L^{-S₀-2})` estimate are hypotheses. Recorded as *analytically closed at the
  declared external-theorem scope*, and the remaining centered source is **not** marked closed.
* **Large-squarefull tail.** `EXTERNAL_ANALYTIC / CERTIFICATE_BACKED`. Only the partition,
  disjointness and no-double-charge logic are kernel-proved.
* **Schinzel–Szekeres.** The function `Fgap`, its structure theorem and the squarefree
  prime-factor formula are `KERNEL_PROVED`. The classical identity `Fgap(d) = d·G(d)` is
  **not** kernel-proved: instead the dense support characterisation is kernel-proved in the
  equivalent `FactorSupport ↔ GapBound` form, the implication
  `FactorSupport → Fgap ≤ Q` is kernel-proved, and the reverse implication is carried as the
  explicit named theorem interface `SchinzelSzekeresSupport` (never inhabited, not an
  axiom), with a concrete verified instance at `d = 6`, `Q = 12`.
* **Minimal-kernel uniqueness, bad-gap fibre contraction, rank bounds, bad-divisor
  classification, prime-kernel bridge source algebra, D+P+J decomposition.** All
  `KERNEL_PROVED`.
* **D + P + J analytic bound.** `OPEN`; the proposition is defined but never inhabited.

## 6. Source provenance

`OmegaC_provenance = IMPROVED_PARTIAL`, recorded formally in the status bank. `Ω_C` is kept
as an abstract physical source parameter; it is **not** replaced by an eleven-prime model,
and the coverage statement is a hypothesis, not a theorem. Missing provenance is treated as
an open source interface.

## 7. Retired branches / firewalls (recorded, not proved impossible)

* Character/Mellin as an active closing procedure: `RETIRED_NONCLOSING` at the tested
  architecture scope (definitions preserved historically).
* Moving-`y` closing family: `RETIRED / FULLY_COOKED` at its tested theorem/dictionary scope.
* Free principal removal in the old empty-site repair: retired; the algebra is preserved.
* Complete dense weight as one well-factorable sequence: `REJECTED_FALSE` (countermodel).
* Pascadi as complete owner: `METHOD_NONCLOSING` at tested scope.
* Open `g | a` → ordinary Mertens: `METHOD_NONCLOSING / EXACT LOOP`.
* Average-shift → fixed shift 2: no legal dictionary.
* Reciprocal exponential → Kloosterman by name: no legal dictionary.

No universal impossibility statement is formalized.

## 8. Current frontier

`minimalKernel_open_frontier` records, with `frontier_open_rows` proving that the open rows
are indeed open:

| row | status |
|---|---|
| complete principal | closed at declared analytic scope |
| large squarefull sector | closed at declared analytic scope |
| Schinzel–Szekeres source algebra | KERNEL_PROVED |
| unique minimal kernel | KERNEL_PROVED |
| bad-gap fibre contraction | KERNEL_PROVED |
| kernel-rank cofactor bounds | KERNEL_PROVED |
| dense owner | OPEN |
| kernel prime-power owners | OPEN / STRICTLY REDUCED |
| prime-kernel bridge | OPEN / STRICTLY REDUCED |
| D + P + J signed balance | OPEN |
| R11 | STRICTLY_REDUCED / OPEN |
| Global Gate1B | OPEN |
| HSTAR | OPEN |
| Twin Prime | OPEN |

No open proposition is inhabited.

## 9. Build result

* Dedicated build: `lake build Gate1B.R11.Frontier.Bank Gate1B.R11.Frontier.AxiomAudit`
  — **PASS** ("Build completed successfully", 8071 jobs), no errors and no warnings.
* Repository-wide diagnostic build: **PRE-EXISTING FAILURE**, unchanged from baseline and
  unrelated to this work: `RequestProject/FixedCertificateAlgebra.lean` is imported by
  `K0K1Status.lean` and `RequestProject/CurrentProgramme/R9LeakageArithmetic.lean` but does
  not exist in the repository (it has never existed in git history). No attempt was made to
  repair unrelated code.

## 10. Axiom audit

`Gate1B/R11/Frontier/AxiomAudit.lean` runs `#print axioms` on every new principal theorem
(≈ 55 declarations). Every one depends only on a subset of
`{propext, Classical.choice, Quot.sound}`; two depend on no axioms at all.

A machine scan of `Gate1B/R11/Frontier/*.lean` finds no `sorry`, no `sorryAx`, no `admit`,
no custom `axiom`, no `native_decide`, no `Lean.trustCompiler`, no `unsafe`, no
`@[implemented_by]` and no `opaque` proof escape (the only textual matches are inside the
audit module's documentation comment).

**AXIOM AUDIT: PASS.**
