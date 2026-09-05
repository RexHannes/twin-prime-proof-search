# UNIVERSAL v9.1 — GATE 1A SOURCE-CERTIFICATE / WEIGHTED-ROOT / DEFECT-MULTIPLIER

Safe formal extension of the Gate 1A v9 postdet/amplifier-line bank.

---

## A. Regression

| item | value |
|---|---|
| HEAD at session start | `b5d73be` ("Initial commit") |
| Baseline `lake build` | Build completed successfully (8406 jobs), 0 errors |
| Final `lake build` | Build completed successfully (8435 jobs), 0 errors |
| Files deleted | none |
| Existing theorems modified or weakened | none |
| Existing v9 files edited | none |

Only pre-existing warning: `manifest out of date: source kind of dependency 'mathlib' changed`.
It is unrelated to this extension and was present before any edit.

## B. Environment

| item | value |
|---|---|
| Lean toolchain | `leanprover/lean4:v4.28.0` |
| Mathlib | pinned revision in `lake-manifest.json` (`v4.28.0` tag) |
| Default targets | `RequestProject`, `Gate04Root`, `Gate1A`, `Gate1B`, `UniversalV8`, `Universal` |
| Glob | `RequestProject.+` — every new file below is a default build target |

## C. v9 bank preserved

The following v9 modules were read (`#check`/search) and **reused, not restated**:

`PMLSNormalization`, `ComplementaryDivisor`, `DoubleDeterminant`, `NDeltaPushforward`,
`ReducedPlucker`, `ReducedConductor`, `PostDeterminant`, `DeltaLCMRouter`,
`AmplifierBudget`, `AmplifierLine`, `AmplifierLinePostDet`, `FamilyIndexGuard`,
`SignedParentGuard`, `ReciprocalProductDFT`, `Status`, `AnalyticInterfaces`.

No declaration in any of these files was touched. No proved theorem was duplicated.

## D. Root multiplier

File: `RequestProject/NANC/Gate1A/SafeExtensions/RootMultiplier.lean`
Namespace: `TwinPrimeProject.NANC.Gate1A.V91`

Finite commutative-ring algebra only; units, never unsafe division.

| declaration | content |
|---|---|
| `rootMultiplierU` | `u = -theta*delta * (inverse q2)^2` |
| `rootMultiplierKappa` | `kappa = -theta*delta * inverse q1 * (inverse q2)^2` |
| `rootMultiplierKappa_eq_u_mul` | `kappa = u * inverse q1` |
| `rootMultiplierU_indep_q1` | **u does not depend on `q1`** (exact, two arbitrary `q1`, `q1'` give the same `u`) |
| `inv_unique_of_mul_eq_one` | uniqueness of inverses in a commutative ring |
| `rootMultiplier_rewrite` | with `ell1 = q2*(t+a)` and explicit unit hypotheses on `q1, q2, t+a`: `-theta*delta * inverse (q1*ell1) * inverse q2 = kappa * inverse (t+a)` |
| `rootMultiplier_mod_cleanFactor` | image under any ring hom to `ZMod pi`: `kappa mod pi = u mod pi * inverse (q1 mod pi)`, with the `q1`-independence of `u` exposed |

No asymptotics appear anywhere in the file.

## E. Clean-factor unit router

Same file.

* `hardDelta_isUnit_mod_cleanPrime` — `pi` prime, `delta : ℤ`, `0 < |delta| < pi` ⟹ `(delta : ZMod pi)` is a unit. Pure finite arithmetic.
* `rootMultiplierU_isUnit_mod_cleanPrime` — under explicit `theta`-unit and `q2`-unit hypotheses plus hard-delta, `u` is a unit mod `pi`.

The analytic inequality `|delta| ≤ L/M < pi` is **not** encoded as a theorem.
Rational-exponent budget arithmetic is kept separate (see `BPPBudget.lean`, section on ℚ budgets).

## F. Weighted root analysis

File: `WeightedRootDefect.lean`.

```
rootAnalysis f z = ∑_{(q,h,α) : ρ q h α = z} β q h α * f q h α
fibreMass z      = ∑_{(q,h,α) : ρ q h α = z} ‖β q h α‖²
```

| theorem | statement |
|---|---|
| `rootAnalysis_sq_le` | fibrewise Cauchy–Schwarz: `‖rootAnalysis f z‖² ≤ fibreMass z * (fibre f-mass)` |
| `weightedRootAnalysis_of_fibreBound` | if every fibre mass `≤ C` then `∑_z ‖rootAnalysis f z‖² ≤ C * ‖f‖²` |
| `weightedRootAnalysis_energy` | the max form: `∑_z ‖rootAnalysis f z‖² ≤ (max_z fibreMass z) * ‖f‖²` |

This **permanently replaces the old arbitrary-Hilbert promotion**: the constant is an
explicit finite fibre mass, not an abstract operator norm.

## G. Residue-mass interface → root fibre

Same file.

* `unitRootMap u q h = u * h * inverse q` in `ZMod pi`.
* `weightedRootFibre_of_residueMass` — **mandatory v9.1 public theorem.**
  Hypotheses: `u` is a unit and independent of the averaged `q`-slot; for every fixed
  `(α, q)` and every residue class `c`, the `h`-square-mass in the class is `≤ C/pi ×`
  total `h`-square-mass. Conclusion: every root fibre `β`-square-mass is `≤ C/pi ×`
  total `β`-square-mass. **Active `α` labels are summed on both sides**; there is no
  "`α` is inert" hypothesis.

No analytic Poisson/R2 estimate is proved or assumed. `OmegaResidueMass1A` remains an
open analytic/source interface (comments only).

## H. Nonunit firewall

`nonunitMultiplier_collapses_rootFibre` — if `u = 0 mod pi` then `ρ q h α = 0` for all
`h`, so the zero fibre carries the **entire unrestricted mass**; the `C/pi` conclusion is
therefore false in general without the unit hypothesis. Documented firewall:
*nonunit sectors must be excised before applying `weightedRootFibre`.*
No claim is made that the actual Gate nonunit sector is analytically closed.

## I. Finite defect multiplier

File: `DefectMultiplier.lean`, group `ZMod n`.

```
defectOp w f z = ∑_r w r * f (z - r)
dftHat f χ     = ∑_z f z * conj (χ z)          (finite additive characters)
```

| theorem | statement |
|---|---|
| `defectOp_character_eigen` | exact eigenvector identity: `defectOp w χ = dftHat w χ • χ` |
| `dftHat_defectOp` | `dftHat (defectOp w f) χ = dftHat w χ * dftHat f χ` |
| `dftHat_plancherel` | finite Plancherel for `ZMod n` |
| `defectOp_energy_le_fourierSup` | `‖defectOp w f‖₂² ≤ (sup_χ ‖dftHat w χ‖)² * ‖f‖₂²` |
| `FourierMultiplierBound w C` | every character coefficient of `w` has norm `≤ C` |
| `defectOp_of_multiplierBound` | `FourierMultiplierBound w C ⟹ ‖defectOp w f‖₂ ≤ C * ‖f‖₂` |

### No raw Fejér ℓ¹ claim

`defectOp_const_one` and `defectOp_l1_mass_not_canonical` exhibit a finite counterexample:
`w ≡ 1` has `∑_r |w r| = n` while its Fourier sup is `1`. Hence `∑_r |w r|` is **not** the
canonical resource; `FourierMultiplierBound` is the safe interface.

## J. Fixed-quotient finite kernel

File: `CorrectedS1.lean` (delivered together with the v9.2 correction line).

* `ee`, `ee_add`, `ee_neg`, `ee_period`, `ee_congr`, `ee_pow`, `ee_eq_one_iff`,
  `ee_scale`, `ee_collapse`, `sum_ee_range` — a self-contained finite additive-phase API.
* `correctedS1_closed_form`, `correctedQuotient_fourier` — exact finite Fourier identity
  for the centred quotient-interval kernel.
* `centeredQuotientKernel_withAmplitude` — multiplying the exact finite kernel by an
  **arbitrary abstract scalar amplitude** preserves the finite identity. The actual source
  amplitude `omega_x(m,ν)` is **not** invented from prose.
* `correctedQuotient_authoritative_match` / `correctedQuotient_match_c_two` — pinned sign
  convention: with `c = -2` and kernel `e_C(-h s)` both authoritative factors are
  reproduced; with `c = +2` only the `q`-factor matches. Reported honestly, not silently.

This is **not** marked as the full Gate source transcription.

## K. Projective crossed convolution

File: `ProjectiveSourceInterfaces.lean`.

* `projectiveCrossedConvolution` — exact finite identity
  `∑_{z₁ l₂ = z₂ l₁} ⟨A z₁, A z₂⟩ ⟨B l₁, B l₂⟩ = ∑_w ‖∑_{z l = w} A z ⊗ conj (B l)‖²`
  in the finite scalar formulation.
* `projectiveCrossedConvolution_of_fibreCard` — bounded-multiplicity corollary: if every
  `w` has at most `D` representations `z*l = w`, then `P ≤ D * ‖A‖² * ‖B‖²`.

No `X^{o(1)}` theorem is stated anywhere.

## L. Source interfaces

Two structures are defined and **deliberately left uninhabited**:

* `RootDefectSourceFactorization` (file `RootDefectFactor.lean`) — carries `State1`,
  `State2`, `Root`, packets `A1`, `A2`, defect weight `w`, the literal `hardParent`, and
  the equality `hardParent = rootDefectForm A1 A2 w`.
  `RootDefectSourceFactorization.bound` proves: factorization + residue-mass hypotheses
  (`C1`, `C2`) + `FourierMultiplierBound w CW` ⟹ hard-parent bound with constant
  `sqrt (C1*C2) * CW`.
* `ZeroProjectiveSourceFactorization` (file `ProjectiveSourceInterfaces.lean`) — carries
  the source coefficient, row packet `A`, graph packet `B`, factorization equality and
  fibre-card hypothesis; `.bound` proves the projective energy bound.

Combined finite operator inequality: `rootDefect_bilinear_bound` (file
`RootDefectFactor.lean`), together with the explicit finite Cauchy layer `l2norm`,
`l2norm_sq`, `l2norm_le_of_sq_le`, `abs_inner_le_l2`, `rootAnalysis_l2_le`,
`defectOp_l2_le`. This is the Lean-safe abstract content of `A₁* W A₂`.

**Status.**

```
ROOTDEFECT-SOURCE-FACTOR1A : INTERFACE OPEN  (no inhabitant; literal source
                             coefficient not located in the repository)
ZERO-PROJ-SOURCE-SPLICE1A  : OPEN INTERFACE  (no inhabitant)
```

## M. Sector table

File: `AllMExhaustiveness.lean` (`Gate1ACleanP3Sector`, `SectorStatus`, `sectorStatus`).
Statuses recorded are only those justified by an existing proved theorem:

| sector | status |
|---|---|
| `genericFullConductor` | `AnalyticInterfaceOpen` (`genericFullConductor_analyticOpen`) |
| `zeroReduced` / `projective` | `SourceInterfaceOpen` (`projective_sourceInterfaceOpen`) |
| `nonunit` | must be excised (`nonunitMultiplier_collapses_rootFibre`) |
| Gate 1A clean-P3 | **OPEN** |

`sectorStatus_not_all_banked` is a proved theorem: the sector table is *not* fully banked.
Nothing is hardcoded as "frozen bank closed".

## N. Closure certificate structure

`Gate1AClosureCertificates.lean`: `FinalBudgetMet`, `SectorEnergyCertificate`,
`Gate1ACleanP3ClosureCertificate`, and the compiler
`Gate1ACleanP3ClosureCertificate.toFinalBudget`.

The certificate is **NOT CONSTRUCTED**. Every missing sector is therefore a
machine-visible open field of the structure.

## O. Axiom audit

File: `V91Status.lean` runs `#print axioms` on the public v9.1 theorems:

`rootMultiplier_rewrite`, `rootMultiplier_mod_cleanFactor`,
`hardDelta_isUnit_mod_cleanPrime`, `weightedRootAnalysis_energy`,
`weightedRootFibre_of_residueMass`, `nonunitMultiplier_collapses_rootFibre`,
`defectOp_character_eigen`, `defectOp_energy_le_fourierSup`,
`rootDefect_bilinear_bound`, `projectiveCrossedConvolution_of_fibreCard`.

Result: only `propext`, `Classical.choice`, `Quot.sound` (several depend on no axioms).
**No user axiom.**

## P. Trust audit

Scan over `RequestProject`, `Gate1A`, `Gate1B`, `Universal`, `UniversalV8`, `Gate04Root`:

```
rg -n "^\s*(sorry|admit|axiom |opaque |unsafe )|native_decide|@\[implemented_by" --type lean
```

Only prose/doc-comment occurrences. **No code-level trust token.**

## Q. Final scientific status

* The v9 bank is preserved bit-for-bit.
* The v9.1 finite bank (root-multiplier algebra, clean-factor unit router, weighted root
  analysis, residue-mass → root-fibre, nonunit firewall, finite defect multiplier,
  Fourier-multiplier norm, combined root-defect bilinear bound, projective crossed
  convolution) is **complete and sorry-free**.
* The two source-factorization interfaces are **OPEN**: no inhabitant was constructed,
  because the literal authoritative source coefficients were not found in Lean form.
* **Gate 1A is not closed. Full Type II is not declared. Twin primes are not declared.**

```
FINAL VERDICT: ARISTOTLE_GATE1A_V9_1_SOURCE_CERT_BANK_PARTIAL
```

Partial (not complete) exactly because `ROOTDEFECT-SOURCE-FACTOR1A` and
`ZERO-PROJ-SOURCE-SPLICE1A` remain open interfaces.
