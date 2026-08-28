# UNIVERSAL / GATE 1B v8.4 — PRIME-CONDUCTOR CHARACTER COLLAPSE / HYBRID h-POISSON / PRIMITIVE PROJECTOR / DUAL DETERMINANT / H7 SELF-DUALITY FIREWALL

**SAFE REPROOF / REPAIR BANK — FORMALISATION REPORT**

Verdict: `ARISTOTLE_V8_4_GATE1B_PRIMECONDUCTOR_DUALDET_SAFE_BANK_PARTIAL`.

---

## A. Regression

`lake build` was run on the untouched checkout **before** any edit: PASS
(8495 jobs, 0 errors). All v8.4 work is append-only: new files only, no
existing module edited, no proof modified, no import repaired.

## B. Immutable v8.1 / v8.2 / v8.3 baseline

Every v8.1, v8.2 and v8.3 module is byte-identical to the pre-run state
(`git diff` against the pre-run commit consists exclusively of new files plus
the appended `LEDGER.md` block and this report). The v8.3 status file
`Gate1B/SafeExtensions/V83Status.lean` is unchanged and still builds.

## C. RF1D conductor state-count repair

`Gate1B/SafeAlgebra/RF1DConductorStateCount.lean` — PROVED_ALGEBRAIC.

* `conductorStateCount_capacity` : `C * C * (Q / C) = Q * C` for `C ∣ Q`;
* `conductorStateCount_factors` : the same with the three factors named
  (moduli `C`, primitive characters per modulus `C`, cofactors `Q / C`);
* `betaCharacterStateExponent` : `γ + γ + (ω − γ) = ω + γ` (ℚ exponents),
  and `betaCharacterStateExponent_gap` : the repaired exponent exceeds the
  cofactor-only exponent by exactly `2γ`;
* FIREWALL `conductorStateCount_ne_cofactorCount` : `Q/C` is **not** the state
  count when the character family is also summed (`Q = C = 4`: `1 ≠ 16`).

No analytic statement. The RF1D analytic theorem is not declared.

`Gate1B/SafeAlgebra/RF1DHighConductorCapacity.lean` — CAPACITY_ONLY.

* abstract capacity exponents `ce − qe` (for `C ≤ Y⁴`) and `2ce − qe − 4`
  (for `C ≥ Y⁴`), agreeing at the branch point `ce = 4`;
* `rf1d_transition_exponent` : at `C₀ = Q^{1/2} Y²` the high-branch exponent is
  `0`, i.e. `C₀²/(Q Y⁴) = 1`;
* `rf1d_belowTransition_margin` : `ce ≤ ce(C₀) − η ⟹` exponent `≤ −2η`
  (margin `Y^{−2η}`), plus the strict form and the `above transition ⟹ ≥ 0`
  complement;
* `rf1d_capacity_transfer` : the monotone transfer of a supplied bound of that
  abstract shape to `Y^{−2η}`, for `Y ≥ 1`.

## D. Lane-E empty

`Gate1B/SafeAlgebra/LaneEEmpty.lean` — PROVED_ALGEBRAIC + PROVED_FINITE.

* `laneEVExponent_consistent` : `9(5/18 − η/2) = 5/2 − (9/2)η`;
* `VExponent_mem_Ioc`, `VExponent_gt_two` : for `0 ≤ η < 1/9` the `Y`-exponent
  of `V` lies in `(2, 5/2]`, in particular `> 2`;
* `V_gt_Ysq` : hence `V > Y²` for `Y > 1`;
* `laneE_prime_not_dvd_e` : `0 < e < p ⟹ p ∤ e`;
* `laneE_empty`, `laneE_empty_setOf` : with `e ≤ Y² < V < p`, lane E is empty.

## E. Lane-C β factorisation

`Gate1B/SafeAlgebra/BetaCEPrimeSplit.lean` — PROVED_FINITE / PROVED_ALGEBRAIC.

* `prime_dvd_conductor` : `q = c e`, `p ∣ q`, `p ∤ e ⟹ p ∣ c`;
* `complement_eq` : `q = d p = c e`, `c = p c₀ ⟹ d = c₀ e`;
* `coprime_cleanSplit`, `moebius_split`, `moebius_complement` :
  `μ(d) = μ(c₀) μ(e)`;
* `rhoCE`, `betaSource` : the abstract restricted conductor coefficient and the
  source sum over the *same* explicit physical range predicate
  (`physicalSupport`), with an abstract `logWeight`;
* `betaCE_laneC_factor` : `β(ce) = μ(e) · ρ(c,e)`.

The analytic β weight is deliberately **not** formalised; the physical range
restriction remains explicit as a carried predicate.

## F. Induced Gauss factor and μ(e) cancellation

`Gate1B/SafeAlgebra/InducedGaussFactor.lean` — PROVED_ALGEBRAIC (Tier 2).

Mathlib's `gaussSum` is the sum `∑_a χ(a) ψ(a)` and the sums used here are
literally of that shape (`gaussSum_eq_abstract`), so the identity is stated in
the repository's Fourier convention. Mathlib does not expose the conductor /
induction API (primitive characters, induced characters mod `c e`, Ramanujan
sums), so the CRT split and the Ramanujan value are carried as explicit
hypotheses; the twist `χ*(e)` — where the orientation lives — is **derived**:

* `gaussShift_unit` : `∑_a χ(a) ψ(a t̄) = χ(t) ∑_a χ(a) ψ(a)` for `t t̄ = 1`;
* `induced_gauss_squarefree` : `τ_{ce}(ind χ*) = μ(e) χ*(e) τ_c(χ*)`.

`Gate1B/SafeAlgebra/InducedMuCancellation.lean` — PROVED_ALGEBRAIC.

* `moebius_sq_complex` : `μ(e)² = 1` for squarefree `e`;
* `beta_mul_inducedGauss_cancel_muE` and the instantiated
  `betaSource_mul_inducedGauss_cancel_muE` :
  `β(ce) τ_{ce}(χ) = ρ(c,e) χ*(e) τ_c(χ*)`.

FIREWALL: `μ(e)` is spent algebraically here and is **not** a remaining
cancellation resource.

## G. Prime CRT character factorisation

`Gate1B/SafeAlgebra/PrimeConductorCRT.lean` — PROVED_ALGEBRAIC.

* `primeConductor_char_equiv` : a pair of multiplicative functions transported
  along Mathlib's concrete `ZMod.chineseRemainder` is multiplicative mod `m n`;
* `crt_gauss_factor` / `primeConductor_gauss_factor` :
  `τ_c(χ) = χ_p(c₀) χ_{c₀}(p) τ_p(χ_p) τ_{c₀}(χ_{c₀})`, with **both** cross
  factors derived from `gaussShift_unit`, not hard-coded.

## H. Prime-character collapse

`Gate1B/SafeAlgebra/PrimeCharacterCollapse.lean` — PROVED_ALGEBRAIC (Tier 1,
concrete `DirichletCharacter ℂ p` and `AddChar (ZMod p) ℂ`).

* `allChars_gauss_collapse` : `∑_{χ mod p} τ_p(χ) χ(A) = φ(p) ψ(A⁻¹)`;
* `principal_gauss_eq_neg_one` : `τ_p(χ₀) = −1` for `ψ ≠ 1`;
* `nonprincipal_gauss_collapse` : `∑_{χ ≠ χ₀} τ_p(χ) χ(A) = (p−1) ψ(A⁻¹) + 1`.

`Gate1B/SafeAlgebra/PrimeCharacterCollapseNormalized.lean` — PROVED_ALGEBRAIC:
the `1/√p`-normalised form, with the correction `1/√p` recorded as a separate
exact term (`primeCollapseCorrection`) and isolated by
`normalized_collapse_correction_isolated`. No analytic estimate on it.

## I. Hybrid h-Poisson

`Gate1B/SafeAlgebra/HybridHPoissonResidue.lean` — PROVED_ALGEBRAIC.

* `residue_condition` : `m c̄₀ = a ⟺ m = a c₀` in `ZMod p`;
* `hybridResidueTransform` : the finite transform over the CRT period splits as
  `(p · 1_{t = a}) × (c₀`-Gauss factor with the character twist`)`, the
  `p`-factor being computed from `AddChar.sum_mulShift` for primitive `ψ_p`;
* `hybridResidue_congruence` : the same, with the constraint written as the
  congruence `m ≡ a c₀ (mod p)`.

`Gate1B/SafeExtensions/HybridHPoisson.lean` — CONDITIONAL_FINITE.
`hybrid_hPoisson_conditional`: given the dual expansion of the class-summed
weight as an **explicit hypothesis** (`hpoisson`), the twisted `h`-sum equals
the exact dual `m`-sum with the finite residue factor. The Poisson identity is
neither proved nor axiomatised; everything downstream of it (interchange, phase
recombination via `AddChar.map_add_eq_mul`, residue factor) is derived. This is
a coordinate transform, **not** a Gate estimate.

## J. Truncated dual-frequency uniqueness

`Gate1B/SafeAlgebra/DualResidueUniqueness.lean` — PROVED_FINITE.

The informal "the dual sum contains a single `m`" is **not** claimed. Instead:

* `residueClass_inter_interval_card_le_one` and the `Subsingleton` form: an
  interval of diameter `< p` meets each class mod `p` at most once;
* `truncatedDual_frequency_unique` : under `|m| ≤ M` and `2M < p` the dual
  frequency is unique.

The rapid-decay truncation of the infinite Fourier tail is recorded as
ANALYTIC_INTERFACE_ONLY (see also countermodel A).

## K. Primitive c₀ projector

`Gate1B/SafeAlgebra/PrimitiveCharacterProjector.lean` — CONDITIONAL_FINITE.
`primitiveChar_sum_squarefree` : Möbius inversion (fully proved, via Mathlib's
`sum_eq_iff_sum_mul_moebius_eq`) of the primitive decomposition hypothesis
gives `∑_{χ prim mod c₀} χ(A) = ∑_{d ∣ c₀, d ∣ A−1} μ(c₀/d) φ(d)`. The
primitive decomposition itself is the explicit hypothesis `hdecomp` (Mathlib
lacks the conductor API); nothing is axiomatised.

## L. Mu projector simplification

`Gate1B/SafeAlgebra/PrimitiveProjectorMu.lean` — PROVED_ALGEBRAIC.

* `mu_mul_quotient_mu` : `μ(c₀) μ(c₀/d) = μ(d)` for squarefree `c₀`, `d ∣ c₀`;
* `mu_weighted_primitiveProjector` :
  `(μ(c₀)/c₀) ∑_{χ prim} χ(A) = (1/c₀) ∑_{d ∣ c₀, d ∣ A−1} μ(d) φ(d)`.

`Gate1B/SafeAlgebra/MuSpentByProjector.lean` — PROVED_ALGEBRAIC.

* `generic_common_divisor_eq_one`, `generic_filter_eq_singleton` : in the
  generic sector `gcd(c₀, A−1) = 1` only `d = 1` survives;
* `primitiveProjector_generic_eq_inv` : `(μ(c₀)/c₀) ∑_{χ prim} χ(A) = 1/c₀`.

FIREWALL: `μ(c₀)` disappears algebraically in the generic sector and must not
be re-counted as an independent sign.

## M. Dual determinant

`Gate1B/SafeAlgebra/H7DualCongruence.lean` — PROVED_FINITE:
`h7_dual_prime_congruence` : `p ∣ m − a c₀` and `p ∣ a c₀ e N − 2` give
`p ∣ m e N − 2` (plus the `ZMod` restatement).

`Gate1B/SafeAlgebra/H7DualDeterminant.lean` — PROVED_FINITE:
`pd_dvd_dualDet` (`IsCoprime`), the ℕ-form, and the shells
`h7_dualDet_shell`, `h7_dualDet_shell_of_congruences` :
`∃ ℓ', n N − p d ℓ' = 2` with `n = m e`.

## N. Self-duality anti-loop

`Gate1B/SafeAlgebra/H7SelfDuality.lean` — PROVED_FINITE:
with `d = c₀` and `c = p c₀`, `h7_fullDivisor_dualShell` gives
`∃ ℓ', n N − c ℓ' = 2`; reassociating `N = C₇ x`, `h7_selfDual_shellShape` and
`h7_fullDivisor_reconstructs_H7shape` give `C₇ x n − c ℓ' = 2`, the two-model
determinant shape of the original H7 packet. Anti-loop certificate; **no**
analytic equivalence of weights is claimed (countermodel D).

## O. Capacity power recovery

`Universal/SafeAlgebra/LargePrimeDivisorCount.lean` — PROVED_FINITE:
`largePrime_pow_card_le` (`V^{|s|} ≤ M`), `largePrime_card_lt` (contrapositive),
`largePrime_five_exceeds_nine` (exponent reading `9 < 5·vexp` for `vexp > 2`),
`largePrime_capacity_bound` (`M < V⁵ ⟹ #s < 5`). CAPACITY_ONLY as a Gate 1B
reading; no asymptotics.

`Universal/SafeAlgebra/DyadicHarmonic.lean` — PROVED_FINITE:
`dyadic_harmonic_le_two` (`∑_{S ≤ s ≤ 2S} 1/s ≤ 2`) and
`dyadic_totient_fibre_le` (`∑ φ(d)/(d s) ≤ 2 φ(d)/d`).

`Gate1B/SafeAlgebra/H7DualDetCapacity.lean` — CAPACITY_ONLY:
previous deficit `Q/Y⁴ = X^{ω − 4/9}` with `h7Deficit_at_13_18 = 5/18` and
`h7Deficit_at_8_9 = 4/9`, scale consistency `9(ω − 4/9) = 9ω − 4`, positivity of
the deficit for `ω > 4/9`; natural-scale capacity
`h7_dualDet_naturalScaleExponent` : `1 + 8 + 0 + 0 + 0 = 9`; and
`h7_fixedPower_deficit_recovered` : capacity − target `= 0`, together with
`h7_recovered_exponent_not_negative` : the recovered exponent is **not**
negative. Fixed positive-power deficit removed; nothing more.

## P. Analytic log-saving interface

`Gate1B/SafeExtensions/H7LogClosureFirewall.lean` — firewall
`no_log_saving_from_natural_scale` : a natural-scale bound `D ≤ S` is compatible
with the failure of any strictly smaller target `D ≤ tS` (`t < 1`). Hence
`Y⁹ X^{o(1)}` does **not** instantiate `Y⁹ log^{−A} X`.

`Gate1B/SafeExtensions/H7DualDetInterface.lean` — COMMENTS ONLY, zero
declarations: exact source of the `D₇(C)` coordinates (seven centered defect
coordinates + one model coordinate + dual `n`-coordinate + determinant
`n N − p d ℓ = 2`), status "fixed-power wall removed; arbitrary-log cancellation
open", label `H7-DUALDET-ONEDEFECT45`.

`Gate1B/SafeExtensions/V84ResourceLedger.lean` — COMMENTS ONLY: which resources
are spent (`μ(e)`, `μ(c₀)`, the prime character), which are untouched (`δ_i`),
and the double-counting rule.

`Gate1B/SafeExtensions/V84PrimeConductorInterfaces.lean` — COMMENTS ONLY:
RF1D low/medium, H7 arbitrary-log, H8, H9, same-`q`, D12, S2 Siegel–Walfisz,
`R_E`, Gate 1B closure — all OPEN and UNINHABITED.

## Q. Countermodels

`Gate1B/SafeAlgebra/CountermodelsV84.lean` — PROVED_FINITE:

* **A** `countermodelA_summable`, `countermodelA_support_infinite` — a rapidly
  decaying weight is summable yet nowhere zero: rapid decay ≠ compact support,
  so no single-frequency conclusion may be encoded;
* **B** `countermodelB_natural_scale_insufficient`,
  `countermodelB_exponent_zero` — a natural-scale bound does not imply a
  prescribed smaller target; exponent `0` is not exponent `−η`;
* **C** `countermodelC_mu_cancels`, `countermodelC_concrete` — a source sign can
  cancel inside a projector identity and so cannot be reused;
* **D** `countermodelD_shell_not_size`, `countermodelD_weights_unbounded` —
  shell reassociation alone implies no analytic bound.

## R. Axiom audit

`Gate1B/SafeExtensions/V84Status.lean` imports every v8.4 module and runs
`#print axioms` on all principal declarations. Every one reports only
`propext`, `Classical.choice`, `Quot.sound` (some fewer). No `sorry`, `admit`,
`axiom`, `opaque`, `native_decide` or `@[implemented_by]` occurs in any new
module.

## S. Gate 1B status

Gate 1B is **OPEN / UNCHANGED**. Nothing in v8.4 closes RF1D, H7, H8, H9,
same-`q`, D12, `R_E`, Full Type II or twin primes; the only movement is that the
fixed positive-power deficit of the H7 dual-determinant route is, at the level
of exponent bookkeeping, reduced to exponent `0` — explicitly *not* a log
saving.

---

## FINAL CLASSIFICATION

```
RF1D STATE COUNT:            PROVED_ALGEBRAIC (C·C·(Q/C) = Q·C, + firewall)
RF1D THRESHOLD:              CAPACITY_ONLY (transition C₀ = Q^{1/2}Y², margin Y^{-2η})
LANE E:                      PROVED_ALGEBRAIC + PROVED_FINITE (empty)
LANE C:                      PROVED_ALGEBRAIC (β(ce) = μ(e) ρ(c,e))
INDUCED GAUSS:               PROVED_ALGEBRAIC (Tier 2: CRT + Ramanujan hypotheses; twist derived)
MU(e) CANCELLATION:          PROVED_ALGEBRAIC (spent; not a remaining resource)
PRIME CRT CHARACTERS:        PROVED_ALGEBRAIC (cross factors derived)
PRIME CHARACTER COLLAPSE:    PROVED_ALGEBRAIC (Tier 1, concrete Dirichlet/gaussSum)
PRIME CORRECTION:            EXACT SEPARATE TERM (1/√p), no estimate
HYBRID h-POISSON:            residue part PROVED_ALGEBRAIC; compiler CONDITIONAL_FINITE
DUAL WINDOW UNIQUENESS:      PROVED_FINITE (truncated window only; tail ANALYTIC_INTERFACE_ONLY)
PRIMITIVE c0 PROJECTOR:      CONDITIONAL_FINITE (Möbius inversion proved)
MU(c0) PROJECTOR:            PROVED_ALGEBRAIC (generic sector = 1/c₀)
DUAL DETERMINANT:            PROVED_FINITE (p d ∣ nN − 2; shell nN − pdℓ' = 2)
H7 SELF-DUALITY:             PROVED_FINITE (anti-loop certificate)
LARGE PRIME DIVISOR CAPACITY:PROVED_FINITE + CAPACITY_ONLY reading
POWER RECOVERY:              CAPACITY_ONLY (exponent 0 at natural scale Y⁹)
ARBITRARY LOG H7:            OPEN / UNINHABITED
H8:                          OPEN
H9:                          OPEN
SAME-q:                      OPEN
D12:                         OPEN
R_E:                         SOURCE INTERFACE OPEN
GATE1B:                      OPEN
```

## FINAL VERDICT

```
ARISTOTLE_V8_4_GATE1B_PRIMECONDUCTOR_DUALDET_SAFE_BANK_PARTIAL

REGRESSION:            PASS
BUILD:                 PASS
SORRY:                 NONE
USER AXIOMS:           NONE
V8.1:                  PRESERVED
V8.2:                  PRESERVED
V8.3:                  PRESERVED
PRIME CHARACTER COLLAPSE: PROVED (Tier 1, concrete)
HYBRID POISSON:        RESIDUE PART PROVED / COMPILER CONDITIONAL
DUAL DETERMINANT:      PROVED (exact integer shell)
SELF-DUALITY FIREWALL: PROVED (anti-loop certificate + countermodel D)
POWER DEFICIT:         RECOVERED TO NATURAL SCALE
ARBITRARY LOG SAVING:  NOT FORMALISED / OPEN
ANALYTIC INTERFACES:   UNINHABITED
GATE1B:                OPEN / UNCHANGED
NEW REPORT:            UNIVERSAL_V8_4_GATE1B_PRIMECONDUCTOR_DUALDET_SAFE_BANK_REPORT.md
LEDGER:                APPENDED
```
