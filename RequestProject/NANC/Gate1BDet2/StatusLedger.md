# Gate 1B / determinant-2 bank — status and trust audit

Bank location: `RequestProject/NANC/Gate1BDet2/`, wired into
`RequestProject/NANCBank.lean`.  Namespace: `TwinPrimeProject.Gate1BDet2`.

Toolchain: Lean 4.28.0, mathlib v4.28.0
(`8f9d9cff6bd728b17a24e163c9402775d9e6a365`).

## Build / trust audit

* `lake build` completes with 0 errors and 0 warnings in the new files.
* Token scan of the whole bank: `sorry` 0, `admit` 0, `axiom` declarations 0
  (only `#print axioms` audit commands in `Main.lean`), `opaque` 0,
  `@[implemented_by]` 0.
* `#print axioms` is run in `Main.lean` on every banked theorem of Modules 1–9.
  Every one reports at most `propext`, `Classical.choice`, `Quot.sound`; several
  (e.g. `dvd_iff_exists_det2`, `det2_ell_unique`) depend on no axioms at all.
* The interface propositions of Module 9 are ordinary `Prop`-valued
  definitions.  They are never inhabited, and no theorem discharges them.

## PROVED / KERNEL-BANKED

| Item | Lean name | File |
| --- | --- | --- |
| Möbius prime-cofactor sign identity `μ d = −μ q` | `moebius_cofactor_of_prime_eq_neg` | `ModulusSignCollapse.lean` |
| Squarefree-support form `μ (q/p) = −μ q` | `moebius_div_prime_of_squarefree` | `ModulusSignCollapse.lean` |
| `λ_{D,P}(q) = −μ(q) L_{D,P}(q)` (finite weighted identity) | `lambdaCell_eq_neg_moebius_mul_LCell` | `ModulusSignCollapse.lean` |
| No same-`q` distinguished-`p` Möbius cancellation (constant sign, nonzero) | `admissible_moebius_constant`, `moebius_div_prime_ne_zero` | `ModulusSignCollapse.lean` |
| Congruence ↔ complementary-divisor identity | `dvd_iff_exists_det2`, `int_dvd_iff_exists_det2Int` | `ComplementaryDivisorDet2.lean` |
| Determinant-2 integer normal form `l q − u v = 2` | `det2_iff_int`, `det2Int_iff_neg`, `dvd_iff_exists_det2Int_nat` | `ComplementaryDivisorDet2.lean` |
| Uniqueness / positivity of the complementary divisor | `det2_ell_unique`, `det2_ell_eq_div`, `det2_ell_pos` | `ComplementaryDivisorDet2.lean` |
| Common divisor divides 2 (`ℕ` and `ℤ`) | `dvd_two_of_dvd_u_of_dvd_l`, `dvd_two_of_dvd_v_of_dvd_q`, `int_dvd_two_of_dvd_u_of_dvd_l`, `int_dvd_two_of_dvd_v_of_dvd_q` | `Det2Coprime.lean` |
| `gcd u l ∣ 2`, `gcd v q ∣ 2` | `gcd_u_l_dvd_two`, `gcd_v_q_dvd_two` | `Det2Coprime.lean` |
| Odd-sector coprimality | `coprime_u_l_of_odd`, `coprime_v_q_of_odd` | `Det2Coprime.lean` |
| Difference identity `u (v₂−v₁) = l (q₂−q₁)` | `det2_diff` | `Det2AffineLines.lean` |
| Exact affine-line parametrisation (iff form) | `det2_line_param_iff` | `Det2AffineLines.lean` |
| Existence and uniqueness of the affine parameter | `det2_exists_param`, `det2_param_unique` | `Det2AffineLines.lean` |
| Translation stability of the determinant-2 line | `det2_translate`, `det2_translate'` | `Det2AffineLines.lean` |
| Affine-form gcd divides 2; no shared odd prime | `affine_common_divisor_dvd_two`, `affine_gcd_dvd_two`, `no_common_odd_prime` | `Det2AffineCoprimality.lean` |
| Odd affine forms are coprime | `affine_coprime_of_odd`, `affine_coprime_of_odd_odd` | `Det2AffineCoprimality.lean` |
| Rational exponent ledger (`4/9 + 5/9 = 1`, `ω + (1−ω) = 1`, `13/18 − 4/9 = 5/18`) | `Uexp_add_Vexp`, `Qexp_add_Rexp`, `omegaHard_sub_Uexp` | `Gate1BExponentLedger.lean` |

### Audit answers requested in the task

1. **Is `Squarefree q` needed for `μ d = −μ q`?**  No.  `q = d p`, `p` prime and
   `Nat.Coprime d p` suffice: multiplicativity of `μ` on coprime arguments plus
   `μ p = −1`.  The banked lemma therefore carries the weaker hypotheses.
   Squarefreeness is used only in `coprime_div_prime_of_squarefree`, where the
   coprimality `Nat.Coprime (q/p) p` must be produced from `p ∣ q` alone; hence
   the cell identity `λ = −μ L` is stated on squarefree source support.
2. **Same-sign consequence.**  For fixed squarefree `q`, all admissible
   distinguished primes have `μ(q/p) = −μ(q)`, a nonzero unit sign.  No
   cancellation among distinguished `p`-representations of a single `q` is
   claimed anywhere.
3. **Oddness hypotheses.**  In `coprime_u_l_of_odd` the second oddness
   hypothesis (`Odd l`) is retained because the source statement carries it, but
   it is not load-bearing; the same for `Odd q` in `coprime_v_q_of_odd` and for
   `affine_coprime_of_odd_odd`.
4. **Positivity/range.**  All range restrictions are kept out of the algebraic
   theorems: the affine parametrisation is stated over `ℤ` with no positivity,
   and the `ℕ`-valued statements are separate.

## PROVED OPTIONAL ANALYTIC SKELETON (Phase B, completed)

| Item | Lean name | File |
| --- | --- | --- |
| Small-measure correlation lemma `‖∫_E A conj B‖ ≤ μ(E)·M_A·M_B` | `norm_setIntegral_mul_conj_le` | `SmallMeasureCorrelation.lean` |
| Chebyshev dyadic layer bound `μ(E_j(F)) ≤ 2^(−2j)` | `measure_ampLayer_le`, `measureReal_ampLayer_le` | `DyadicAmplitudeSeparation.lean` |
| Amplitude-unbalanced layer correlation `≤ 4·2^(−|j−k|)` | `layer_correlation_bound` | `DyadicAmplitudeSeparation.lean` |
| Scalar geometric tail `∑_{d≥L} 4·2^(−d) = 8·2^(−L)` | `geometric_tail` | `DyadicAmplitudeSeparation.lean` |
| Finite unbalanced-tail bound with explicit `C' = 4·|S|` | `layer_tail_bound` | `DyadicAmplitudeSeparation.lean` |

Correction recorded: the tail statement cannot be summed over *all* pairs
`(j,k)` with `|j−k| ≥ L` — that double sum diverges, since each difference class
is infinite.  The banked tail is therefore over a finite family of layer pairs,
with the explicit constant `4·|S|`, together with the separate scalar geometric
series identity.  No PMS45 claim follows from these lemmas.

## EXTERNAL ANALYTIC / OPEN (interfaces only, never inhabited)

* `ModulusFourierUniformity` — Davenport-type arbitrary-log Fourier uniformity;
* `NaturalMajorArcBound`;
* `PMS45Bound`;
* `OST45Bound`;
* Drappeau / Bettin–Chandee / Wright applications: not stated, not used.

## SOURCE OPEN (interfaces only, never inhabited)

* `SourceExpectedTermIdentified` — exact `E(q)` source formula / normalization
  dictionary not supplied;
* `FixedSwitchedPacketReassembled`;
* `GlobalGate0Exhaustive` — global direct/switched/skeleton exhaustiveness.

Deterministic implications proved (premises never discharged):

* `PMS45Bound + NaturalMajorArcBound → NaturalPhysical45Bound`
  (`naturalPhysical45_of_pms45_of_majorArc`);
* `NaturalPhysical45Bound + SourceExpectedTermIdentified +
  FixedSwitchedPacketReassembled → FixedSwitchedGate1BBound`
  (`fixedSwitchedGate1B_of_interfaces`).

## NOT PROVED

* `Gate1BClosed` — declared, uninhabited; the guard
  `gate1BClosed_needs_gate0` records that the fixed switched bound alone does
  not deliver closure (the Gate-0 exhaustiveness datum is missing).
* `FullTypeIIBound` — declared, uninhabited.
* `TwinPrimes` — declared, uninhabited.
* MAM45, PMS45, OST45, Davenport's Möbius exponential-sum theorem,
  Bettin–Chandee / Wright / Drappeau estimates: not attempted in this run.

---

# GATE 1B POST-MAM45 BANK EXTENSION (Modules 10–17)

New modules, all sorry-free, all built through
`RequestProject/NANC/Gate1BDet2/Main.lean` and hence through
`RequestProject/NANCBank.lean`:

* `DFBTAntiLoop.lean`
* `DFBTOffShell.lean`
* `DeltaExponentLedger.lean`
* `NearTopKloostermanLedger.lean`
* `PrimeCharacterReduction.lean`
* `KaratsubaExponentLedger.lean`
* `MobiusK2Dyadic.lean`
* `Gate1BMCInterfaces.lean`

## 1. Exact newly banked mathematics

| Item | Theorem | File |
|---|---|---|
| Gram invariant `Δ = x₁q₂ − x₂q₁`, on-shell factorisation `Δ = q₁q₂(ℓ₁−ℓ₂)` | `det2_gram_on_shell` | `DFBTAntiLoop.lean` |
| Coprime-factor cancellation in a congruence | `modEq_cancel_left_of_isCoprime` | `DFBTAntiLoop.lean` |
| Congruence lifting `Δ ≡ r q₁q₂ (mod c) ⟹ r ≡ ℓ₁−ℓ₂ (mod c)` | `dfbt_residue_congr_on_shell` | `DFBTAntiLoop.lean` |
| Integer rigidity: `r ≡ s (mod c)`, `c > 0`, `|r−s| < c` ⟹ `r = s` | `eq_of_modEq_of_abs_sub_lt` | `DFBTAntiLoop.lean` |
| Packaged on-shell anti-loop `r = ℓ₁ − ℓ₂` | `dfbt_coherence_on_shell_eq_complementary_shift` | `DFBTAntiLoop.lean` |
| The size hypothesis is load-bearing (explicit counterexample without it) | `dfbt_size_hypothesis_is_load_bearing` | `DFBTAntiLoop.lean` |
| Off-shell decomposition `Δ = q₁q₂(ℓ₁−ℓ₂) + η₁q₂ − η₂q₁` | `dfbt_gram_off_shell_decomposition` | `DFBTOffShell.lean` |
| Specialisation `η₁ = η₂ = 0 ⟹ Δ = q₁q₂(ℓ₁−ℓ₂)` | `dfbt_gram_off_shell_specialize` | `DFBTOffShell.lean` |
| The defect can be the only surviving contribution | `offshell_defect_can_be_nonzero` | `DFBTOffShell.lean` |
| `Uₑ + Vₑ = 1`, `Qₑ + Rₑ = 1` | `Delta.Ue_add_Ve`, `Delta.Qe_add_Re` | `DeltaExponentLedger.lean` |
| `1/9 ≤ Rₑ ≤ 5/18` on `13/18 ≤ ω ≤ 8/9` | `Delta.Re_mem_Icc` | `DeltaExponentLedger.lean` |
| `ω > 2/3`, hence `2Rₑ < Qₑ` (with converse) | `Delta.omega_gt_two_thirds`, `Delta.two_Re_lt_Qe`, `Delta.two_Re_lt_Qe_iff` | `DeltaExponentLedger.lean` |
| `Hₑ = Qₑ − Rₑ = 2ω − 1`; `Hₑ = 4/9` at `ω = 13/18` | `Delta.He_eq`, `Delta.He_at_omegaLow` | `DeltaExponentLedger.lean` |
| `Hₑ/Qₑ = 2 − 1/ω`; `= 8/13` at the binding endpoint | `Delta.He_div_Qe`, `Delta.He_div_Qe_at_omegaLow` | `DeltaExponentLedger.lean` |
| `t/3 − 1/5 = 8/39 − 1/5 = 1/195` at `t = 8/13` | `NearTop.bp_endpoint_one_over_195` | `NearTopKloostermanLedger.lean` |
| `t = Hₑ/Qₑ` at the binding endpoint | `NearTop.tEndpoint_eq_He_div_Qe` | `NearTopKloostermanLedger.lean` |
| Field identity `u v + 2 = u (v + 2u⁻¹)` for `u ≠ 0` | `PrimeChar.mul_add_two_eq` | `PrimeCharacterReduction.lean` |
| The shifted factor vanishes exactly when `uv+2 = 0` | `PrimeChar.shifted_factor_eq_zero_iff` | `PrimeCharacterReduction.lean` |
| Character rewrite `χ(uv+2) = χ(u)·χ(v + 2u⁻¹)` (`MulChar`, general field; `ZMod p` version) | `PrimeChar.mulChar_mul_add_two`, `PrimeChar.zmod_mulChar_mul_add_two` | `PrimeCharacterReduction.lean` |
| Injectivity of `u ↦ 2u⁻¹` on nonzero elements when `2 ≠ 0` (and for odd `p` in `ZMod p`) | `PrimeChar.two_inv_injOn`, `PrimeChar.zmod_two_inv_injOn` | `PrimeCharacterReduction.lean` |
| `Uc ≥ 1/2`, `Vc ≥ 5/8` on the window | `Karatsuba.half_le_Uc`, `Karatsuba.five_eighths_le_Vc` | `KaratsubaExponentLedger.lean` |
| `5/8 > 1/2 + 1/9 = 11/18` and `1/2 > 1/9` (window inside the numerical hypotheses) | `Karatsuba.window_inside_numerical_hypotheses` | `KaratsubaExponentLedger.lean` |
| `r = 10` exponents `−1/160`, `−37/160`; weaker saving `1/160 > 0` | `Karatsuba.karatsuba_r10_uniform_exponent_margin` | `KaratsubaExponentLedger.lean` |
| `h_y` vanishes on `n ≤ y`; `h_y*h_y*μ = μ − (μ_{≤y}+μ_{≤y}) + μ_{≤y}*μ_{≤y}*ζ` | `MobiusK2.hy_apply_eq_zero_of_le`, `MobiusK2.hy_sq_mul_moebius` | `MobiusK2Dyadic.lean` |
| Dyadic identity `μ(d) = −(μ_{≤y}*μ_{≤y}*ζ)(d)` for `y < D`, `y² ≥ 2D`, `D < d ≤ 2D` | `MobiusK2.moebius_dyadic_truncated` | `MobiusK2Dyadic.lean` |
| Same identity as an explicit finite divisor sum | `MobiusK2.moebius_dyadic_divisor_sum` | `MobiusK2Dyadic.lean` |
| The unsigned form of that identity is FALSE (`y=5, D=6, d=7`) | `MobiusK2.unsigned_dyadic_identity_false` | `MobiusK2Dyadic.lean` |

### Correction recorded (K2 Möbius identity)

The requested boxed identity was `μ(d) = (μ_{≤y} * μ_{≤y} * 1)(d)`.  That form
is **false**.  The derivation
`h_y^{*2} * μ = μ − 2μ_{≤y} + μ_{≤y}^{*2} * 1`, together with
`h_y^{*2}*μ(d) = 0` and `μ_{≤y}(d) = 0` on `D < d ≤ 2D`, gives
`0 = μ(d) + (μ_{≤y}^{*2} * 1)(d)`, i.e. the identity carries a **minus sign**:

  `μ(d) = − (μ_{≤y} * μ_{≤y} * 1)(d)`.

Concretely `(μ_{≤5} * μ_{≤5} * ζ)(7) = 1` while `μ(7) = −1`.  The signed
identity is proved; the unsigned one is refuted in Lean.

## 2. Interfaces (declared, never inhabited, never axioms)

`Gate1BMCInterfaces.lean` (namespace `TwinPrimeProject.Gate1BDet2.MC`):
`CorrectDeltaCharacterNormalization`, `LowCleanDeltaBlocksClosed`,
`MiddleCleanDeltaBlocksClosed`, `NearTopMC45Bound`,
`PrimeCharacterKaratsubaInput`, `PrimeMC45CovarianceTransfer`,
`NearPrimeCompositeTransfer`, `GeneralCompositeMC45Transfer`,
`NearTopZeroDualIdentified`, `SourceExpectedTermIdentified`,
`Kappa4NormalizationMatched`, `FixedSwitchedPacketReassembled`,
`Gate1BAnalyticCoreClosed`, `Gate1BClosed`, plus the *missing datum*
`PrimeCovarianceCompatibility`.

Deterministic implications proved (premises never discharged):

* `NearTopMC45Bound + LowCleanDeltaBlocksClosed + MiddleCleanDeltaBlocksClosed +
  CorrectDeltaCharacterNormalization → Gate1BAnalyticCoreClosed`
  (`MC.gate1BAnalyticCoreClosed_of_interfaces`, with the exact split as an
  explicit hypothesis);
* `Gate1BAnalyticCoreClosed + NearTopZeroDualIdentified +
  SourceExpectedTermIdentified + Kappa4NormalizationMatched +
  FixedSwitchedPacketReassembled → Gate1BClosed`
  (`MC.gate1BClosed_of_interfaces`);
* `PrimeCharacterKaratsubaInput + PrimeCovarianceCompatibility →
  PrimeMC45CovarianceTransfer`
  (`MC.primeMC45CovarianceTransfer_of_input_of_compatibility`).

**Not proved, deliberately:** `PrimeCharacterKaratsubaInput →
PrimeMC45CovarianceTransfer`.  A pointwise prime-character estimate is not by
itself the mixed `(c, χ)`-covariance; `MC.covariance_not_implied_by_pointwise`
exhibits data satisfying the pointwise interface and violating the covariance
target.

## 3. Analytic claims deliberately NOT formalized

* Heath–Brown / DFI delta symbol and any delta-block estimate; the label
  `C_e = Q_e = ω` is a **rational label only** (`Delta.Ce`).
* Bettin–Chandee, Blomer–Pascadi all-modulus bilinear Kloosterman bounds
  (including any `c^{-1/32}`-type saving), MQW, Wright: not imported, not
  assumed, not axiomatised.  Only the exponent arithmetic `8/39 − 1/5 = 1/195`
  is banked, and it says nothing about applicability; the source's joint
  `h(uv+2)` argument and the coefficient-class matching remain external.
* Karatsuba / FSX Appendix-A bilinear character-sum theorem: external.  Only
  the rational exponent margins are banked; `PrimeMC45Closed` is **not**
  stated.
* Multiplicative large sieve, Pólya–Vinogradov, Poisson estimates, MC45,
  source `E(q)`, Gate 1B closure.
* Full Type II and twin primes: not stated in the new modules.

## 4. Status labels

```text
DFBT_ON_SHELL_ANTI_LOOP:              PROVED
DFBT_OFF_SHELL_DECOMPOSITION:         PROVED
FULL_DFBT_ANALYTIC_EQUIVALENCE:       NOT CLAIMED
DELTA_EXPONENT_LEDGER:                PROVED
C_EQUALS_Q:                           WORKING ANALYTIC CHOICE / NOT A LEAN ANALYTIC THEOREM
NEAR_TOP_H_EXPONENT:                  PROVED
BP_ENDPOINT_1_OVER_195_ARITHMETIC:    PROVED
PRIME_CHARACTER_ALGEBRAIC_REWRITE:    PROVED (field identity + MulChar rewrite + injectivity)
KARATSUBA_R10_EXPONENT_MARGIN:        PROVED RATIONALLY
KARATSUBA_ANALYTIC_THEOREM:           EXTERNAL / NOT FORMALIZED
PRIME_MC45_COVARIANCE:                OPEN
COMPOSITE_MC45_TRANSFER:              OPEN
K2_MOBIUS_DYADIC_IDENTITY:            PROVED, WITH SIGN CORRECTION
                                      (unsigned form refuted; explicit finite
                                       divisor-sum form also banked)
SOURCE_E(q):                          OPEN
GATE_1B:                              OPEN
FULL_TYPE_II:                         NOT CLAIMED
TWIN_PRIMES:                          NOT CLAIMED
```

## 5. Trust audit (new modules)

`sorry` 0, `admit` 0, user `axiom` 0, `opaque` 0, `@[implemented_by]` 0.
`#print axioms` is run in `Main.lean` on every principal theorem of Modules
10–17; each reports at most `propext`, `Classical.choice`, `Quot.sound`.

---

# Extension III — on-shell pair surface / common-shift rigidity / split ledger

Eleven new sorry-free modules (Modules 19–29), all imported through
`RequestProject/NANC/Gate1BDet2/Main.lean` and hence through
`RequestProject/NANCBank.lean`.  Nothing pre-existing was reproved or replaced:
the determinant predicate `OnDet2Line` (Module 4), the translation-stability
lemma `det2_translate'`, the congruence-cancellation lemma
`modEq_cancel_left_of_isCoprime` and the integer rigidity lemma
`eq_of_modEq_of_abs_sub_lt` (Module 10) are reused.

## A. Files created

| file | content |
|---|---|
| `PrimitiveDet2PairSurface.lean` | pair determinant, shift identity, `= 2h` on shell, converse, translation stability |
| `CommonShiftGCD.lean` | `gcd(ℓh, uh) = h` over `ℕ` and `ℤ`; forward pair-surface package |
| `PrimitiveDet2PairConverse.lean` | converse by cancellation of `h`; normalisation; uniqueness of the primitive normal form; packaged equivalence |
| `CommonShiftRigidity.lean` | divisibility and residue rigidity in both directions; short-interval uniqueness; finite residue-class interval count |
| `CommonShiftSchur.lean` | abstract finite bipartite Schur/Cauchy bound (squared and square-root forms) |
| `SplitSchurExponentLedger.lean` | `k = 0,1,2` rational ledger; complementary-modulus ratios; Schur endpoint losses |
| `SequentialDeficitLedger.lean` | `(1/2)(3·5/18 − 13/18) = 1/18`; `1/12 − 1/36 = 1/18`; guards |
| `PascadiGroupingLedger.lean` | rational no-go for the three `k = 1` four-prime groupings |
| `Det2Unipotent.lean` | `2 × 2` unipotent matrix algebra and determinant preservation |
| `JointFourierInterfaces.lean` | uninhabited joint-Fourier interfaces; tautological transfers only |
| `Gate1BOnShellInterfaces.lean` | on-shell interface layer; the one valid closure package; guards |

## B. Pair-surface package (exact)

* `pair_det_shift_identity` : `v₂z₁ − v₁z₂ = h(ℓz₁ − uv₁)` for
  `v₂ = v₁ + ℓh`, `z₂ = z₁ + uh` — no hypotheses.
* `pair_det_eq_two_mul_shift` : on the shell `ℓz₁ − uv₁ = 2`, the pair
  determinant is `2h`.
* `primitive_det2_pair_surface_converse` / `onDet2Line_of_pair_det_eq_two_mul_shift` :
  for `h ≠ 0` (resp. `h > 0`), `v₂z₁ − v₁z₂ = 2h` forces `ℓz₁ − uv₁ = 2`.
* `gcd_shift_pair_eq_h`, `int_gcd_shift_pair_eq_h`, `shift_parameter_eq_gcd_of_increments` :
  `gcd(Δv, Δz) = h` under `gcd(u, ℓ) = 1`.
* `primitive_det2_pair_surface_forward`, `primitive_det2_pair_surface` : the two
  conclusions simultaneously; `primitive_shift_normal_form_unique` : the
  increments determine `(u, ℓ, h)` uniquely in the primitive normal form.
* `det2_form_translation_invariant`, `det2_shell_translate` : translation
  stability (the shell case delegates to `det2_translate'` of Module 4).

## C. Common-shift rigidity (what is finite, what stays asymptotic)

Finite/combinatorial and proved: `u_dvd_z_shift`, `ell_dvd_v_shift`,
`ell_mul_z_mod_u_eq_two`, `u_mul_v_mod_ell_eq_neg_two`,
`ell_congr_mod_u_of_isCoprime`, `u_congr_mod_ell_of_isCoprime`,
`ell_unique_in_short_interval`, `det2_ell_unique_in_short_interval`,
`card_le_of_residue_class_in_interval` (`|S| ≤ (b−a)/m + 1` for a set in one
residue class inside `[a,b]`, `a ≤ b`, `m > 0`) and its `Finset.filter` form.

Deliberately **not** formalized: any `X^{o(1)}` statement, the asymptotic form
`O(U/ℓ + 1)`, and the ratio `U/R = X^{1/6}` (which belongs to the exponent
ledger, not here).  The degree bounds required by the Schur estimate are inputs
to `bipartite_schur_bound`, not consequences of it.

## D. Split exponent ledger (`ω = 13/18`, `Rₑ = 5/18`)

| k | `x_k` | `s_k` | `H_k = ω − x_k` | `Rₑ/s_k` | `δ_k = (x_k − Rₑ)/2` |
|---|---|---|---|---|---|
| 0 | 4/9 | 5/9 | 5/18 | 1/2 | 1/12 |
| 1 | 5/9 | 4/9 | 1/6  | 5/8 | 5/36 |
| 2 | 2/3 | 1/3 | 1/18 | 5/6 | 7/36 |

`k0_minimizes_schur_endpoint_loss` : `δ₀ < δ₁ < δ₂`.  **This is not an intrinsic
Gate-1B power deficit**; it is a rational exponent ledger for the
coefficient-blind common-shift Schur method only.

## E. Pascadi `k = 1` grouping no-go (which inequality kills each grouping)

Skeleton: `M ≤ Rmod`, `Rmod ≤ N + L − ε`, `N + L ≤ 2/3 − ε`, `L ≤ M − ε`.

* Grouping A (`M = 1/2`, `N = L = 1/4`): the range pair `M ≤ Rmod ≤ N+L−ε`
  demands `1/2 ≤ Rmod ≤ 1/2 − ε`.
* Grouping B (`N = 1/2`, `M = L = 1/4`): `N + L = 3/4 > 2/3`, margin `1/12`.
* Grouping C (`L = 1/2`, `M = N = 1/4`): `L ≤ M − ε` fails since `1/2 > 1/4`.

`no_four_prime_grouping_satisfies_prop63_exponent_skeleton` packages the three.
Pascadi's analytic proposition is **external**, is not formalized, and is not
contradicted by this no-go, which concerns only the attempted dictionary.

## F. Unipotent bank

`det_pairMatrix` : `det !![z,u;v,ℓ] = zℓ − uv`; `det_unipotent = 1`;
`det2_right_unipotent_action` : `!![z,u;v,ℓ]·!![1,0;h,1] = !![z+uh,u;v+ℓh,ℓ]`;
`det2_preserved_by_right_unipotent`, `det_eq_two_preserved`, and the bridge
`onDet2Line_iff_det_pairMatrix`.

## G. Interfaces deliberately left unproved

`JF.JointFourierProducesNewOrthogonality`,
`JF.DeterminantConditionedGeneralizedVonNeumann`,
`JF.DeterminantWeightedSpectralInequality`, `JF.QuotientWeightSpectrallySeparated`,
`JF.TwoSequenceKloostermanManufactured`, `JF.OnShellMixedFourthMomentBound`,
`JF.PreCauchyP45Bound`, `JF.JointFourierAntiLoopDiagnosed`;
`OnShell.CommonShiftGraphControlled`, `OnShell.BetaU2ProjectorStable`,
`OnShell.FivePrimeBetaJointMoment`, `OnShell.PascadiQuotientInterface`,
`OnShell.DeterminantConditionedU1Plus`,
`OnShell.AutomorphicSourceWeightCompatible`,
`OnShell.SourceExpectedTermIdentified`, `OnShell.Kappa4NormalizationMatched`,
`OnShell.FixedSwitchedPacketReassembled`, `OnShell.OnShellAnalyticCoreClosed`,
`OnShell.Gate1BClosed`.

Not proved on purpose:
`ExactJointFourierRepresentation → JointFourierProducesNewOrthogonality`
(guard `orthogonality_not_implied_by_representation`);
`PrimitivePairSurfaceBanked → OnShellAnalyticCoreClosed`
(guard `pairSurface_does_not_close_core`);
`CommonShiftGraphControlled → OnShellAnalyticCoreClosed`
(guard `graphControl_does_not_close_core`); `BetaU2ProjectorStable`.

Only valid package: `OnShellAnalyticCoreClosed + SourceExpectedTermIdentified +
Kappa4NormalizationMatched + FixedSwitchedPacketReassembled → Gate1BClosed`
(`gate1BClosed_of_onShell_interfaces`, a triangle inequality).

## H. Literature interface ledger (prose only, no Lean theorems)

* **Blomer–Pascadi** — published/external bilinear Kloosterman technology.
  Status here: `GENUINE TWO-SEQUENCE KERNEL REQUIRED FIRST`.
* **Pascadi Proposition 6.3** — external analytic theorem.  Our direct `k = 1`
  four-prime exponent dictionary: `RATIONAL RANGE MATCH: FAILED FOR ALL THREE
  GROUPINGS`.  This does not preclude a proof-level adaptation.
* **Grimmelt–Teräväinen generalized von Neumann** — external analytic theorem.
  `COMMON-BASE LINEAR FORMS: KNOWN THEOREM`;
  `OUR DETERMINANT-DEPENDENT UNEQUAL INTERCEPTS: NOT DIRECTLY MATCHED`.  The
  mismatch is **not** formalized as a theorem (the definitions needed to state
  it exactly are not locally formalized).
* **Determinant/Poincaré spectral route** — only the exact unipotent matrix
  algebra is banked.  The claim that the source weight fails automorphic
  invariance remains an analytic/interface audit, not a Lean theorem.

## I. Extension-III status labels

```text
PRIMITIVE_DET2_PAIR_SHIFT_IDENTITY:      PROVED
PAIR_DETERMINANT_EQUALS_2H:              PROVED
COMMON_SHIFT_GCD_RECOVERY:               PROVED
PRIMITIVE_DET2_PAIR_SURFACE_FORWARD:     PROVED
PRIMITIVE_DET2_PAIR_SURFACE_CONVERSE:    PROVED
FIXED_BETA_PAIR_DIVISIBILITY_RIGIDITY:   PROVED
FIXED_B_PAIR_DIVISIBILITY_RIGIDITY:      PROVED
SHORT_INTERVAL_RESIDUE_UNIQUENESS:       PROVED
FINITE_RESIDUE_CLASS_INTERVAL_COUNT:     PROVED (hypotheses m > 0, a ≤ b)
ABSTRACT_BIPARTITE_SCHUR:                PROVED (squared and sqrt forms)
K_SPLIT_ENDPOINT_LEDGER:                 PROVED
SCHUR_METHOD_ENDPOINT_LOSSES:            k=0 : 1/12, k=1 : 5/36, k=2 : 7/36
K0_SCHUR_OPTIMAL_AMONG_012:              PROVED RATIONALLY
SEQUENTIAL_X_ONE_OVER_18:                PROVED RATIONALLY / METHOD-SPECIFIC ONLY
PASCADI_K1_PROP63_GROUPING_NO_GO:        PROVED RATIONALLY
PASCADI_ANALYTIC_THEOREM:                EXTERNAL
DET2_RIGHT_UNIPOTENT_ACTION:             PROVED
JOINT_FOURIER_ANALYTIC_IDENTITY:         INTERFACE ONLY (not formalized)
DETERMINANT_CONDITIONED_U1PLUS:          OPEN INTERFACE
AUTOMORPHIC_SOURCE_WEIGHT_COMPATIBILITY: OPEN INTERFACE
ON_SHELL_MIXED_FOURTH_MOMENT:            OPEN
PRE_CAUCHY_P45:                          OPEN
SOURCE_E(q):                             OPEN
GATE_1B:                                 OPEN
GATE_1A:                                 SEPARATE
GATE_0:                                  SEPARATE
FULL_TYPE_II:                            NOT CLAIMED
TWIN_PRIMES:                             NOT CLAIMED
```

## J. Retraction guards

* **Guard A.**  Do not state "Gate 1B intrinsically loses `X^{1/18}`".  Correct:
  Gate 1B is power-critical; `X^{1/18}` is method-specific (docstrings of
  `SequentialDeficitLedger`, `one_over_18_is_a_ledger_value`).
* **Guard B.**  Do not multiply an `X^{-1/36}` five-prime fourth-moment saving
  with the Schur `X^{1/12}` loss: no independence theorem is proved.  Only the
  rational identity `1/12 − 1/36 = 1/18` is banked
  (`stacking_is_not_implied_by_the_identity`).
* **Guard C.**  Do not claim "Pascadi 5/8 applies because ℓ = s^{5/8}": the
  direct Proposition-6.3 grouping audit fails (Module 26).
* **Guard D.**  The primitive pair-surface normal form is an exact structural
  coordinate, not analytic progress toward closure
  (`pairSurface_does_not_close_core`).

## K. Trust audit (Extension III)

```text
lake build:            passes (0 errors)
warnings in new files: 0
sorry:                 0
admit:                 0
user axioms:           0
opaque:                0
implemented_by:        0
```

`#print axioms` is run in `Main.lean` on every principal theorem of Modules
19–29; each reports at most `propext`, `Classical.choice`, `Quot.sound`.

Final status: NEW ALGEBRAIC/COMBINATORIAL BANK: COMPLETE.
ON-SHELL ANALYTIC CORE: OPEN.  SOURCE ZERO MODE: OPEN.  GATE 1B: OPEN.

---

# NANC BANK EXTENSION IV — Gate 1B: reciprocal frame / fixed-cell convolution / composite view / source boundary

Modules 30–40 plus optional Phase B.  **Nothing from Modules 1–29 was reproved,
renamed, replaced, weakened or duplicated.**  No new analytic Gate-1B closure
theorem is formalized: the Band-II / Band-III master bound remains under
hostile analytic audit, and `BandIIClosed`, `LowerBandIIIClosed`,
`UpperBandIIIClosed`, `UpperBandResidualBound`, `CompositeViewSquareRootGain`,
`Gate1BAnalyticCoreClosed`, `Gate1BClosed` (and the rest) are ordinary
uninhabited `Prop` interfaces.

## A. Files created

| Module | File |
|---|---|
| 30 | `Det2AdditiveReciprocalFrame.lean` |
| 31 | `Det2Reciprocity.lean` |
| 32 | `FiniteReciprocalFourierOperator.lean` |
| 33 | `FixedCellBetaTwistRecombination.lean` |
| 34 | `CompositeViewDet2.lean` |
| 35 | `CompositeViewMultiplicity.lean` |
| 36 | `ProjectiveThirdCoordinateRigidity.lean` |
| 37 | `FullFaceFixedPacket.lean` |
| 38 | `FullDivisorBoundaryAlgebra.lean` |
| 39 | `SpectatorNonTensorizationGuard.lean` |
| 40 | `Gate1BUpperBandInterfaces.lean` |
| Phase B | `SteinbergJetFinite.lean` |

All are imported through `Main.lean`, hence through `RequestProject/NANCBank.lean`.

## B. BANKED EXACT (Modules 30–39, all sorry-free)

**Module 30 — additive reciprocal frame.**
`addPhase` (the standard additive character of `ZMod q`), finite orthogonality
`sum_addPhase_mul : ∑_h e_q(h t) = if t = 0 then q else 0` (proved from
primitivity), and the exact indicator identity
`det2_additive_frame : 1_{u v = −2} = q⁻¹ ∑_h e_q(h v + 2 h u⁻¹)` for `u` a unit.
The zero mode is separated (`addPhase_zero_mode`, `sum_addPhase_split`) and
`addPhase_det2_split` records the sign-correct factorisation.
**Guards:** `additive_zero_mode_does_not_identify_source_expected_term` (the
`h = 0` mode is the constant `q⁻¹` for all data, hence carries no source
information) and `zero_mode_ne_indicator` (a concrete `q = 5` separation).

**Module 31 — reciprocity.**
Integer layer `reciprocity_dvd : u q ∣ u ū + q q̄ − 1` (equivalently
`ū/q + q̄/u − 1/(u q) ∈ ℤ`) with witnessed form `reciprocity_witness`.
Analytic translation with `phase x = exp(2π i x)`: `phase_add`, `phase_int_add`
(1-periodicity), `phase_det2_split`, and
`det2_reciprocity_phase : e(2hū/q) = e(−2h q̄/u) · e(2h/(u q))`.
No range or saving claim.

**Module 32 — finite reciprocal Fourier operator.**
`fourierKernel m c x y = e_m(c x y)`; Gram relation `gram_sum` and
`gram_kernel_entry`; block support `dvd_mul_iff_div_gcd_dvd`,
`gram_support_int_iff`, `nat_dvd_mul_iff_div_gcd_dvd` (support exactly
`x ≡ x' mod m/g`); block size `card_multiples_range`, `card_mul_kernel`
(kernel of multiplication by `c` has exactly `g = gcd(c,m)` elements); row sum
`gram_row_sum = m g`; coprime case `gram_coprime`,
`normalized_kernel_unitary_rows`.
**Interface:** `ReciprocalOperatorNormIdentity` (`‖F‖ = √(m g)`) is *not*
inhabited (`reciprocalOperatorNormIdentity_not_automatic`).

**Module 33 — fixed-cell β twist recombination.**
`qSupport`, `betaCell`, and the exact twisted convolution identity
`fixed_cell_recombination`, plus the `μ` / abstract-prime-weight specialisation
`fixed_cell_recombination_moebius_prime`.  The twist is an abstract
multiplicative `tau : ℕ → R`; no `Real.log`, no characters, no Mellin, no
hybrid large sieve.
**Guard:** `fixed_cell_recombination_does_not_imply_full_face_recombination`
(the same `q` receives `β(2) = 1` in one cell and `β(2) = 2` in a larger one).

**Module 34 — composite-view geometry.**
`CompositeDet2 q l u rho s : q l − u ρ s = 2`; `composite_view_mod_u`,
`composite_view_mod_s`, CRT combination `det2_composite_view_mod_us`; interval
uniqueness `composite_view_l_unique_in_short_interval` and
`composite_det2_l_unique_in_short_interval` (the rigidity step is Module 22's
`ell_unique_in_short_interval`, **reused, not reproved**); reconstruction
`composite_view_rho_exists`, `composite_view_rho_unique`,
`composite_view_reconstructs_l_rho`.  No square-root gain claimed.

**Module 35 — composite-view multiplicity.**
`composite_view_at_most_one_l`, `composite_view_at_most_one_l_rho`,
`composite_view_multiplicity_le` (`≤ Mfact` for `(l, ρ, d, p)` representations)
and `composite_view_multiplicity_one`.  `Mfact` stays an abstract natural
number: **no `X^{o(1)}` substitution is made inside Lean.**

**Module 36 — projective third-coordinate rigidity.**
`ProjectivelyEq3`; `two_ne_zero_of_odd`; `projective_scalar_eq_one` (the
projective scalar is forced to be `1` — nonvanishing of the scalar turned out
*not* to be needed and was therefore dropped from that lemma);
`projective_third_coordinate_rigidity`; determinant specialisation
`det2_projective_collision_rigidity` (`A = pSource·l`, `B = −u`).
**Guard:** `projective_collision_rigidity_does_not_imply_operator_saving`.

**Module 37 — full-face fixed packet.**
`LRouted`, `lambdaRouted`, sign collapse
`lambdaRouted_eq_neg_moebius_mul_LRouted` (reusing Module 1's cofactor
identity), partition-of-unity recombination
`sum_lambdaRouted_eq_lambdaRouted_switched` and
`sum_lambdaRouted_eq_neg_moebius_mul_LSwitched`.
`L_sw(q) = log q` is **not** proved.
**Interface:** `SourceFaceCompleteness`, never inhabited.
**Guard:** `fixed_switched_recombination_does_not_imply_full_face_completeness`.

**Module 38 — full divisor-boundary algebra.**
Derivation identity `log_deriv : (f*g)·log = (f·log)*g + f*(g·log)`, abstract
additive-weight version `additive_weight_deriv` (arbitrary commutative ring, no
`Real.log`), and the classical identities `moebius_pmul_log : μ·log = −(μ*Λ)`,
`moebius_mul_vonMangoldt_apply : (μ*Λ)(n) = −μ(n) log n`, and
`zeta_mul_moebius_mul_vonMangoldt : ζ*(μ*Λ) = Λ`.  *Convention note:* Mathlib's
`1` in `ArithmeticFunction` is the delta function, so the requested
`1 * (μ*Λ) = Λ` is banked with the constant-one function `ζ`.
**Interfaces:** `SourceExpectedTermIdentified`, `SourceZeroModeReconciled`,
`Gate1BPacketClosed` — none inhabited.
**Guard:** `divisor_boundary_identity_does_not_imply_packet_closure`.

**Module 39 — spectator non-tensorization guard.**
`identical_view_operators_do_not_compound` (an idempotent view with contraction
factor `c` composes to factor `c`, and `c = c²` forces `c ∈ {0,1}`) and the
explicit finite-dimensional countermodel
`factor_count_does_not_imply_independent_operator_gain` (two identical
projections on the same latent coordinate, each contracting `nsq` by `1/2`,
composition still `1/2`, not `1/4`), plus
`composition_gain_is_not_the_product_of_gains`.

**Optional Phase B — finite Steinberg jet.**
`jetCoeff`, `jetCoeff_one` (top alternating tensor `(−1)^{|T|}`),
`jet_first_variation` (algebraic first variation in one leg),
`jet_sum_first_variation` (one differentiated leg tensored with the remaining
alternating legs).  Explanatory only.

## C. INTERFACES (declared, never inhabited, no axioms)

`ReciprocalOperatorNormIdentity`; `SpectatorOperatorSaving`;
`SourceFaceCompleteness` (Modules 37 and 40);
`SourceExpectedTermIdentified`, `SourceZeroModeReconciled`,
`Gate1BPacketClosed` (Module 38);
and in Module 40: `ReciprocalMasterBound`, `BandIIClosed`,
`LowerBandIIIClosed`, `UpperBandResidualBound`,
`TwoPrimeCompositeViewExtracted`, `FourPrimeCompositeViewExtracted`,
`CompositeViewSquareRootGain`, `UpperBandIIIClosed`,
`FixedSwitchedPacketReassembled`, `Gate1BAnalyticCoreClosed`, `Gate1BClosed`.

Only two deterministic chains are proved, both plain triangle inequalities:

```
BandIIClosed ∧ LowerBandIIIClosed ∧ UpperBandIIIClosed → Gate1BAnalyticCoreClosed
Gate1BAnalyticCoreClosed ∧ SourceExpectedTermIdentified
    ∧ FixedSwitchedPacketReassembled → Gate1BClosed
```

Separating guards: `compositeViewGeometry_does_not_imply_squareRootGain`,
`projectiveRigidity_does_not_imply_upperBandIIIClosed`,
`reciprocalMasterBound_not_automatic`.

## D. NOT BANKED

Band II analytic closure; lower Band III analytic closure; upper Band III;
spectator / composite-view square-root gain; the reciprocal master bound;
source face completeness; source expected term / zero-mode reconciliation;
Gate 1B closure; full Type II; twin primes.

## E. Requested statements found false or needing correction

* None of the requested Extension-IV statements was found false.
* Two *convention* corrections were required and are documented in the
  affected files: (i) Mathlib's `1 : ArithmeticFunction` is the delta function,
  so `1 * (μ*Λ) = Λ` is banked as `ζ * (μ*Λ) = Λ`; (ii) in Module 36 the
  hypothesis `a ≠ 0` on the projective scalar is unnecessary (the third
  coordinate forces `a = 1`), so it was dropped rather than carried unused.

## F. Trust audit (Extension IV)

```text
lake build:            passes (0 errors, 8281 jobs)
warnings in new files: 0
sorry:                 0
admit:                 0
user axioms:           0
opaque:                0
implemented_by:        0
```

`#print axioms` is run in `Main.lean` on every principal theorem of Modules
30–40 and Phase B; each reports at most `propext`, `Classical.choice`,
`Quot.sound`.

## G. Final statuses (Extension IV)

```text
RECIPROCAL EXACT BANK:            BANKED EXACT (Modules 30–32)
FIXED-CELL BETA RECOMBINATION:    BANKED EXACT (Module 33)
COMPOSITE VIEW GEOMETRY:          BANKED EXACT (Modules 34–35)
PROJECTIVE RIGIDITY:              BANKED EXACT (Module 36)
FULL-FACE FIXED PACKET:           BANKED EXACT (Module 37)
SOURCE FACE COMPLETENESS:         OPEN INTERFACE
MASTER ANALYTIC BOUND:            OPEN (under hostile audit)
BAND II:                          OPEN
LOWER BAND III:                   OPEN
UPPER BAND III:                   OPEN
SOURCE ZERO MODE:                 OPEN INTERFACE
GATE 1B:                          OPEN
FULL TYPE II:                     NOT CLAIMED
TWIN PRIMES:                      NOT CLAIMED
```
