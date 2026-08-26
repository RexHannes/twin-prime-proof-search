# HPoissonComplementaryDivisor — Status Ledger

Bank: `RequestProject/NANC/HPoissonComplementaryDivisor/`
Scope: **finite arithmetic only** for the switched `r = 9`, `4|5` h-Poisson bridge.
Lean 4.28.0, Mathlib `v4.28.0` (`8f9d9cff6bd728b17a24e163c9402775d9e6a365`).

Parameters (exponent bookkeeping only):
`U = X^{4/9}`, `V = X^{5/9}`, `Q = X^{13/18}`, `H₀ = X`.

---

## FILES

| File | Content |
|---|---|
| `CRTPhase.lean` | CRT existence/uniqueness, units and inverses, additive inverse phase identity |
| `PoissonCongruenceCore.lean` | post-Poisson congruence reindexing (Poisson itself **not** asserted) |
| `ComplementaryDivisor.lean` | `q ∣ yv − 2 ↔ ∃ ℓ, yv − qℓ = 2`, uniqueness, modulus factorization |
| `ExponentGeometry.lean` | exact `ℚ` exponent identities and corrected dyadic `L_ℓ` geometry |
| `CenteringCore.lean` | centered divisor indicator `ρ_q`, CRT expansion, four separated centering operations |
| `ConditionalExponentLedger.lean` | never-inhabited analytic predicates, conditional target-exponent arithmetic, repair guards |
| `Main.lean` | aggregation + `#print axioms` audit |
| `StatusLedger.md` | this file |

Wired into `RequestProject/NANCBank.lean`.

---

## PROVED FINITE (Lean, sorry-free)

### CRT inverse phase core (`CRTPhase.lean`)
- `crt_exists`, `crt_unique`, `crt_existsUnique_mod` — existence and uniqueness of `w mod q₁q₂`
  under `IsCoprime (q₁ : ℤ) q₂`.
- `isCoprime_of_congr`, `crt_isCoprime_mul` — a CRT solution `w` is a unit mod `c = q₁q₂`
  when `v₁, v₂` are units mod `q₁, q₂`.
- `exists_inv_of_isCoprime`, `inv_unique`, `inv_congr_of_congr`, `inv_congr_inv` —
  `w ≡ v_i (mod q_i)` implies `w̄ ≡ v̄_i (mod q_i)`.
- `crt_inverse_decomposition` — integer form:
  `w̄ ≡ a₁b₂q₂ + a₂b₁q₁ (mod q₁q₂)` with `a_i v_i ≡ 1`, `q₂b₂ ≡ 1 (mod q₁)`, `q₁b₁ ≡ 1 (mod q₂)`.
- `crt_phase_identity` — rational form: `(−2h w̄)/(q₁q₂) − ((−2h a₁b₂)/q₁ + (−2h a₂b₁)/q₂) ∈ ℤ`,
  i.e. the additive phase identity mod 1. **Not** extended to `(q₁,q₂) > 1`.

### Poisson congruence reindexing core (`PoissonCongruenceCore.lean`)
- `residue_iff_mul` — `y ≡ 2w̄ (mod c) ↔ yw ≡ 2 (mod c)`.
- `crt_split_two` — `yw ≡ 2 (mod q₁q₂) ↔ q₁ ∣ yv₁ − 2 ∧ q₂ ∣ yv₂ − 2`.
- `residue_iff_split` — combined form.
- `residueClassEquiv`, `shift_injective`, `shift_surjective` — `n ↦ nc + 2w̄` is a bijection
  from `ℤ` onto the residue class `{ y : y ≡ 2w̄ (mod c) }`, for `c ≠ 0`.

### Complementary-divisor bijection (`ComplementaryDivisor.lean`)
- `dvd_iff_exists_ell`, `ell_unique`, `ell_eq_div`, `existsUnique_ell`.
- `ell_can_be_negative`, `ell_can_be_zero` — negative `y` and negative/zero `ℓ` occur;
  `ℓ > 0` is never assumed.
- `subst_factor`, `subst_factor'`, `dvd_iff_exists_ell_factored` — modulus factorization `q = dp`.
- `residue_iff_two_ell` — link to the CRT split.

### Corrected dyadic exponent geometry (`ExponentGeometry.lean`)
- `expU_add_expV` : `4/9 + 5/9 = 1`.
- `two_expQ_sub_expU` : `2·13/18 − 4/9 = 1`.
- `two_expQ_add_expH0_add_two_expV` : `2Q + H₀ + 2V = 32/9`.
- `expH0_add_expU_add_two_expV` : `H₀ + U + 2V = 23/9`.
- `composite_exponent_gap` : difference `= 1`.
- `expQ_sub_expV` : `Q − V = 1/6`; `expU_add_expV_sub_expQ` : `U + V − Q = 5/18`.
- `ellExponent γ = γ + 5/9 − 13/18 = γ − 1/6`; `ellExponent_mem_Icc` : `γ ∈ [1/6, 4/9] ⇒
  ellExponent γ ∈ [0, 5/18]`; `ellExponent_top`, `ellExponent_bottom`,
  `ellExponent_eq_top_iff`, `ellExponent_injective`.
- `global_ell_exponent_false` — **the global claim `ℓ ∼ X^{5/18}` is refuted**.

### Centering identities (`CenteringCore.lean`)
- `divIndicator`, `rho`, `indicator_eq_rho_add` : `1_{q ∣ t} = ρ_q(t) + 1/q`.
- `divIndicator_mul_coprime`, `rho_mul_coprime` :
  `ρ_{dp}(t) = ρ_d(t)ρ_p(t) + ρ_d(t)/p + ρ_p(t)/d` for coprime `d, p > 0`.
- Four separated operations: `deleteZeroFrequency`, `subtractInverseModulus`,
  `subtractSourceExpected`, `diagonalRestriction`, with
  `deleteZero_eq_subtractSource_iff` (needs `E = a 0`),
  `deleteZero_eq_subtractInverse_iff` (needs `a 0 = 1/q`),
  `subtractInverse_eq_subtractSource_iff` (needs `E = 1/q`),
  `diagonalRestriction_ne_full`, and `centering_ops_pairwise_distinct`
  (explicit data on which all three one-variable operations differ).

### Conditional target exponent arithmetic (`ConditionalExponentLedger.lean`)
- `TA_target_exponent_arith`, `TA_target_exponent_unique` : `exp(U) + t − exp(H₀) = 2 − 2δ ↔
  t = 23/9 − 2δ`.
- `S4_sq_bound_of_TA_bound_conditional` : **CONDITIONAL ON THE SOURCE NORMALIZATION**
  `|S₄|² ≤ U·T_A/H₀`; with `U = X^{4/9}`, `H₀ = X`, `T_A ≤ X^{23/9−2δ}` it gives
  `|S₄|² ≤ X^{2−2δ}`. This is **not** an unconditional Gate-1B theorem.
- `no_unconditional_TA_target` : the normalization hypothesis is load-bearing.
- `conditional_error_assembly` : triangle-inequality assembly with all analytic
  inputs as explicit hypotheses.

---

## NOT LEAN-PROVED / ANALYTIC (never inhabited)

Represented only as predicates in `ConditionalExponentLedger.lean`
(`SmoothPoissonIdentity`, `SourceCenteringMatch`, `NonCoprimeStrataNegligible`,
`CenteredIncidenceVariance`, `GlobalSwitchedReassembly`, `D2D3CoefficientDictionary`,
`FullTypeII`), or absent entirely:

- real Poisson summation with the source weight;
- smoothing error;
- divisor-function `X^{o(1)}` estimate;
- Mellin separation;
- source expected-term identification;
- non-coprime / diagonal analytic bounds;
- any Bombieri–Vinogradov application;
- any shifted-convolution power saving;
- Centered Incidence Variance;
- Gate 1B closure;
- Full Type II;
- Ford–Maynard / twin primes / Hardy–Littlewood.

`GlobalSwitchedReassembly` and `CenteredIncidenceVariance` are defined but never used
as a hypothesis of a proved theorem other than as an explicit assumption; no
inhabitant of any of these predicates is constructed anywhere in the project.

---

## REPAIRS VERIFIED IN LEAN

1. **`ℓ ∼ X^{5/18}` is not global.** The dyadic statement `L_ℓ = YV/Q`, exponent
   `γ − 1/6 ∈ [0, 5/18]`, is banked (`ellExponent_mem_Icc`), and the global claim is
   refuted (`global_ell_exponent_false`). Only `γ = 4/9` gives `5/18`
   (`ellExponent_eq_top_iff`).
2. **`L_ℓ < X^{1/2}` does not give Bombieri–Vinogradov.** `ellExponent_lt_half` is pure
   `ℚ` arithmetic, and `exponent_inequality_has_no_analytic_content` records that such an
   inequality implies no analytic proposition. BV remains OPEN and is not used.
3. **No proved `d₂ × d₃` reduction.** The dictionary between the source
   prime-product / Möbius–Λ coefficients and divisor coefficients is only the
   uninhabited predicate `D2D3CoefficientDictionary`; `no_free_d2d3_dictionary` shows it
   is not automatic.
4. **`−W(0)` is not source centering.** `negW0_not_source_centering`, plus the four
   separated centering operations in `CenteringCore.lean`
   (`deletion_not_inverse_modulus`, `centering_ops_pairwise_distinct`).
5. **`X^{23/9}` is not a globally authoritative target.** It appears only inside
   `S4_sq_bound_of_TA_bound_conditional`, hypothesised on the source normalization, and
   `no_unconditional_TA_target` shows the hypothesis cannot be dropped.

Additional repair made while formalizing: the phase identity
`(−2h w̄)/(q₁q₂) ≡ (−2h v̄₁q̄₂)/q₁ + (−2h v̄₂q̄₁)/q₂ (mod 1)` is only correct once the
inverses `q̄₂ (mod q₁)` and `q̄₁ (mod q₂)` are *named data* satisfying explicit
congruences; it is stated with `a₁, a₂, b₁, b₂` as hypothesised inverses rather than
with an implicit inverse notation, and the underlying integer statement
(`crt_inverse_decomposition`) is proved first.

---

## AUDIT

- `sorry` : 0 occurrences in this bank.
- `admit` : 0 occurrences in this bank.
- `axiom` declarations : 0 (this bank declares none).
- `#print axioms` on all banked theorems: only `propext`, `Classical.choice`, `Quot.sound`.
- `lake build` : 0 errors.
