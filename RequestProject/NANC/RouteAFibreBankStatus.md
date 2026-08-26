# Route-A fibre frame — Lean bank status

Namespace: `RouteAFibreFrame`.

Lean files (all under `RequestProject/NANC/`, all exported by
`RequestProject/NANCBank.lean`):

| File | Contents |
|---|---|
| `RouteANames.lean` | permanent namespace repair: `Sector`, `BankStatus`, `status`, distinctness theorems |
| `FibreModel.lean` | exact integer fibre model, (F1), (F2), `B`-integrality, (F3) |
| `FibreDeterminant.lean` | row determinant identity (RD), (RD-div), same-prime double-hit impossibility |
| `FiniteGramFourthMoment.lean` | finite Gram / fourth-moment Cauchy–Schwarz inequality (Gram4), both forms |
| `FF4Interfaces.lean` | `FF4Hypothesis`, `FF4MixHypothesis`, `RouteAVarianceHypothesis` and the two packaging theorems |
| `FF4ExponentLedger.lean` | rational exponent ledger: `H/R`, `21a + 44b ≥ 21`, vertex margins and deficits |

## Notation repair

```text
V_BDH:
  old V★ analytic sector;
  closed outside Lean by zero-frequency reassembly and multiplicative large sieve.

T0_CRT:
  old T₀★ analytic sector;
  closed outside Lean after CRT repair and multiplicative large sieve.

Tsh_SHIFT:
  separate old shifted operator; do not identify with the new Route-A variance.

V_ROUTE_A:
  new Route-A edge variance formerly called T*;
  analytically OPEN.

FF4:
  sufficient one-row fourth-moment theorem;
  analytically OPEN.

FF4_MIX:
  remaining one-row mixed-prime covariance;
  analytically OPEN and related to CDV mixed covariance.
```

The analytic closure of `V_BDH` and `T0_CRT` is **not** encoded as a Lean
theorem.  In Lean these sectors are only names carrying the status value
`BankStatus.ClosedOutsideLean`; any use of their content must be supplied as an
explicit hypothesis.

## Theorem inventory

Fibre model (`RouteAFibreFrame.Fibre`, integer data `r > 0`, `c`, `w0`, `a0`
with `gcd c r = 1` and `c * w0 + 2 = r * a0`):

* `fibre_m_def`  : `m j = c + j r`
* `fibre_alpha_affine` : `α j = a0 + j w0`
* `fibre_A_expansion` (F1) : `A j t = a0 + c t + j (w0 + r t)`
* `fibre_A_eq_shifted_root` (F2) : `A j t = a0 + c t + j w t`
* `fibre_B_numerator` : `m j' * w t + 2 = r * A j' t`
* `fibre_B_integral` : `r ∣ m j' * w t + 2`
* `fibre_B_eq_A_jprime` (F3) : `B j' t = A j' t`
* `exampleFibre` : the hypotheses are consistent (`r = 3, c = 1, w0 = 1, a0 = 1`)

Row determinant:

* `row_determinant_identity` (RD) : `m j' * A j t - m j * A j' t = 2 (j' - j)`,
  proved for all integers `j, j'` with no ordering assumption
* `common_divisor_divides_two_jdiff`, `common_prime_divides_two_jdiff` (RD-div)
* `same_prime_double_hit_impossible` : for an odd prime `p`, `j ≠ j'` and
  `2 |j' - j| < p`, no `p` divides both `A j t` and `A j' t`

Finite Gram fourth moment (finite index types `J, T`, arrays `x y : J → T → ℂ`):

* `sum_swap_four`, `crossFourth_eq_corr_pairing`, `gramFourth_eq_corr_sq`,
  `crossFourth_le_pairing`
* `finite_gram_fourth_moment_sq` : `(∑_{j,j'} |G_{j,j'}|²)² ≤ Q(x) Q(y)`
* `finite_gram_fourth_moment_cauchy` (Gram4) :
  `∑_{j,j'} |G_{j,j'}|² ≤ Q(x)^{1/2} Q(y)^{1/2}`

Conditional dependency interfaces (packaging only — no analytic bound is
created; the `bound` field is exactly the conjunction of what was supplied):

* `routeA_variance_from_ff4` and `routeA_variance_from_ff4_bound_holds`
* `ff4_from_mix_and_closed_sectors` and
  `ff4_from_mix_and_closed_sectors_bound_holds`
* `gramFourthMomentStatement_holds` : the only *proved* ingredient of the
  Route-A packaging

Rational exponent ledger (dictionary reused from
`RequestProject/NANC/D4/BasicParams.lean`: `R_exp a = a`,
`H_exp a b = a + 2b − 2/3`, `M_exp = 1/3`, `formalMSaving = 1/6`):

* `H_over_R_exponent` : `H_exp a b − R_exp a = 2b − 2/3`, i.e. `H/R = X^{2b−2/3}`
* `exponent_gap_nonneg` : `b ≥ 1/3 ⇒ 2b − 2/3 ≥ 0`
* `R_exp_le_H_exp`, `R_exp_le_H_exp_of_highB`
* `bcRegion a b : 21 ≤ 21a + 44b`, `bcMargin a b = 21a + 44b − 21`
* `bcMargin_V1 = −1/2`, `bcMargin_V2 = 1/9`, `bcMargin_V3 = −5/24` at
  `V₁ = (5/18, 1/3)`, `V₂ = (5/18, 25/72)`, `V₃ = (7/24, 1/3)`
* `bcRegion_vertices` : of the three vertices only `V₂` satisfies `21a + 44b ≥ 21`
* `v2_residual_margin` : if the claimed formal saving `s` and the Route-A deficit
  `d` satisfy `s + d = 19/180`, then the residual `V₂` margin is exactly `1/180`
* `vertex_deficits` : `H_exp − M_exp/2 − formalMSaving` equals `−1/18`, `−1/36`,
  `−1/24` at `V₁`, `V₂`, `V₃`
* `vertex_crg_net` : the banked CRG net exponents `0`, `−1/36`, `0`

## Audit notes

1. `bcRegion` is *only* the arithmetic inequality `21a + 44b ≥ 21`.  Membership
   of a vertex is **not** a claim that the Bettin–Chandee theorem applies there.
2. The supplied data fix only the sum `s + d = 19/180` of the formal saving and
   the Route-A deficit, not the two values separately, so the `1/180` residual
   margin at `V₂` is banked in exactly that conditional form
   (`v2_residual_margin`), together with the unconditional raw margin `1/9`.
3. Newly recorded: `V₁` and `V₃` **fail** the arithmetic inequality
   `21a + 44b ≥ 21` (margins `−1/2` and `−5/24`); only `V₂` satisfies it.
4. The coprimality field `gcd c r = 1` is carried in the fibre data as
   specified.  The affine identities (F1)–(F3) and (RD) do not use it; they use
   only `c * w0 + 2 = r * a0` and, for (F3), `r ≠ 0`.
5. No file asserts FF4, FF4_MIX, `V_ROUTE_A`, CDV mixed covariance, a
   Schatten/Hilbert-valued Bettin–Chandee lift, Route A, Type II, FCPT, or any
   twin-prime bound.

## Required status block

```text
LEAN-BANKED:
- namespace distinction between old V★/T₀★ and new V_ROUTE_A
- fibre affine identities
- B-edge equals A_{j'}
- row determinant identity
- same-prime double-hit impossibility
- finite Gram fourth-moment inequality
- conditional dependency implications
- rational exponent ledger

ANALYTICALLY OPEN:
- V_ROUTE_A
- FF4
- FF4_MIX
- CDV mixed covariance
- Schatten/Hilbert-valued Bettin–Chandee lift
- Route A
- Type II
- FCPT
- twin-prime lower bound
```

Status: `LEAN_BANK_COMPLETE` — every finite theorem listed above compiles with
no `sorry`, no `admit` and no added axioms (only `propext`, `Classical.choice`,
`Quot.sound`).
