# NANC Lean Bank Status

| Sector | Status | Lean treatment |
|---|---|---|
| Type I | Externally audited | Proof-carrying interface |
| K0 algebra | Lean-proved | Type-A theorem files |
| K0 recombination | Audited failed route | Tautology theorem |
| Pattern 16/69 | Lean-proved | Finite arithmetic |
| Half-sieve counterexample | Lean-proved | Continuous toy model |
| ROW phase/reduction | Lean-proved reduction | Algebraic theorem files |
| ROW full bound | Open / conditional | Reciprocal concentration input |
| SAME-R | Conditional | Requires pointwise ROW |
| T0 CRT/exponents | Lean-proved | Rational arithmetic |
| VStar variance | Lean-proved | Finite variance identity |
| VStar analytic closure | Conditional | Requires analytic inputs |
| CDV algebra | Lean-proved | Form/redundancy/diagonal files |
| CDV mixed covariance | Open | Input only |
| FCPT | Open | Dependency assembly only |
| Twin primes | Open | No theorem |

## W4 / Salié frontier supplement

| Sector | Status | Lean treatment |
|---|---|---|
| 1/72 vertex and covariance normalization | Proved finite/algebraic | Integer arithmetic |
| Unsigned joint mass versus target | Proved finite | Exponent identities |
| DELTA_SHIFT_INJECTIVITY | PROVED_FINITE | Prime divisibility theorem under `R² > M` and support bounds |
| TWO_K_Z_DETERMINANT_GRAPH | PROVED_ALGEBRAIC | Active graph `pq'uv' - p'qu'v = 2kz` |
| TWO_DELTA_Z_DETERMINANT_GRAPH | FALSE_ROUTE / RETIRED | Extra factor `r`; retained only as historical correction |
| Salié and shifted Salié identities | Conditional | External proof-carrying interfaces |
| Generic local transform | Conditional | External proof-carrying interface |
| Complete w-correlation classification | Conditional | External proof-carrying interface |
| Salié exponent saving | Retired | Lossless-gainless ledger item |
| Decoupling Cauchy routes | False route / retired | Exact exponent losses proved |
| SIGNED_JOINT_HIT_CENSUS | OPEN | Current frontier |
| GENERIC_SIGNED_MEAN_VALUE | OPEN | No square-root cancellation theorem |
| SALIE_LARGE_W_FIBRES_5_AND_8 | OPEN_PENDING_EXACT_ASSEMBLY | No analytic closure claimed |
| FCPT | OPEN | No closure theorem |

## Determinant correction

The active determinant graph is

    pq'uv' - p'qu'v = 2kz,

with delta = kr and m' = m + delta.

The former formula with RHS 2delta z was false: it contained
an extra factor r. Algebraically,

    r(2kz) = 2delta z.

The signed joint-hit census remains OPEN.

The corrected RHS exponent is `k + z = 4 + 28 = 32`; the retired graph used
`delta + z = 24 + 28 = 52`. This correction alone proves no analytic counting
bound. The `z=0`, `p'|z`, `q|z`, non-four-hit, fibre 9, gamma-support, and
generic-census conclusions remain open.

## Route-A fibre frame — notation repair (namespace `RouteAFibreFrame`)

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

The analytic closure of `V_BDH` and `T0_CRT` is not encoded as a Lean theorem;
in Lean these are names with status `ClosedOutsideLean`, usable only through an
explicit hypothesis.

| Sector | Status | Lean treatment |
|---|---|---|
| Fibre affine identities (F1),(F2),(F3) | Lean-proved | `RequestProject/NANC/FibreModel.lean` |
| Row determinant identity (RD), (RD-div) | Lean-proved | `RequestProject/NANC/FibreDeterminant.lean` |
| Same-prime double-hit impossibility | Lean-proved | `RequestProject/NANC/FibreDeterminant.lean` |
| Finite Gram fourth moment (Gram4) | Lean-proved | `RequestProject/NANC/FiniteGramFourthMoment.lean` |
| Conditional FF4 / Route-A dependency | Interface packaging only | `RequestProject/NANC/FF4Interfaces.lean` |
| Rational exponent ledger | Lean-proved | `RequestProject/NANC/FF4ExponentLedger.lean` |
| V_ROUTE_A, FF4, FF4_MIX | Analytically open | Interfaces only |

Full detail: `RequestProject/NANC/RouteAFibreBankStatus.md`.

---

## ROOT-COLLAPSE / R4C / PPD finite bank

```text
LATEST CONTROLLING FINITE ROUTE:
ROOT-COLLAPSE / R4C / PPD

FIRST OPEN ANALYTIC THEOREM:
PPD

FIRST OPEN SOURCE OBLIGATION:
exhaustive weighted clean-edge coverage

LEGACY DSTAR INTERFACES:
preserved, not claimed solved
```

Finite core: `Gate04Root/` (standalone).  Incremental delta on the Gate 0–1
bank: `RequestProject/NANC/Gate01Root/`, exported by
`RequestProject/NANCBank.lean`.  Item-by-item statuses: see the table in
`LEDGER.md` and the machine-checkable ledger
`RequestProject/NANC/Gate01Root/Ledger.lean`.
