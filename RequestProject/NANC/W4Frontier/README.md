# W4 / Salié frontier supplement

This W4Frontier supplement banks the corrected determinant frontier after the
Salié/DUT3/PDS audits.

The active determinant graph is

```text
pq'uv' - p'qu'v = 2kz,
```

with `delta = kr` and `m' = m + delta`.

The former formula with RHS `2delta z` was false: it contained an extra factor
`r`. Algebraically,

```text
r(2kz) = 2delta z.
```

The signed joint-hit census remains OPEN.

Main points:

- The count-scale covariance target is `C_E << M/H`.
- Unsigned joint-hit mass is `(M/H)^2`.
- `delta = k r` has a unique prime factor in the specified R-range because
  `R^2 > M`; the Lean theorem states the exact finite divisor argument.
- The shift relation is `mPrime = m + delta = m + k*r`, but the determinant RHS
  is `2*k*z`, not the retired `2*delta*z` RHS.
- The RHS exponent at the worst vertex is corrected from
  `delta + z = 24 + 28 = 52` to `k + z = 4 + 28 = 32`.
- This exponent repair does not close the generic signed census.
- The Salié identity, shifted identity, local transform, and complete
  w-correlation classification are explicit proof-carrying external interfaces.
- Salié is lossless-gainless: it clarifies the local transform but supplies no
  exponent saving.
- Any Cauchy route that decouples `E_pq` and `E_p'q'` loses joint rarity.
- All listed exceptional fibres remain open; in particular no `z=0`, `p'|z`,
  `q|z`, non-four-hit, fibre 9, gamma-support, or generic square-root analytic
  conclusion follows merely from exponent arithmetic.
- `SALIE_LARGE_W_FIBRES_5_AND_8` is OPEN_PENDING_EXACT_ASSEMBLY.
- FCPT remains OPEN.

The exact division-free active graph banked in Lean is

```text
p q' u v' - p' q u' v = 2 k z,
delta = k r,
mPrime = m + delta,
z m = p' u' - p u,
z mPrime = q' v' - q v.
```

No analytic estimate is claimed by this supplement.
