# NANC W-Operator Status

Final algebraic checkpoint:

```text
W_OPERATOR_ALGEBRA_VERIFIED
GRAPH_ENERGY_CANCELLATION_OPEN
```

## BANKED

- `DOUBLE_RECIPROCITY_COLLAPSE_IMPORTED` — treated as the externally audited background checkpoint requested by the user; it is not reproved here.
- `TRUE_H_BLOCK_LOCAL_COEFFICIENTS`
- `TRUE_GLOBAL_CRT_NUMERATOR_GAMMA`
- `W_OPERATOR_H_BLOCK`
- `W_OPERATOR_HPRIME_BLOCK`
- `W_MAP_INJECTIVE_FIXED_P_MPRIME` — banked with the corrected centered signed range `|k| < p/2`; see the correction below.
- `CRITICAL_LENGTH_PRODUCT_BANKED`
- `EXPONENT_MATCH_M_OVER_H_VS_C_TWELFTH`

## CORRECTION TO THE PROPOSED INJECTIVITY RANGE

The proposed implication with only `0 < |k| < p` is false for signed integers. For example, with
`p=5`, `m'=7`, `r=1`, the pairs `k=-1` and `k=4` yield respectively `m=8` and `m=3`; both are
coprime to `p`, both satisfy `0<|k|<p`, and both give the same residue `k/(m'-kr) mod p` (and the
same `m'` component because `r` is fixed). The proof outline's final assertion
`|k₁-k₂|<p` does not follow from the two separate bounds `|kᵢ|<p`.

The machine-banked theorem therefore uses the standard centered signed range
`|kᵢ| < p/2`, which implies `|k₁-k₂|<p`. This is the first exact correction needed to make the
injectivity claim valid. If an application instead uses a one-sided range such as `0<k<p`, that
also supplies unique representatives and can be banked separately.

## SUPERSEDED / REJECTED

- `FABLE_GAMMA_WITH_EXTRA_PPRIME`
- `LOCAL_COEFFICIENT_AS_GLOBAL_GAMMA`
- `PRO_DISCARDS_PPRIME_CRITICISM`
- `W_MAP_INJECTIVE_WITH_ONLY_ABS_K_LT_P` — counterexample recorded above.
- `HIGH_B_CLOSED`
- `RPA_CELS_PROVED`
- `TYPE_II_PROVED`
- `FCPT_PROVED`
- `TWIN_PRIME_PROVED`
- `UNIVERSAL_PARITY_WALL_BREAK`

## OPEN

- `GRAPH_ENERGY_CANCELLATION_OPEN`
- `PASCADI_TRANSFER_TO_GRAPH_ROW_SUPPORT_OPEN`
- `RPA_CELS_OPEN`
- `RESTRICTED_TYPE_II_OPEN`
- `FCPT_OPEN`
- `TWIN_PRIMES_OPEN`

The candidate graph-energy estimate is deliberately not a Lean theorem in this bank:

```text
E_{pm'}(W_{p,m'}) E_{pm'}(Q_L^{-1})
  <= (pm')^3 (H/M)^4 X^{o(1)}.
```

No analytic cancellation, high-`b` closure, Type-II theorem, FCPT theorem, or twin-prime theorem
is asserted.

## Lean declarations

Module: `RequestProject.NANC.WOperator`

- `Moduli`
- `wOperator`
- `wPrimeOperator`
- `gamma`
- `gammaPrime`
- `h_local_coeff_mod_p`
- `h_local_coeff_mod_mprime`
- `h_global_crt_numerator`
- `w_operator_h_block`
- `hprime_local_coeff_mod_pprime`
- `hprime_local_coeff_mod_mprime`
- `w_operator_hprime_block`
- `w_map_injective_fixed_p_mprime`
- `critical_length_product_banked`
- `missing_saving_le_composite_twelfth`
- `worst_corner_exact_match`
