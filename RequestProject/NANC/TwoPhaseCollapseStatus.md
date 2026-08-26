# Two-Phase Collapse Algebra Status

## Verdict

`TWO_PHASE_COLLAPSE_PREREQUISITES_BANKED`

Sections 1–6 are machine checked in `RequestProject/NANC/TwoPhaseCollapse.lean` without proof placeholders or new axioms. Section 7 is not asserted.

## Compiled theorem list

### CDV base algebra

- Existing reusable division-free results:
  - `TwinPrimeProject.NANC.cdv_B_eq_A_add_k_w`
  - `TwinPrimeProject.NANC.cdv_mprimeA_sub_mB`
- Quotient-level specializations for `A₀ = (mw₀+2)/r`, `B₀ = (m'w₀+2)/r`, `Aₜ=A₀+mt`, `Bₜ=B₀+m't`, and `wₜ=w₀+rt`:
  - `r_mul_cdvA0`
  - `r_mul_cdvB0`
  - `cdv_B_eq_A_add_k_w_quotient`
  - `cdv_mprimeA_sub_mB_quotient`

The quotient-level statements explicitly require `r ≠ 0`; divisibility alone would permit the degenerate case `r = 0`, where integer quotient reconstruction is unavailable.

### Four-hit determinant algebra

- `cdv_time_shift_determinant`
- `four_hit_determinant_eq_two_k_z`
- `extra_r_formula_iff_degenerate`

The active identity is

`p q' u v' - p' q u' v = 2 k z`.

The rejected formula with right side `2 k r z` is equivalent to the extra degeneracy condition `k z (r-1)=0`; it is not asserted unconditionally.

### Frequency determinant

- `frequency_determinant_ne_zero`

This proves nonvanishing from `IsCoprime (pq) (p'q')` and the two strict nonzero ranges `0 < |h| < pq` and `0 < |h'| < p'q'`. The proof extracts both divisibilities symmetrically.

### CRT specification layer

- `PrimePairFreqData`
- `CRTFrequencyWitness`
- `A_mod_p_spec`
- `A_mod_pprime_spec`
- `B_mod_q_spec`
- `B_mod_qprime_spec`

The four local inverse congruences are encoded in `ZMod`. This banks a proof-carrying specification for chosen integer representatives. It does **not** claim unconditional existence when moduli are zero or non-coprime.

### Primitivity composition

- `A_coprime_P`
- `Ak_coprime_P`

These combine explicit local `IsCoprime` assumptions into primitivity modulo `P = pp'`. The module does not silently infer the local assumptions from unformalized distinct-prime/range data.

### Rational exponent algebra

- `saving_decomposition`
- `region_high_b_no_M_over_L_saving_needed`
- `pascadi_saving_threshold`
- `residual_strip_width`
- `residual_endpoint_gap`

## Uncompiled / open theorem list

### `OPEN_TO_BE_AUDITED_BY_FABLE_OR_OPUS`

The exact final double-reciprocity collapse was deliberately not asserted. The intended formula remains:

\[
\Phi
=
e_P\!\left(Ak\,\overline{mm'}\right)
e_{m'}\!\left(-2N\,\overline{cr}\right)
e\!\left(\frac{NB_0}{cm'}\right).
\]

A future formal statement must first fix precise definitions for `Φ`, each additive-character normalization, all inverse/coprimality hypotheses, and the interpretation of the final rational phase. Its analytic use remains open.

`SHIFTED_TWO_PHASE_KLOOSTERMAN_MEAN_VALUE_OPEN`

## Scope exclusions

No analytic cancellation is proved.
RPA-CELS is not proved.
Type II is not proved.
FCPT is not proved.
Twin primes are not proved.
