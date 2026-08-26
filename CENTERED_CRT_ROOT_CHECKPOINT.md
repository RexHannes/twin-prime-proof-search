# Repaired checkpoint — centered CRT-root normal form

## Verdict

The checkpoint is banked conservatively as a certified normal form, not as an
RPA-CELS or Type-II closure.

| Label | Status | Banked conclusion |
|---|---|---|
| `CENTERED_CHARACTER_IDENTITY` | PROVED (finite algebra, conditional on the standard complete additive orthogonality identity in its abstract Lean statement) | Centering removes exactly the principal additive character; no hit/non-hit branch is discarded. |
| `CRT_ROOT_FUSION` | PROVED | The two affine roots fuse uniquely under CRT; both component identities and root equations are Lean checked. |
| `EXACT_HARMONIC_NORMAL_FORM` | PROVED as a finite normal-form definition | The packet is represented by the normalized primitive harmonic sum. |
| `HARMONIC_CUTOFF` | CONDITIONAL | The cutoff `|h| ≪ H X^{o(1)}` requires scale-`D` smoothness. Lean checks the scaling identity `L²/D=H`. |
| `LEMMA_N1` | CONDITIONAL | The `X^{o(1)}` pointwise bound requires bounded variation or smoothness. It is not claimed for arbitrary bounded weights. |
| `COEFFICIENT_ENERGY` | CONDITIONAL FINITE CONSEQUENCE | Lean proves the normalization from an explicitly supplied discrete Parseval identity and the aggregate `L²/H=D` algebra. Support/residue-class estimates remain assumptions when used analytically. |
| `NORMALIZED_COMMON_COEFFICIENT_D2_TARGET` | CORRECT AND SUFFICIENT | Lean proves that D2 plus energy `≤ D X^{o(1)}` gives `M L² D X^{o(1)} = M L⁴/H X^{o(1)}`. |
| `D2_LARGE_SIEVE_INEQUALITY` | OPEN | No proof or global assumption is installed. |
| `DETERMINANT_RESONANCE_EQUIVALENCE` | NOT PROVED | Only a heuristic correspondence is recorded. |
| `Z_VARIABLE_ELIMINATION` | NOT PROVED | Restoring the full sum and subtracting `z=0` does not constitute elimination. |
| `RPA_CELS / TYPE II / TWIN PRIMES` | OPEN | No downstream closure is claimed. |

## Required clean-packet assumptions

The intended analytic instance has

- `A_{e,t}=α_e+m_e t`, `B_{e,t}=β_e+m'_e t`;
- `m'_e=m_e+k_e r_e` and `m'_e α_e-m_e β_e=2k_e`;
- distinct primes `p,q ≍ L` with `p∤m_e`, `q∤m'_e`;
- support on `O(D)` consecutive integers and pointwise size `X^{o(1)}`;
- smoothness or bounded variation only for decay, truncation, and N1;
- `DH=L²`, `H>1`, hence `D<L²`.

Primality and dyadic-size assumptions are not needed by the finite CRT algebra,
so the Lean CRT structure uses only coprimality and explicit affine-root data.

## Exact centered and CRT formulas

For prime `ℓ`, the intended identity is

`ρ_ℓ(n) = 1_{ℓ|n} - 1/ℓ = (1/ℓ) Σ_{c=1}^{ℓ-1} e(cn/ℓ)`.

The nonzero character pair `(c mod p,d mod q)` maps by
`h ≡ cq+dp (mod pq)` to exactly the units modulo `pq`. The roots

` t_{p,e} ≡ -m_e^{-1}α_e (mod p)`,
` t_{q,e} ≡ -(m'_e)^{-1}β_e (mod q)`

fuse to `T_{pq}(e)` under CRT. This yields the intended exact finite formula

`E_{pq}(e) = (1/pq) Σ_{h mod pq,(h,pq)=1} Ŵ_{D,e}(h/pq)e(-hT_{pq}(e)/pq)`.

The Lean file banks the CRT fusion and the finite harmonic packet without
introducing any analytic cancellation assumption.

## Parseval normalization and D2 target

With `γ_{p,q,h}=Ŵ(h/pq)/(pq)`, discrete Parseval gives pair energy of scale
`D/(pq) ≍ D/L² = 1/H`. Summation over `O(L²)` prime pairs gives total energy
`O(D X^{o(1)})`. The Lean theorem `coefficient_energy_of_parseval` makes the
Parseval convention explicit; `energy_scaling` and
`aggregate_coefficient_energy` verify the normalization algebra.

For a coefficient family common to all outer edges, the sufficient target is

`Σ_e |Σ_{p,q,h} c_{p,q,h} e(-hT_{pq}(e)/(pq))|²`
`  ≪ M L² X^{o(1)} Σ_{p,q,h}|c_{p,q,h}|²`.

Its sufficiency is kernel checked in `normalized_D2_suffices` and
`target_eq_ML4_over_H`. The inequality itself remains open.

## Exact correction found during banking

As written in the checkpoint,

`c_{p,q,h}=b_p d_q Ŵ_{D,e}(h/pq)/(pq)`

depends on the outer edge `e`, because the weight is denoted `W_{D,e}`. But the
stated large-sieve theorem writes `c_{p,q,h}` outside the `e`-sum, i.e. as one
common coefficient vector. These are not literally the same typed statement.

Therefore the ordinary normalized D2 target is banked as correct for a common
weight (or after a proved reduction that removes the `e`-dependence). The
edge-dependent special family is separately represented in Lean and remains an
open structured inequality. This correction does not affect the coefficient
energy calculation edge by edge, but it is necessary before claiming that the
stated common-coefficient D2 inequality applies to the intended `W_{D,e}`.

## Trivial calibration

Lean verifies

`(M²D²)/(ML⁴/H)=M/H`

under `DH=L²`. Thus `M²D²X^{o(1)}` is retained as the calibrated aggregate
trivial baseline. The triangle-inequality alternatives `E₀L⁴` and `E₀H/M` are
not promoted into the proof ledger.

## Files

- `RequestProject/CenteredCRTRootNormalForm.lean`
- re-exported by `RequestProject/Banking.lean`

No D2 large-sieve proof, determinant-resonance equivalence, `z`-elimination,
RPA-CELS closure, Type-II theorem, or twin-prime theorem is asserted.
