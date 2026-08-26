# Gate 0–1 finite bank — status

Scope of this run: **banking and finite reproof only**.  No Gate 0 or Gate 1
closure is claimed.  Nothing analytic is proved: `D*`, `AVG-COV`, `FF4`,
`FF4-MIX`, `CDV`, `CPF`, Route-A closure, high-`P3` closure, Type II, FCPT,
Hardy–Littlewood and twin primes all remain untouched and open.

## Files

| File | Content |
| --- | --- |
| `CanonicalCongruence.lean` | `m_j w_0 = r α_j − 2`, `r α_j ≡ 2 (mod m_j)`, and `α_j ≡ 2 r̄` when `r` is invertible |
| `GenericCRTResidue.lean` | edge determinant `m'A − mB = 2k`; joint-hit criterion; `q`-side residue; `m`-side residue; CRT amalgamation `p n' ≡ w✦ (mod qm)` and `n' ≡ w✦ p̄` |
| `HZeroCentering.lean` | exact centered bilinear expansion; the `h = 0` cancellation `+ − − + = 0` |
| `SamePrimeAndExceptionalRow.lean` | same-prime no joint hit; centered same-prime contribution `−Ŵ(0) ∑ b_p d_p / p²`; exceptional row `p' ∤ B`, `ρ_{p'}(B) = −1/p'`; Ramanujan remainder `p−1` / `−1` |
| `CompletionInterface.lean` | finite CRT phase splitting (integer, rational and exponential forms) and the `COMP` interface structures |
| `DStarInterfaces.lean` | open `D*` inputs, the proved finite strata bundle, the conditional reduction `D* + COMP + strata ⇒ AVG-COV`, and the bookkeeping arithmetic `RK = M`, `(MHL²)/(HL⁴) = M/L²`, `X^{1/3−2b} ≤ X^{−1/3}` for `b ≥ 1/3` |
| `SlotDictionaryAudit.lean` | exponent-level mismatch of the old direct BC slot triple `(H, RL, M)` with the direct COMP masses `(H, L, LM)` and `(H, L², M)` |
| `Ledger.lean` | machine-checked status ledger of all Gate 0–1 items |

## Status ledger

```text
CANONICAL_CONGRUENCE_BANKED                  PROVED
GENERIC_CRT_RESIDUE_BANKED                   PROVED
H_ZERO_CENTERING_CANCELLATION_BANKED         PROVED
SAME_PRIME_NO_JOINT_HIT_BANKED               PROVED
EXCEPTIONAL_ROW_NO_HIT_BANKED                PROVED
RAMANUJAN_MINUS_ONE_REMAINDER_BANKED         PROVED

COMP_GENERIC_COMPLETION_INTERFACE            CONDITIONAL / INTERFACE
STRUCTURED_DSTAR_OPEN_ANALYTIC_INPUT         OPEN_ANALYTIC
ARBITRARY_DSTAR_STRONGER_OPEN_ANALYTIC_INPUT OPEN_ANALYTIC
DSTAR_IMP_AVG_COV_CONDITIONAL_BANKED         CONDITIONAL
AVG_COV                                      OPEN_ANALYTIC
GENERIC_HIGH_P3_CLOSURE                      OPEN_SOURCE_AND_ANALYTIC
OLD_DIRECT_BC_SLOT_DICTIONARY_FALSE_FOR_COMP_REPRESENTATION  AUDITED

FULL_TYPE_II                                 OPEN
FCPT                                         OPEN
TWIN_PRIME                                   OPEN
```

The same ledger is available inside Lean as `RouteAFibreFrame.Gate01.status`,
with the machine-checked guarantees
`bankedFinite_proved`, `analyticItems_not_proved`, `avgCov_open`,
`structuredDStar_open`, `fullTypeII_open`, `fcpt_open`, `twinPrime_open`,
`oldSlotDictionary_audited`.

## Preserved earlier bank

Untouched and still in the bank:

* the fibre model `m_j = c + jr`, `α_j = a0 + j w0`, `w_t = w0 + rt`,
  `A_j(t) = α_j + m_j t` (`RequestProject/NANC/FibreModel.lean`);
* the row determinant `m_{j'} A_j(t) − m_j A_{j'}(t) = 2(j'−j)`
  (`RequestProject/NANC/FibreDeterminant.lean`);
* `B = A + k w`, `m'A − mB = 2k` and the four-hit determinant
  `p q' u v' − p' q u' v = 2 k z`
  (`RequestProject/NANC/W4Frontier/DeterminantGraph.lean`).  The determinant is
  **not** reverted to `2krz` or `2Δz`.

## Audit notes

* `same_prime_no_joint_hit` requires `k ≠ 0` in addition to `2|k| < P`: for
  `k = 0` the shift vanishes and the joint event is *not* empty, so the
  hypothesis is load-bearing and is stated explicitly.
* `q_dvd_B_iff` needs `IsCoprime q m` (the stratum condition `q ∤ m m'`), and
  the edge relation is used in the form `m B = m' A − 2k`.
* `exceptional_row_no_hit` needs only that `p'` is an odd prime dividing `m'`;
  the hypothesis `p' ∤ r` mentioned in the source statement is not required.
* The COMP representation, the truncation of the `h`-range and the error bound
  `|E_e| ≪ D L^{-1} X^{o(1)}` are **interface fields**, never inhabited.
* The slot audit is deliberately narrow: it refutes the *direct* slot
  assignment only.  No claim is made that no Bettin–Chandee, Wright or
  dispersion reformulation can work.

## Trust

No `sorry`, `admit`, `axiom`, `@[implemented_by]` or `opaque` in the Gate 0–1
files.  Representative theorems depend only on `propext`, `Classical.choice`,
`Quot.sound` (the ledger theorems depend on no axioms at all).

Verdict: `ARISTOTLE_FINITE_BANK_COMPLETE`.
