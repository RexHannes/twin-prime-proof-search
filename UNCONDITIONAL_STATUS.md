# Unconditional status report

Requirement for this delta: **no added hypotheses, no weakened statements, no
partial or conditional conclusions.**

This document states, without hedging, which results in this project are
unconditional Lean theorems and which are not. Nothing was upgraded in status,
and no new interface, hypothesis, or "externally audited" record was created.

---

## 1. What is now unconditional (new in this delta)

All four statements below are kernel-checked, `sorry`-free, and depend only on
Lean's standard axioms (`propext`, `Classical.choice`, `Quot.sound`). They carry
no hypotheses beyond the intrinsic ones (`ε > 0`, `n ≠ 0`), and they are not
weakened forms of anything: they are the standard statements.

| Theorem | Statement | File |
| --- | --- | --- |
| `ShiftedMobiusBank.card_divisors_le_mul_rpow` | ∀ ε>0 ∃ C≥1 ∀ n≠0: τ(n) ≤ C·n^ε | `RequestProject/UnconditionalDivisorBound.lean` |
| `ShiftedMobiusBank.card_divisors_pow_le_mul_rpow` | ∀ A, ∀ ε>0 ∃ C≥1 ∀ n≠0: τ(n)^A ≤ C·n^ε | `RequestProject/UnconditionalDivisorBound.lean` |
| `ShiftedMobiusBank.card_divisors_in_range_le_mul_rpow` | #{q ∈ W : q ∣ K} ≤ C·K^ε for every window W and K≠0 | `RequestProject/UnconditionalDivisorBound.lean` |
| `ShiftedMobiusBank.diagonal_divisor_count_le` | Σ_{m≤M} Σ_{n≤N} #{q ∈ W : q ∣ mn+2} ≤ C·MN·(MN+2)^ε | `RequestProject/UnconditionalDivisorBound.lean` |
| `ShiftedMobiusBank.sum_one_div_radical_le` | ∀ ε>0: Σ_{1≤n≤T} 1/rad(n) ≤ C(ε)·T^ε, with C(ε) = exp(Σ_{n≥2} 1/(n(n^ε−1))) | `RequestProject/UnconditionalRankinRadical.lean` |
| `ShiftedMobiusBank.rankin_tail_bound` | ∀ 0<ε<1 ∃ C ∀ T≥1: Σ_{s₁s₂>T} 1/(s₁rad(s₁)·s₂rad(s₂)) ≤ C·T^(−1+ε), uniformly over all finite subfamilies | `RequestProject/UnconditionalRankinRadical.lean` |

Effect on the ledger: two entries that were previously listed as *imported
analytic theorems* — "divisor-bound estimates" and "Rankin/radical summation
estimates" (§14.4–§14.5 of the master task) — are now **proved theorems of this
project**, not assumptions. The divisor-window count is exactly the counting
input `#{q ∼ Q : q ∣ mn+2} ≤ τ(mn+2) ≪ X^ε` used in the pre-Poisson diagonal.

Proof method (both files are self-contained):

* divisor bound: the Euler factorisation `τ(n)/n^ε = ∏_p (a_p+1)/p^{a_pε}`,
  with `(a+1) ≤ 2^a ≤ p^{aε}` at primes with `p^ε ≥ 2` and the uniform factor
  bound `2/(ε log 2)` at the finitely many primes below `2^{1/ε}`;
* Rankin: the twisted density `f_ε(n) = 1/(rad(n)·n^ε)` is multiplicative with
  Euler factors `1 + 1/(p(p^ε−1))`; its partial sums over `N`-smooth numbers
  equal the finite Euler product, which is bounded uniformly in `N` by
  `exp(Σ_{n≥2} 1/(n(n^ε−1)))`, a convergent series.

---

## 2. What is *not* unconditional, and is not claimed

Under the "no conditional conclusions" rule, the following are **not delivered**
and were not touched, marked, or upgraded:

| Target | Status here |
| --- | --- |
| `TII-core`: B(α,β) ≪ X(log X)^{−B} for the shifted Möbius Type-II sum | not proved; open problem (parity) |
| `ACTUAL_KF_TINY_WEDGE` (the `206μ+274θ<1` wedge conclusion `D ≪ XM·X^{−η}`) | not proved unconditionally |
| `DOUBLE_CROSS_GCD` sector bound | not proved unconditionally |
| `ACTUAL_KF_DIAGONAL` (`D_Δ ≪ X^{1+ε}` for the centred dispersion square) | not proved unconditionally |
| `OffdiagCrossCoprime` (Bettin–Chandee application) | not proved unconditionally |
| `CW_mu_window`, `MainTermKilled`, `LowMidConductorsControlled` | not proved unconditionally |

Reason, stated exactly: each of these rests on deep analytic inputs that are
not theorems of this project — the Bettin–Chandee bound for sums of Kloosterman
fractions, the corrected conductor-window Möbius estimate, the multiplicative
large sieve, and zero-free-region cancellation for Möbius in smooth weights.
Within this project they exist only as interfaces (hypotheses), so any statement
built on them is conditional by construction. Deriving them from scratch is not
something this delta achieves, and no substitute, weakened, or hypothesis-laden
version of them was introduced to create the appearance of progress.

The parts of the programme that *are* unconditional Lean theorems remain the
finite/algebraic ones already in the project (exponent algebra such as
`RequestProject/Wedge206274.lean` and `RequestProject/Wedge122162.lean`,
residual-coprimality and CRT collapse in
`RequestProject/DoubleCrossArithmetic.lean`), together with the analytic
estimates added above.

---

## 3. Verdict

`NO_UNCONDITIONAL_UPGRADE_OF_THE_WEDGE; TWO_IMPORTED_ANALYTIC_INPUTS_NOW_PROVED`

Concretely: the divisor bound and the Rankin/radical summation estimates are no
longer assumptions. The KF tiny wedge, the double-cross sector, the F3 (r=2)
conclusion and TII-core remain open and are not claimed in any form.
