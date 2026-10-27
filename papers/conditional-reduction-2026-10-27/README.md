# Conditional Twin-Prime Reduction Notes (27 October 2026)

This directory archives two source-explicit conditional mathematical notes prepared on 27 October 2026 for independent mathematical review. Neither document claims an unconditional proof of the Twin Prime Conjecture, a completed exterior/covariance estimate, or formal-kernel certification of the open analytic hypotheses.

## Included PDFs

1. **[`Twin_Primes_Conditional_Criterion_Rev2_2026-10-27.pdf`](Twin_Primes_Conditional_Criterion_Rev2_2026-10-27.pdf)** (18 pages, Revision 2)
   - **Title:** *A Conditional Criterion for Twin-Prime Abundance: A source-explicit endgame, classical support estimates, and two optional analytic reductions*
   - **SHA-256:** `d71050b71003e7640d842139b347b0bf3ea8722b9f35713a5ebe7db1770535e2`
   - **Summary:**
     - Specifies the shrunken Ford–Maynard divisor weight $H_\varepsilon(n)$, the literal rough comparison $\mathcal{B}_X(n)$, and the exact interior/exterior partition.
     - Proves the exact partition inequality $Q_X \ge C_X + T_X - S_X - D_X$, proper prime-power removal, and the general conditional budget theorems (Theorems 2.3 and 2.4) showing that a positive net signed margin $\kappa = c - t - d - s > 0$ implies $\liminf_{X\to\infty} (\log X)^2 X^{-1} N_2(X) \ge C_2 \kappa > 0$.
     - Supplies self-contained proofs from classical maximal Bombieri–Vinogradov and Bonferroni sieve truncation for the prime-input comparison mass $B_*(X) = (C_2 + o(1))X/L$ (Proposition 3.1) and the complete physical Type-I estimate $T_X \ll_{A,\varepsilon} X L^{-A}$ (Lemma 3.2 and Proposition 3.3).
     - States the remaining interior positivity/leakage bounds (Hypothesis 4.1) and the full exterior upper bound (Equation 4.2) as explicit open hypotheses.
     - Separates two optional routes: the degree-twelve signed sum reduction (Section 5) and the balanced A5 frontier with a repaired fixed-collar / successive-limit smoothing argument (Section 6) and explicit non-A5 remainder obligation (Corollary 6.7).

2. **[`Twin_Primes_Conditional_Reduction_2026-10-27.pdf`](Twin_Primes_Conditional_Reduction_2026-10-27.pdf)** (20 pages, Controlling Draft)
   - **Title:** *A Conditional Reduction of Twin-Prime Abundance to a Signed Ford-Weighted Exterior Estimate: The direct-scalar endgame and the degree-twelve auxiliary reduction*
   - **SHA-256:** `f17d53c71754c1aa5c3faf22da46fbab85365bfeda70b3b6cc0214ea49f4bccb`
   - **Summary:**
     - Initial 20-page draft from which Revision 2 was developed.
     - Establishes the finite partition identity, the sign-sensitive direct-scalar endgame, proper prime-power removal, and the conditional degree-twelve auxiliary reduction to $\mathcal{J}_{12}(X)$ under the rough-input transfer and uniform twelfth-moment hypotheses.

## Verification & Scope Firewall

| Item | Status in Revision 2 |
|---|---|
| Source definitions & exact partition (Section 1; Lemma 2.1) | **PROVED** |
| Prime-input comparison mass $B_*(X) \sim C_2 X/L$ (Proposition 3.1) | **PROVED** (from classical maximal BV and truncation) |
| Complete physical Type I $T_X \ll_{A,\varepsilon} X L^{-A}$ (Proposition 3.3) | **PROVED** (weighted literal-comparison; no exterior mask) |
| Proper prime-power removal & conditional budget endgame (Theorems 2.3, 2.4) | **PROVED** |
| Balanced A5 fixed-collar smoothing & separation (Lemmas 6.1, 6.2) | **PROVED** |
| Interior positivity and positive leakage (Hypothesis 4.1) | **OPEN** (requires source/collar verification) |
| Complete signed exterior upper bound (Equation 4.2) | **OPEN** |
| Rough-input transfer & twelfth moment (Hypotheses 5.1, 5.2) | **OPEN / OPTIONAL** |
| Dispersion background & far prime-pair covariance (Hypotheses 6.3, 6.5) | **OPEN / OPTIONAL** |
| Non-A5 remainder bound (Corollary 6.7) | **OPEN / OPTIONAL** |
| Twin Prime Conjecture | **OPEN** |
