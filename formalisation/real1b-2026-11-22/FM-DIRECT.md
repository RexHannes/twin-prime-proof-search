# Gold 4.65–4.66 · direct Ford–Maynard reduction

The open arithmetic target is a strict upper bound for the full contribution from outputs outside the original 1,566 five-prime boxes. For fixed $0<a<1$ and some fixed $\kappa>0$, the target coefficient is $0.317014679964-\kappa$. The conditional endpoint uses the physical twin-prime mass $T$ and the original comparator $S_b$.

Gold 4.67 expands the lower ledger, Vaughan reduction, five-prime calibration, profile transfer and low-label dependencies into checks on the individual source sums. [Updated analytic dependency graph](FM-ANALYTIC.md)

## Source equivalence

| Manuscript definition | Lean object and check |
|---|---|
| Composite good set, Gold 4.66 Part I | `Direct.good` uses the normalized ordered prime-factor list, nonnegative integral ranks with total at most five, the strict lower face and the strict total tiny-mass budget. `good_iff_rank_good` proves equivalence to `Source.good` for every natural number. |
| Coagulation | `coagulation_iff_rank` covers every positive finite vector of sum one and both directions. A fundamental vector has total tiny mass below epsilon because the first subsum to reach epsilon cannot jump across the forbidden interval. Counting the other coordinates in each block gives a rank witness. Conversely, `rank_iff_allocations` distributes positive slack below the residual budget. Each positive-rank block splits into equal pieces strictly between its two faces plus a tiny piece. The proof includes zero ranks, equal upper faces and repeated coordinates. |
| $H_\epsilon,K$ | Both routes call the same divisor kernels. The small-prime test is strict, the total divisor and beta cutoffs are weak, and the singleton and pair tests in `g0` retain their different endpoints. The three labelled bank variables are prime. The remaining quotient in `Source.labels` is a general integer. All divisors, Möbius weights and the factor $64^{-3}$ are retained. |
| $F,G,\Phi,\psi$ | `phi_eq_legacy` proves equality on the physical window. The new $F,G$ carry this window explicitly. Both use squarefree outputs. Only $F$ carries the polynomial roughness and retained-rank tests. $G$ uses the negative part of $H$. `psi` restricts $\Phi$ to `Closing.boxes`, which checks squarefreeness and strict open cells on the first four ordered prime coordinates of a rank-five output. |
| $B_\sigma$, $\mathcal U$ | `Closing.coeff` sums over each eligible prime label and every eligible divisor of its quotient with $m>U$, $m\ell>D_1$. The remaining cofactor is determined by division. `Direct.largeSum` uses $k=n-2$, input $R_w(k)\mu^2(k)$ and $n\in(x/2,x]$. `whole_eq_legacy` identifies the full sum in the two presentations. |
| $T,S_b$ | `Source.T` and `Source.Sb` are reused verbatim. The output is prime in the same dyadic window. The actual weight uses genuine primality of $n-2$ and $\log(n-2)$, with the output presieve. The comparator uses both presieves and $1/V_y$. `Source.T_le_native` and the dyadic extraction theorem turn eventual positive mass into infinitely many distinct lower twins. |

In Gold 4.59 the selected joint source also restricts the input. Gold 4.65 Part II charges the entire output-box contribution. `source_split` proves $\mathcal U=\mathcal U_{\mathscr B}+\mathcal U_{\mathscr B^c}$ with the same original input weights on both sides.

## Exact owner accounting

`Owners.divisor_complement` proves that the strict Möbius tail equals the unit indicator minus its weak prefix. `owner_row` specializes this to $E_\ell=\max(U,D_1/\ell)$. Summing all labels, `coeff_complement` gives the genuine-prime term $1_{k\text{ prime},k>U}\log k$ minus the complete prefix bank. This term cancels the omitted unit on eligible prime inputs once $U\ge1$. On distinct semiprimes above the cutoffs both labels contribute and `Closing.coeff_semiprime` gives $-\log(pq)$.

`Owners.large_owners` proves Gold 4.66 Part V (2.2) for a nonunit squarefree owner product $M$ coprime to $r>1$, each owner above $\max(U,D_1/U)$. The one-prime case gives (2.1). The proof yields $-(\log M)S_U(r)+B_\sigma(r)-1_{r\text{ prime},r>U}\log r$. The physical source still multiplies by $\mu^2(Mr)$. The finite identity itself holds for arbitrary $r>1$ satisfying the stated coprimality.

## Dependency graph

| Classification | Result or input | Use |
|---|---|---|
| LEAN_PROVED | Good-set equivalence, source equality, whole-box partition, all-owner and semiprime identities | Identify the native objects before using analytic estimates. |
| PAPER_PROVED_NOT_FORMALIZED | `Closing.LowerLedger`, `Closing.Reduction` | The 4.57–4.58 lower covariance ledger and Vaughan/presieve/comparator reduction feed `lower_of_covariance`. Both errors are budgeted on the same scale. |
| PAPER_PROVED_NOT_FORMALIZED | Eventual $S_b>0$ | The manuscript uses the prime distribution and fundamental sieve normalization for $S_b$. |
| PAPER_PROVED_NOT_FORMALIZED | `Calibration` | Gold 4.60 restricted, entire-box identity $\mathcal U_{\mathscr B}=A(\psi)-J_\psi S_b+o(S_b)$. |
| UNVERIFIED_TRANSFER | `ProfileUpper` | Gold 4.64–4.65 adapt Lichtman's distribution and sieve inputs to this specific fixed nonnegative five-prime profile, including collar and normalization issues. The paper gives an argument. The exact source-specific transfer is an explicit Lean hypothesis. |
| LEAN_PROVED | `Grid.integral_le_mesh`, `Grid.total_upper_exact`, `Grid.integral_enclosure` | The Lebesgue integral of (B7) is bounded by the rounded mesh sum. The native certificate reduces the actual contributions of every cell in the kernel and proves the numerical upper bound. Identifying this fixed-profile integral with the physical box payment still uses the preceding calibration and profile hypotheses. |
| LEAN_PROVED | `splice_arithmetic`, `five_factor_rounding`, `box_payment` | Given the preceding box inputs, derive the entire-box cap $0.682878095535$. |
| PAPER_PROVED_NOT_FORMALIZED | `LowLabelEstimate` | Optional Gold 4.66 Part III route. This uses the clean output identity and unique ownership, Fouvry distribution with the stated multiplier, presieve and squarefree restoration, and the Möbius PNT. |
| LEAN_PROVED | `outside_label_split`, `outside_iff_unpaid` | The optional low-label payment leaves every high label on the clean class and all remaining outputs. The exact split retains the native outside profile throughout. |
| OPEN_ARITHMETIC | `OutsideBound a κ` for fixed $\kappa>0$ | Independent favorable upper for the entire remaining signed source. The reported near-half DRZ row and genuine-prime recovery family each leave companions. Neither supplies this bound. |
| LEAN_PROVED | `reserve`, `eventual_positive`, `infinite_of_direct` | Lower ledger, box payment, outside bound and eventual comparator positivity imply positive physical twin mass and infinitude. Each error tolerance is fixed before the scale tends to infinity. |
| LEAN_PROVED | `Grid.infinite_of_certified_profile` | Expanded native endpoint supplies the integral enclosure internally. The historical lower ledger and reduction, box calibration, profile transfer, strict outside bound and comparator positivity are its arithmetic hypotheses. |

## Numerical replay

Run `python3 formalisation/real1b-2026-11-22/full_box.py` to enumerate 1,566 ordered boxes and all $1,566\cdot8^4=6,414,336$ cells using integers. On each cell the fifth coordinate stays above each independent coordinate, so the product denominator increases in each independent coordinate. The verifier uses the opposite corners for the two density bounds and preserves both strict and weak faces of (B7). It rounds every cell outward on denominator $10^{20}$. The endpoint numerators are **26697968067675082204** and **28449989344325252602**.

The native proof first covers the open boxes by closed mesh cells and proves that the product denominator increases between the lower corner and each point. It bounds the two indicator faces with their distinct endpoint conventions, integrates a finite sum of cell majorants, then evaluates the outward-rounded integer bound. The files in `GridColumns/` split the calculation by fourth index so the kernel can check one box at a time. The Python replay also checks the lower enclosure; the Lean closing theorem uses the upper enclosure.

Lean checks $(17/5)1.000081=3.4002754$, the exact upper product $0.682878095534460334193665908$, outward rounding, and the exact difference $0.999892775499-0.682878095535=0.317014679964$. The local analytic payments are used once each.

## Source provenance

The source dictionary is in Gold 4.66 Part I. The integral and transfer are in Gold 4.65 Part II (B1)–(B9), the low-label decomposition is in Gold 4.66 Part III (2)–(15), and the owner product formula is in Gold 4.66 Part V (2.1)–(2.2). These SHA-256 values identify the manuscript versions consulted.

| Source | SHA-256 |
|---|---|
| Gold 4.58 FM Complete Proofs | `5552894853d44df01d97d8cef9564dbdf0adac270636d53ff8696e3a4780044e` |
| Gold 4.60 FM Full Q Complete Proofs | `2289faefac18b373b3b78f4b8e80d892f0085d50ce255920c7bf13c9db3253ac` |
| Gold 4.61 Outside Box Proof Audit | `0f26d6f1c6f9390ed77e46c1251ba06a3d185cb773054f644abf581e0b53e8c7` |
| Gold 4.62 FM Complete Proofs | `d8d1ec53baa193a28643e9aa700e7c50bf4437ff68277c18afdf5b446145e933` |
| Gold 4.63 FM Complete Proofs | `31ddc1aa6c16122987637b7ea152c02d31bec96d310ad6d293a1087a20d25c71` |
| Gold 4.64 FM Complete Proofs | `95bd6328ea85c0941e8ca3550c9b1eb2a9144ce6c80b1a090c8cf4f4017477b9` |
| Gold 4.65 FM Complete Proofs | `eeca844fc048a132e24b8cffc22f0edd53fae3178b3f2f2bcaba62fd9eec87b6` |
| Gold 4.66 FM Complete Proof Report | `993b4f34c631f7ec4a59c38c0fc4fd322875f29430cf55eeb58d7884f6f13bb1` |
