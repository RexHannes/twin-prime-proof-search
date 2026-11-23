# Audit of the calibrated whole-source mean

**Target.** At the repository's analytic endpoint, Ledger.calibrated is the squarefree, \(Z=x^\delta\)-rough mask times \(H(n)-K(n)\). Here \(X=x/2\), \(\delta=1/(400000000000)\). The target is the bound for the absolute value of its actual-minus-comparator mean with coefficient \(9\delta^{-2}/(50\cdot99!)\) against \(S_b\). The source statement and deductions below are an independent paper audit of a previously stated premise. No new Lean declaration is asserted.

**Original reviewed.** REAL1B_Gold4_48_FM_MAIN_Complete_Proofs_20261122.md, Appendix H, Parts B–C, SHA-256 a1209a2f45976bad7a86af9c5e2c163ed0aa9dc455ae7a502b75558b3f08e9aa. Recovered locally as an author-supplied research manuscript. The later Gold 4.55–4.58 dossier uses this bound around its lines 7242–7252 and 7949–7958. The audit uses the earlier original and the published source contracts.

## Whole \(H\) mean

Let \(\epsilon=10^{-9}, \gamma=1/2-\epsilon, y=e^{(\log x)^{1/20}}, D=x^\gamma, R=x^{\epsilon/4},s=\log R/\log Z=100\). Write \(G_d(n)\) for the native short-divisor coefficient, including its three cutoffs, and let \(G_d^\pm\) be its two nonnegative parts. The original constructs separate actual and comparator sequences on \(h\) by writing \(n=dh\) and requiring \(P^-(d)>Z\).

For \(k\) supported on primes in \((y,Z]\), the actual divisibility sum uses the true progression \(dh-2\equiv-2\bmod dk\ell\), where the additional Bonferroni label \(\ell\) uses only small primes at most \(y\). The three alphabets are disjoint, so for a fixed modulus the triple \(d,k,\ell\) is unique. Their level is \(x^{\gamma+\epsilon/4+o(1)}<x^{1/2-\epsilon/2}\) eventually. The at most two large coordinates of \(d\) yield bounded interval variation of \(G_d\), so maximal endpoint Bombieri–Vinogradov controls the sum of all errors. The absolute small-prime truncation tail can be bounded using progression discrepancy and its positive reciprocal principal term before applying that same theorem. Factorial decay from truncation at \(C_A\log\log x\) pays any fixed power of \(\log x\). The actual main for each \(k\) is \(W_y\sum_d J_{d,\pm}/(\varphi(d)\varphi(k))\), where \(J_{d,\pm}=\int_{X}^{2X}G_d^\pm(t)\,dt\) and \(W_y=\prod_{2<p\le y}(1-1/(p-1))\).

For the comparator, two distinct forbidden classes occur modulo each odd small prime, and exactly one modulo 2. Dividing by the native density yields precisely \(W_y\). Elementary CRT gives \(W_y\sum_d J_{d,\pm}/(dk)\). The proof's four nonnegative sequences satisfy the standard dimension-one sifting condition, uniformly in the interval \((y,Z]\); the negative ones have size bounded below by the contributions from prime \(d\in(Z,Z^2)\). The linear sieve at the same level on each source is therefore legitimate. For \(P^-(d)>Z\) we have \(d/\varphi(d)=1+o((\log x)^{-A})\), uniformly for fixed \(A\). The ratios of the two medium-prime sieve products differ from one by \(O(1/y)\). Accordingly the two prospective main terms agree up to an error negligible on the terminal scale. Differences between actual and comparator means are bounded by the upper/lower sieve gap times the **single** absolute envelope \(\sum_\pm J_{d,\pm}\le X\). No factor counting the cutoff intervals enters that positive main bound. Combining the marked product and \(\sum_{P^-(d)>Z,d\le D}1/\varphi(d)\le\gamma/\delta+o(1)\) proves the original Part B (6.3)
\[
 \limsup_x\frac{\left|\sum_{n\in I_x}w_nR_Z(n)H(n)\right|}{S_b}
 \le e^{-\gamma_E}\gamma\delta^{-2}\big(F(100)-f(100)\big).
\]
The proof bounds the actual whole rough mean in (5.6) before separately analyzing removal of roughness. Lean adds squarefreeness to \(H\). Since \(|H(n)|\le\tau(n)\), \(|w_n|\ll\log x\), and \(\tau(n)\ll_\delta x^{\delta/4}\), deleting nonsquarefree rough outputs costs
\(O_\delta((\log x)x^{\delta/4}\sum_{q>Z}\lfloor x/q^2\rfloor)=o(S_b)\).

## Whole \(K\) mean

On the squarefree rough physical support the original \(\mu^2(n)\) and marking presieve agree with the Lean coefficient: \(R_Z\) forces \(R_Y\) eventually. Factor \(n=q u v w h\) using the three disjoint prime banks and the general-integer \(q\). There the exact Möbius sign is \(-\mu(q)\). The extension after removing \(\mu^2(n)\) is legitimate only because this first replacement is made holding \(R_Z(n)\), and a repeated factor costs \(o(S_b)\) with the same square-divisor bound and a fixed divisor power for multiplicity. Later sieve midpoints use the extended coefficient \(-\mu(q)\), not a new assertion about \(\mu(quvw)\) at nonsquarefree inputs.

For \((y,Z]\) on \(h\), the Rosser upper and lower weights supported up to \(R=x^{\epsilon/4}\) bracket the exact indicator pointwise. The absolute difference from their midpoint is bounded by half their gap. Wu, Lemma 3.1, permits an arbitrary prime subset satisfying the dimension-one upper product; Mertens verifies this uniformly here. After summing \(k\mid h\), Bonferroni-expand \(R_y(h/k)\) with \(\ell\) supported at smaller primes. Fold \(U=k\ell q\). Given \(U\), \(k,\ell,q\) are determined by their three disjoint prime alphabets. The signed row, either Rosser coefficient and positive Bonferroni error each consequently give bounded or fixed-divisor-power coefficients in this first block.

Lichtman, Theorem 1.4, controls a signed average of four independent divisor-bounded coefficient sequences at fixed reduced residue \(-2\). The other three blocks \(u,v,w\) remain independent. For the smooth kernel, expand \((\log q(U)+\log u+\log v+\log w)^2\) into finitely many products. Normalize individual logs by \(\log x\) to respect the literal divisor bound even on primes, restoring fixed log powers using arbitrary saving. Weighted prime logarithms and \(1/(\log n)^2\) follow by partial summation with the same fixed margins for \(t\in[X-2,2X-2]\). The theorem only bounds a signed factorized discrepancy; this proof never needs an absolute all-moduli quadrilinear estimate. With block exponents \((.466,.0285,.0125)\) and the theorem's \(\epsilon_L=.001\), one has
\[
 .4945<.501,\quad .491<.498,\quad .025<.0285<.03025.
\]
The squarefree \(k,\ell\) are coprime to \(quvw\) while \(q\) need not be coprime to every marked prime in the auxiliary extension: Lichtman's fixed-residue theorem imposes only coprimality with \(-2\). The principal \(\varphi(quvw k)\) retains that distinction. The resulting actual and comparator densities are \(W_y/\varphi(dk)\) and \(W_y/(dk)\) with \(d=quvw\). Their absolute difference is negligible since \(dk\) has no prime at most \(y\). Positive Bonferroni tails are evaluated as separate factorized sums before applying the theorem.

The positive Rosser gap, after comparison with these main terms, is bounded by \(XW_y(\sum_{d\le X^{.517},P^-(d)>Z}1/\varphi(d))V(y,Z)(F(100)-f(100)+o(1))\), using the original ownership bound \(m_X(d)\le64^3\). The two normalized Euler factors are each at most \(2/\delta\) eventually. This gives Part C (1.1),
\[
 \limsup_x\frac{|\sum_n w_nR_Z(n)K(n)|}{S_b}
 \le 4\delta^{-2}\big(F(100)-f(100)\big).
\]

## Exact cap

The linear-sieve equations give \(F(100)-f(100)=2e^{\gamma_E}\rho(99)/100\). The Dickman identity \(u\rho(u)=\int_{u-1}^u\rho(t)dt\) gives \(\rho(99)\le1/99!\) by monotonicity and induction. Using \(e^{\gamma_E}<2\) and \(e^{-\gamma_E}\gamma<1/2\) gives the sum of the two bounds strictly below \(9\delta^{-2}/(50\cdot99!)\). This proves the stated native paper-format estimate including the squarefree mask. It removes a formerly untraced source dependency at paper-audit level. There is no independent positive terminal gain in this cap.

Primary sources: J. D. Lichtman, Theorem 1.4, https://arxiv.org/pdf/2211.09641; J. Wu, Lemma 3.1, https://doi.org/10.1017/S144678871800023X; K. Matomäki and S. Zuniga Alterman, Definition 2.4 and Lemma 2.5, https://doi.org/10.1017/S0305004125000258. The numerical ratios are evaluated with the unchanged native \(S_b\) normalization.
