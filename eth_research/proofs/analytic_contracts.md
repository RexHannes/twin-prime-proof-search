# The calibrated mean and the four signed Vaughan estimates

This paper-level derivation uses commit 43facedcf40b2f998aa47f7198d6b9b5feb5b792. The quantities are those of FMAnalyticEndpoint, FMAnalyticReduction, FMDirect and FMLowerLedger. Put \(X=x/2\), \(L=\log x\), \(I=(X,x]\), \(y=\exp(L^{1/20})\), \(\epsilon=10^{-9}\), \(\gamma=1/2-\epsilon\), \(\delta=\epsilon/400\), \(Z=x^\delta\). Write \(R_t(k)=1_{P^-(k)>t}\), \(V_t=\prod_{p\le t}(1-1/p)\), \(W_t=\prod_{2<p\le t}(1-1/(p-1))\). Let \(a_n=R_y(n)\vartheta_{\mathbb P}(n-2)\), \(b_n=R_y(n)R_y(n-2)/V_y\) and \(w_n=a_n-b_n\). The companion normalization proof gives \(S_b\sim\mathfrak S_2X/L\), where \(\mathfrak S_2=\lim_{t\to\infty}W_t/V_t\). The original derivations are in Gold 4.48 Appendix H Parts B–C and 4.58 Parts A–B. The separate referee's calibrated-mean note contains additional contract details.

## Calibrated complete divisor sum

We obtain the native bound

\[
\limsup_{x\to\infty}\frac{|\sum_{n\in I}w_n\mu^2(n)R_Z(n)(H(n)-K_X(n))|}{S_b}
\le\frac{9\delta^{-2}}{50\,99!}.
\tag{1}
\]

In the \(H\) term, remove squareful \(Z\)-rough outputs first. Every repeated prime then exceeds \(Z\), so their count is at most \(x\sum_{m>Z}m^{-2}\ll x/Z\). The weights are bounded by \(O(L)\) times a fixed divisor power, which is \(O_\delta(x^{\delta/4})\). The cost is \(O_A(xL^{-A})\) for every fixed \(A\).

For each divisor \(d\le x^\gamma\), let \(G_d(t)\) be its native coefficient at varying output \(t\in I\), and put \(J_{d,\pm}=\int_I (G_d(t))_\pm\,dt\). These functions are bounded by one with uniformly bounded variation on \(I\). At most two prime factors of \(d\) exceed \(X^\nu\), since \(3\nu>\gamma\). They and the comparisons of \(d\), one prime, or a pair to the native threshold powers give only a bounded number of changes. For each sign apply the linear sieve to its nonnegative cofactor sequence indexed by \(h\), summed over \(n=dh\in I\) with \(R_Z(d)R_y(h)=1\).

At squarefree \(k\mid \prod_{y<p\le Z}p\) of level \(D_s=x^{\epsilon/4}\), the actual and comparator main terms respectively are

\[
\frac{W_y}{\varphi(k)}\sum_{R_Z(d)=1,d\le x^\gamma}\frac{J_{d,\pm}}{\varphi(d)},
\qquad
\frac{W_y}{k}\sum_{R_Z(d)=1,d\le x^\gamma}\frac{J_{d,\pm}}{d}.
\]

The sum over these \(k\) of absolute discrepancies is \(O_A(xL^{-A})\). For actual primes the additional Bonferroni divisor \(\ell\) consists of at most \(C_A\log L+1\) odd primes \(\le y\), and \(d k\ell\) determines its three parts uniquely. The residue of \(n-2\) is \(-2\) modulo this odd product, and \(dk\ell\le x^{1/2-3\epsilon/4+o(1)}\). Maximal-endpoint Bombieri–Vinogradov and bounded variation pay the discrepancy. Both the signed polynomial and the positive next-order remainder have this same injective grouping. Their harmonic tails have arbitrary fixed logarithmic saving by \((C\log L)^j/j!\). On the comparator the two forbidden residues of the cofactor at odd \(p\le y\) are distinct, and the factor at 2 is \(1/2\). After division by \(V_y\), their product is \(W_y\). The CRT floor errors total \(x^{\gamma+\epsilon/4+o(1)}\). To apply a relative-error level definition, the positive sign contains \(d=1\), while the negative sign contains every prime \(Z<d<Z^2\). Both unsifted sizes are consequently \(\gg XW_y\).

For middle primes the two densities are \(1/(p-1)\) and \(1/p\). Their product ratio is \(1+O(1/y)\), and \(d/\varphi(d)=1+O(L/(Z\log Z))\). The dimension-one condition holds uniformly for this prime subset by comparison with the full Mertens product. At \(s=\log D_s/\log Z=100\), each true and comparator mass is in the linear-sieve interval with coefficients \(f(s),F(s)\), up to \(o(S_b)\) after matching their main terms. The integral of the positive and negative parts together is at most \(X\) per \(d\). Finally,

\[
\sum_{d\le x^\gamma,\ R_Z(d)=1}\frac1{\varphi(d)}
\le\prod_{Z<p\le x^\gamma}\left(1+\frac p{(p-1)^2}\right)
\le\gamma/\delta+o(1).
\]

Since \(W_Z\sim\mathfrak S_2 e^{-\gamma_E}/(\delta L)\), this bounds the normalized \(H\) term by \(e^{-\gamma_E}\gamma\delta^{-2}(F(100)-f(100))\).

For \(K_X\), on the original squarefree and \(Z\)-rough support the weaker mark cutoff is automatic. Write the marked divisor \(d=quvw\), with the general integer \(q\) and the three primes \(u,v,w\) in their original banks. On squarefree outputs \(\mu(d)=-\mu(q)\). Extend this latter coefficient to all representations after removing squareful outputs by the same rough-square and divisor bound. Keep \(R_Z(q)\); the three prime banks already exceed \(Z\). For \(n=dh\) insert the midpoint of the ordinary Rosser upper and lower sums for the middle part of \(R_Z(h)\). Its pointwise absolute error is bounded by half the sum of their difference. On this nonnegative envelope one may discard \(\mu(q)\) and the multiplier \(0\le 1-\log^2(d)/\log^2(n)\le1\).

Fold the medium divisor \(k\le D_s\), the odd Bonferroni divisor \(\ell\), and \(q\) into \(U=k\ell q\), retaining their disjoint prime ranges. The coefficient of \(U\) is independent of \(u,v,w\). Even if the new \(q\) shares a bank prime on an artificially introduced squareful output, the three small/medium/large parts within \(U\) are still uniquely recoverable. The multiplier expands in finitely many separated logarithms of the *original* \(q(U),u,v,w\), with a smooth factor at \(n\). Partial summation restores this multiplier and the genuine prime logarithm. Lichtman's fixed-residue, signed quadrilinear Theorem 1.4 applies with \((Q,R,S)=(X^{.466},X^{.0285},X^{.0125})\), \(a=-2\), and \(\epsilon_L=.001\): the three comparisons are \(.4945<.501,\ .491<.498,\ .025<.0285<.03025\). The same application controls the positive Bonferroni remainder and the Rosser-gap expression after grouping. All harmonic tails permit arbitrary logarithmic precision.

The actual and comparator main terms are \(W_y\int_I g_d/\varphi(dk)\) and \(W_y\int_I g_d/(dk)\), with \(g_d(t)=1-\log^2(d)/\log^2(t)\). Their signed midpoint difference is \(O_A(xL^{-A})\), since \(dk\) has only primes \(>y\), \(dk/\varphi(dk)=1+O(L/(y\log y))\), and only fixed logarithmic powers occur in the absolute reciprocal sums. The normalized gap is at most \(4\delta^{-2}(F(100)-f(100))\). Indeed the bank representation count divided by \(64^3\) is at most one. The three banks are disjoint, and fewer than 100 of their primes can divide \(n\), because each exceeds \(n^{.01}\). The product of the three bank counts is at most \((100/3)^3<64^3\), also for squareful \(n\). The reciprocal \(d\)-sum for \(d\le X^{.517}\) is bounded as above by \(2/\delta\), while \(XW_y(V_Z/V_y)/S_b<2/\delta\) eventually. The upper-minus-lower Rosser Euler sum for the arbitrary middle-prime subset is bounded by its local product times \(F(100)-f(100)+o(1)\). These factors include both the source and comparator costs with the midpoint factor \(1/2\).

The linear-sieve delay equations give \(F(100)-f(100)=2e^{\gamma_E}\rho(99)/100\). The Dickman integral identity \(u\rho(u)=\int_{u-1}^{u}\rho(v)\,dv\) and monotonicity give \(\rho(99)\le1/99!\) by induction. Use \(e^{-\gamma_E}\gamma+4<9/2\) and \(e^{\gamma_E}<2\). This proves (1) in the exact normalization of Ledger.Estimates.calibratedMean. [Lichtman, Theorem 1.4](https://arxiv.org/pdf/2211.09641) · [J. Wu, Lemma 3.1](https://doi.org/10.1017/S144678871800023X) · [Matomäki and Zuniga Alterman, Definition 2.4 and Lemma 2.5](https://arxiv.org/html/2405.19063v3#S2.SS3)

## The fixed-rank prime-product distribution needed for both signed profiles

Take either \(P_x(n)=\mathrm{Direct.phi}(x,n)\) or \(P_x(n)=\mathrm{Direct.psi}(x,n)\), and fix \(0<a<1\). The exact support and the proved good-set lemmas in the native code give a squarefree product of at most 255 primes, each \(>Z\), wherever \(P_x\ne0\) for sufficiently large \(x\). Its absolute size is bounded by a fixed constant. In the ordered logarithms of these primes \(P_x\), \(|P_x|\) are bounded, uniformly Lipschitz functions on the chambers of a finite collection of affine faces in \(\log p_i/L\). Indeed each divisor and the general marked cofactor are subset products. The fixed banks compare subset sums with constant multiples of \(\log X/L\); the denominator \(\log n/L\) stays bounded away from zero. The good assignment has finitely many rank vectors and each excess is a positive part of an affine expression in angular coordinates. The physical rough cutoff and the ordered boxes add finitely many faces. Identically constant face tests can be evaluated first, including strict/weak endpoints.

For every \(\xi>0,A>0\), both weights satisfy the following with either one in place of \(P_x\). Uniformly in the common output endpoint \(T\in[X,x]\),

\[
\sum_{\substack{d\le x^{1/2-\xi}\\d\ \mathrm{odd}}}
\left|\sum_{\substack{X<n\le T\\n\equiv2\pmod d}}P_x(n)-
\frac1{\varphi(d)}\sum_{\substack{X<n\le T\\(n,d)=1}}P_x(n)\right|
\ll_{A,\xi}xL^{-A}.
\tag{2}
\]

Partition \(\log p_i/L\) with step \(\eta=L^{-B}\). Occupancies in disjoint prime bins count each squarefree integer once, including repeated occupancies of a bin. For each occupancy apply Liu, Park and Song, Theorem 3.2, to products of distinct primes with identical/disjoint prescribed intervals. Use base \(N=T\) and outer exponent \(u=1\), adjusting the level gap from \(\xi\) to \(\xi/2\) if necessary. The printed theorem makes its implied constant independent of the interval endpoints. One can put each finite set of permitted primes in its own closed interval, so strict bin boundary conventions create no overcount. For \(n\le T\) versus the strict printed cutoff one can evaluate at \(\lfloor T\rfloor+1/2\) and subtract the corresponding lower endpoint. The number of bins is a fixed power of \(L\), paid by the arbitrary logarithmic saving.

Here is an elementary estimate for all collar errors that occur when freezing \(P_x\). In a width \(O(\eta)\) collar for a nonconstant affine face, fix all prime factors except a coordinate with nonzero coefficient. Its logarithm varies on an interval of length \(O(\eta L)\); if the product of the fixed factors is \(M\), the dyadic cutoff limits the number of integer candidates to \(O(\eta Lx/M+1)\). The sum of \(1/M\) is \(O_{\delta,r}(1)\) by Mertens in \([x^{\delta/2},x]\), and \(M\ll x^{1-\delta/2}\) with at most a fixed factorial multiplicity. The larger range \(p_i\ge x^{\delta/2}\) safely contains all cells meeting the support. Thus the total collar population is \(O(\eta Lx+x^{1-\delta/2})\). Summing its progression error over moduli costs at most \(\sum_{n\ {\rm in\ collar}}\tau(n-2)\), bounded by Cauchy and \(\sum_{3\le n\le x}\tau(n-2)^2\ll xL^3\). The primitive principal error costs at most the collar count times \(\sum_{d\le x}1/\varphi(d)\ll L\). Away from the collars the coefficient error is \(O(\eta)\) and the same bounds apply. Choose \(B\) sufficiently large. This proves (2), including shifts at every signed threshold. [Liu, Park and Song, Theorem 3.2](https://link.springer.com/article/10.1007/s40993-017-0089-3)

## Input presieve and both signs of Vaughan's Type I term

Set \(w=\exp(L^a)\), \(U=x^{.24}\), \(D=x^{.49}\), \(g_w=\prod_{3\le p\le w}(1-1/(p-1))\). For every coefficient \(|b_e|\ll L\) supported on \(e\le D\), (2) implies

\[
\sum_nP_x(n)R_w(n-2)\sum_{e\mid n-2}b_e
=g_w\sum_nP_x(n)\sum_{\substack{e\le D\\(e,2n)=1}}
  \frac{b_eR_w(e)}{\varphi(e)}+O_A(xL^{-A}).
\tag{3}
\]

Here and below sums over \(n\) use \(I\). Formula (3) also holds for every prefix of \(I\). On the support \(n\) is odd. Decompose \(R_w(n-2)=R_w(e)R_w((n-2)/e)\) and Bonferroni-expand the second factor over odd primes with an order \(j=\lceil C_A\log L\rceil\). The folded modulus \(e\ell\) uniquely determines the \(w\)-rough part \(e\) and the squarefree \(w\)-smooth part \(\ell\). Its size is at most \(Dw^{j+1}=x^{.49+o(1)}\). Since all prime factors of \(n\) exceed \(Z>w\), primitive coprimality in the \(\ell\) factor is automatic, while \((e,n)=1\) remains. Apply (2) to the signed coefficients, and to \(|P_x|\) with \(|b_e|\) for the next-order positive remainder. The latter's harmonic sum in \(\ell\) is at most \(\big(\sum_{3\le p\le w}1/(p-1)\big)^{j+1}/(j+1)!\); this absorbs every required logarithmic power, including the \(e\)-harmonic sum. The same estimate completes the truncated Euler product to \(g_w\). This proves (3). A log factor \(\log(n-2)\) can be inserted by prefix partial summation.

For odd \(h\) having at most 256 distinct prime divisors, all exceeding \(w\), define

\[
A_h(t)=\sum_{m\le t,(m,2h)=1}\frac{\mu(m)R_w(m)}{\varphi(m)},\qquad
B_h(t)=\sum_{m\le t,(m,2h)=1}\frac{\mu(m)R_w(m)\log m}{\varphi(m)}.
\]

At \(x^c\le t\le x^C\), for fixed \(c,C>0\) and each \(E>0\), uniformly in \(h\),

\[
A_h(t)=O_E(L^{-E}),\qquad
B_h(t)=-\frac{\mathfrak S_2(h)}{g_w}+O_E(L^{-E}),\quad
\mathfrak S_2(h)=\mathfrak S_2\prod_{p\mid h}\frac{p-1}{p-2}.
\tag{4}
\]

First omit \(R_w\). Its Dirichlet series is \(\zeta(1+s)^{-1}G_h(s)\). For odd \(p\nmid h\), the factor of \(G_h\) is \(1-\sum_{j\ge1}p^{-js}/[p^j(p-1)]\), while for \(p\mid 2h\) it is \((1-p^{-1-s})^{-1}\). Its coefficient norm weighted by \(d^{1/8}\) is bounded uniformly in \(h\), since the unchanged factors have summable excess and only a bounded number are altered. At \(s=0\), \(G_h(0)=\mathfrak S_2(h)\). The classical Möbius PNT gives the \(O_E(\log^{-E}(2t))\) weighted harmonic sum \(\sum_{m\le t}\mu(m)/m\) and its logarithmic derivative \(\sum_{m\le t}\mu(m)\log(m)/m=-1+O_E(\log^{-E}(2t))\). Convolution, split at \(d=\sqrt t\), gives (4) without \(R_w,g_w\). To insert \(R_w\), convolve with the nonnegative coefficients \(u(d)\) of \(\prod_{3\le p\le w}(1-p^{-s}/(p-1))^{-1}\). Their mass is \(1/g_w\ll\log w\). Also \(\sum_d u(d)d^{1/\log w}\ll\log w\), since the logarithm of the latter product differs from \(\sum_{3\le p\le w}1/p\) by \(O(1)\). Consequently \(d>\sqrt t\) costs \(O(L^a\exp(-cL^{1-a}/2))\). The remaining convolution and its logarithmically differentiated form yield (4), including the stated sign.

Vaughan's native coefficient at \(k=n-2\) is

\[
I(k)=\sum_{m\mid k,\ m\le U}\mu(m)\log(k/m)-
\sum_{md\mid k,\ m,d\le U}\mu(m)\Lambda(d).
\]

In the second term group at \(e=md\), whose coefficient has magnitude at most \(\sum_{d\mid e}\Lambda(d)=\log e\). In the first use (3) also with the output logarithm and with \(b_m=\mu(m)\log m\). For a contributing prime power \(d=\ell^j\), \(\ell>w\) and \((\ell,2n)=1\), the exact primitive harmonic sum in \(m\) equals

\[
\frac{A_{n\ell}(U)-\ell^{-1}A_{n\ell}(U/\ell)}
     {\varphi(\ell^j)} .
\tag{5}
\]

This follows by separating \(\ell\mid m\) and \(\ell\nmid m\) within the squarefree Möbius sum. The first part of (5), summed against \(\log\ell\), is \(O_E(L^{-E})\) using (4) at stronger precision and \(\sum_{\ell^j\le U}\log\ell/\varphi(\ell^j)\ll L\). The same holds for its second part when \(\ell\le\sqrt U\). For the other primes, use \(|A_h(t)|\ll\log(2t)\) and \(\sum_{\ell>\sqrt U,j\ge1}\log\ell/(\ell\varphi(\ell^j))\ll L/\sqrt U\). Thus the *entire* Type I correction with \(\Lambda(d)\) has negligible principal. The \(\log k\) part is negligible from \(A_n(U)\), and the remaining derivative term is \(-g_w B_n(U)=\mathfrak S_2(n)+O_E(L^{-E})\). Every active \(n\) is \(Z\)-rough of rank at most 255, so \(\mathfrak S_2(n)=\mathfrak S_2(1+O(255/Z))\). Consequently

\[
\mathrm{typeI}(a,x,P_x)-\mathfrak S_2\sum_nP_x(n)
=O_A(xL^{-A})+O(x/Z)=o(x/L).
\tag{6}
\]

## Signed short product

Group at \(e=m\ell\) with \(m,\ell>U\), \(\ell\) prime, \(e\le D\). Its signed coefficient has magnitude at most \(\sum_{\ell\mid e}\log\ell\le\log e\). Formula (3) applies. The principal factor at \(n\), apart from \(g_w\), is

\[
\sum_{\substack{U<\ell\le D/U\\\ell\nmid 2n}}
\frac{\log\ell}{\ell-1}
\left[A_{n\ell}(D/\ell)-A_{n\ell}(U)
-\ell^{-1}\{A_{n\ell}(D/\ell^2)-A_{n\ell}(U/\ell)\}\right].
\tag{7}
\]

The first two arguments are at least \(U=x^{.24}\) and at most \(x\), so (4) handles both. The last two may be small. Put \(A_h(t)=0\) below one, then the remaining cost is at most \(O(L\sum_{\ell>U}\log\ell/(\ell(\ell-1)))=O(L^2/U)\). Therefore

\[
\mathrm{shortProduct}(a,x,P_x)=O_A(xL^{-A})+O(xL^2/U)=o(x/L).
\tag{8}
\]

Equations (6) and (8) apply separately on the complete weight \(\phi\) and on the restricted weight \(\psi\). They supply the four signed paper statements in infinite_of_signed_estimates with its finer scale \(x/L\). The proof uses no distribution of the large residual bilinear sum. Combining (1) with the independent companion proofs supplies all six fields of Ledger.Estimates on paper and makes the strengthened lower bound in collar_ledger unconditional at paper level. The native endpoint still takes these mathematical inputs as hypotheses in Lean. Its remaining arithmetic bound concerns the exact signed outside sum with a strict positive margin. No estimate in this note supplies that bound.
