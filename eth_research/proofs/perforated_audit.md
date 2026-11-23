# Independent check of the perforated polynomial sieve

The candidate in polynomial-rough-holes uses the stated second-moment estimates of the November 19, 2026 version of Lü, Wang and Wu's *On the Hardy–Littlewood–Chowla Conjecture*. I checked the extension of those estimates with the extra divisor polynomial and give a further quantitative rank test below. The published status available to this check is a preprint. Its 2026 spectral and major-arc inputs have not been rederived here. The classical prime-sieve and rank statements below are independent of those spectral inputs, except when taking the difference of the two Möbius signs.

## Source extension

Let \(P_i=(\exp(L^{a_i}),\exp(2L^{a_i})]\cap\mathbb P\), \(1/10<a_i<1/5\), with the fixed exponents distinct, \(L=\log x\). At large \(x\) these bands are disjoint. Write \(R\) for roughness at \(z=x^\beta\) with their primes excluded from the prohibition. A signed polynomial \(S(n)=\sum_{d\mid n}\lambda_d\), with \(|\lambda_d|\le1\), \(d\le x^{.001}\) odd and squarefree, has support avoiding **all** the bands selected for the family.

For the Type II term, every extracted label \(a=p_1\cdots p_K\) in (4.5) is coprime to every \(d\) with \(\lambda_d\ne0\). Therefore \(S(ah)=S(h)\) even at the repeated-prime tuples temporarily introduced by removing \((a,h)=1\). The second-moment operator \(Q_Y\) in (4.7) is literally the same expression as before. The first quadratic factor in (4.6) is bounded by \(\sum_{h\ll X/Y}\tau(h)^2\ll (X/Y)L^3\). The actual input coefficients, including the sifted Möbius coefficient on the prime side, have not changed. The Mellin smoothing loss and the \(O(L^3)\) factor are absorbed by requesting stronger fixed logarithmic accuracy in Propositions 4.2 and 5.3, with \(K\) chosen before its admissible exponents. At the sharp smoothing cutoff and when a label square divides \(mn+2\), the extra weight is bounded by \(\tau(mn+2)\). The summed label multiplicity is at most another divisor factor, since the bands are disjoint, and the pairs \(mn\) add \(\tau(mn)\). Hölder and fixed divisor moments on the two shifts dominate the errors by a fixed logarithmic power times the square root of their ordinary density. The square-divisor exceptional density decays faster than any log power and the smoothing width can be chosen first at stronger precision. [Lü–Wang–Wu v2, equations (4.5)–(4.7), Propositions 4.2, 5.3](https://arxiv.org/html/2610.20242v2)

For Type I, use Proposition 2.1 with the original \(Z=\exp(L^{.24})\), \(U=V=x^{1/5}\). The new supremum norm loss from \(S\) is \(x^{o(1)}\), still negligible in the initial \(O(Z)\) term and for proper prime powers. Expand the \(Z\)-rough cofactor on odd integers by upper/lower Bonferroni of order \(C\log L\), retaining parity directly. The next-order error has arbitrary logarithmic saving in harmonic norm. In the expansion of an auxiliary band weight, the coefficient of \(j\) distinct selected primes is \(j(\rho-1)^{j-1}/V_i\). This follows by differentiating \((1+t)^\omega\) at \(t=\rho-1\). A Taylor remainder after \(j\le J\) is bounded by \((J+1)\binom{\omega}{J+1}/V_i\), and its harmonic mass is arbitrarily small at \(J=C\log L\). For every fixed group the coefficients in its retained expansion are bounded uniformly in \(J\), since \(0<1-\rho<1\). Multiplying by the disjoint roughness sieve divisor yields a unique folded odd squarefree \(d_1\ll x^{.001+o(1)}\), with all absolute harmonic norms bounded by fixed logarithmic powers. In the intermediate truncation errors, \(k\equiv0\bmod r,\ qk+2\equiv0\bmod d_1\) have no solutions when \((d_1,qr)>1\) and provide at most \(O(x/(qrd_1)+1)\) otherwise. The total number of triples is \(x^{.401+o(1)}\), harmless even with the extra \(O(L)\) coefficient.

LWW (3.7) holds for every such squarefree \(d_1\), including odd small primes. At \(d_1a\le x^{1/20}\), their (3.8) gives arbitrary logarithmic accuracy with the sum over \(q,r\) inside the maximal modulus sum, since \(2qr\le x^{.4+o(1)}\) and \(\sqrt{x/(d_1a)}\ge x^{.475}\). Summing outside over \(d_1,a\) costs at most \(O(L^C)\) after extracting \(x\), since \(\prod_{p\mid d_1}(1-1/p)^{-1}\ll\log x\). In the other range \(a>x^{1/25}\) eventually. The two Rankin products in (3.9) are \(x^{o(1)}\) uniformly for this enlarged support. Indeed the number of distinct factors of \(d_1\le x^{.001+o(1)}\) is \(O(L/\log L)\), and each local factor in either product is bounded by a fixed constant. This gives \(x^{.98+o(1)}\) from the harmonic main and \(x^{.451+o(1)}\) from the floor errors. Prefix partial summation handles the sole output logarithm. This justifies the claimed uniform signed sieve-polynomial estimate for each prescribed accuracy and its correspondingly chosen \(K\).

The positive comparison uses the fundamental lemma for an arbitrary subset of odd primes with its one-sided dimension bound and level \(D=x^{.001}\). The ratio of the corresponding whole Mertens product on each interval is an upper bound independent of the omitted primes. Its sieve polynomials have \(|\lambda^\pm_d|\le1\); its local Euler means differ from \(V\) by \(O(s^{-s/2}V)\) at \(s=.001/\beta\). On positive prime mass, the same disjoint-label expansion plus classical prime BV at \(d_1\le x^{.001+o(1)}\) yields the local moments for the auxiliary products with arbitrary log saving. The multiplicative CRT means for distinct groups factor. Treat \(W_j^2\) by \(W_j^2\le C_{K,\rho}W_j\), since each individual pointed exponential is bounded and \(V_i\to\log 2\). The off-diagonal terms and \(-2G+1\) combine to order \(O_{K,\rho}(\delta_s)+o_{b,s}(1)\), the \(b\) diagonal terms leave \(O_{K,\rho}(1/b)\). The sequence of choices \(K\), number of groups \(b\), then \(s\), all before \(x\to\infty\), supports a prescribed relative tolerance. The dimension constants are uniform in the fixed bands and \(s\). There is no available quantitative uniformity in \(a_i,b\) sufficient to send them to a singular value jointly with \(x\). [Koukoulopoulos, Theorem 19.1](https://dms.umontreal.ca/~koukoulo/documents/publications/primes.pdf)

## A quantitative test at fixed factor rank

For any fixed tolerance \(0<\eta<1/8\) and any predetermined integer \(r\ge1\), choose the parameter \(b\) still larger if necessary in the perforated theorem. Then the same fixed \(H=bK\), \(\beta>0\) and bands satisfy, for each sign \(\sigma=\pm1\),

\[
\liminf_{x\to\infty}
\frac{\sum_{x<p\le2x}\log p\,
 R(p+2)\,1_{\mu(p+2)=\sigma}\,
 1_{\text{more than }r\text{ distinct bands divide }p+2}}{xV}
\ \ge\ \frac12-2\eta .
\tag{1}
\]

Here a band divides \(n\) if at least one prime in that band divides it. To prove this, choose \(K,\rho,b,s\) so the signed and unsigned estimates in the candidate have tolerance \(\eta\), and make \(s\) large enough for a sieve upper \(1+C\delta_s\le2\). If at most \(r\) bands divide \(p+2\), their occupied set is contained in some \(r\)-element subset \(B\subseteq[H]\). For this \(B\), reimpose the primality sieve at *all* odd primes \(\le z\) outside the chosen \(r\) bands. No signed transfer and no additional helper groups are needed to count this positive event. The fundamental lemma at \(D=x^{.001}\) plus prime BV gives a relative upper \(1+C\delta_s+o(1)\) times its local mass. Relative to \(V\) that local mass tends to

\[
\prod_{i\notin B}\prod_{q\in P_i}\left(1-\frac1{q-1}\right)
\to 2^{-(H-r)}.
\]

Indeed each band's sum of reciprocal primes tends to \(\log2\), and its sum of squared reciprocals tends to zero. Thus

\[
\limsup\frac{M(R1_{\#\ {\rm occupied}\le r})}{xV}
\ \le\ (1+C\delta_s)\binom Hr2^{r-H}.
\tag{2}
\]

For fixed \(r\), increase \(b\) first until \(2\binom Hr2^{r-H}\le\eta\). This respects every prior choice. On the whole perforated population every squareful output is negligible on the \(xV\) scale by the large least-prime bound. Each sign therefore has mass at least \((1/2-\eta-o(1))xV\). Subtracting the positive upper (2) proves (1). These are genuine primes \(p\) with shifted outputs having more than the prescribed number of distinct prime factors. For the minus sign their squarefree outputs are odd-rank composites, supplying explicit donors at the very \(x/\log x\) scale under consideration.

On rank one every nonempty pointed label \(W_j(p+2)\) is exactly zero, as all band primes are \(o(x)\). Imposing exact rank one inside its signed weighted theorem gives zero on both sides tautologically. Even the positive upper for the unperforated subset is only \((1+C\delta_s)2^{-H}xV\), and includes every twin and other rough outputs. Equations (1) and (2) exhibit the rank-one limitation on the original prime measure and with the required order of magnitude. They supply no lower bound for the mass at rank one or for the native terminal reserve.
