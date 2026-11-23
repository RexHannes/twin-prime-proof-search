# Exact occupancy patterns on the polynomially rough companion sieve

Keep the notation of polynomial-rough-holes.md. Select \(K\) large enough to use the Lü–Wang–Wu v2 marked estimate with the fixed log precision needed below, and let \(H\ge K\) be fixed. Take any \(H\) disjoint admissible subpower bands \(\mathcal B_i\) as in that proof. Sieve \(p+2\) by every odd prime \(\le x^\beta\) outside those \(H\) bands. Its indicator and local product are \(R,V\), and \(M\) is the true prime-input log measure on \((x,2x]\). Take \(s=.001/\beta\) sufficiently large. Let \(\theta_s=C s^{-s/2}\), with a dimension-one constant independent of \(H\).

For \(I\subseteq[H]\), write \(P_I(n)\) for the exact indicator that the nonempty divisibility bands of \(n\) are precisely those in \(I\). Define
\[
 q_i=\prod_{\ell\in\mathcal B_i}\left(1-\frac1{\ell-1}\right),
 \qquad
 \pi_I(x)=\prod_{i\in I}(1-q_i)\prod_{i\notin I}q_i
 \longrightarrow 2^{-H}.
\]
For every \(I\), the actual positive mass is between \((1-\theta_s)xV\pi_I\) and \((1+\theta_s)xV\pi_I\), up to \(o_{H,\beta}(xV)\). For every \(I\) with \(|I|\ge K\), the true Möbius sign obeys
\[
 \left|M(\mu R P_I)\right|
 \le 2\theta_s xV\pi_I+o_{H,\beta}(xV).
 \tag{1}
\]
The leading signed upper is relative to the particular occupancy pattern, which can have probability \(2^{-H}\) under the perforated sieve. Both signs therefore have close to half the mass on each such squarefree pattern. The squareful exception is \(o_{H,\beta}(xV)\) because every retained prime factor exceeds \(\exp(L^{1/10})\).

### A bounded quotient multiplier on the genuine source

Let \(S(n)=\sum_{d\mid n}l_d\) be an arbitrary divisor polynomial of the preceding proof, with \(\lvert l_d\rvert\le1\), \(d\) squarefree odd, \(d\le x^{.001}\), and every \(d\) disjoint from the \(H\) bands. For \(|I|\ge K\) and the required fixed \(A>2\), the same Type I and Type II theorem gives
\[
  M(\mu P_I S)\ll_{A,H,\mathbf a}x(\log x)^{-A}. \tag{2}
\]
This is a separate modification before the original Cauchy–Schwarz step. It does not multiply the final scalar HLC estimate by \(P_I\).

Choose exactly \(K\) bands \(J\subset I\). Write \(u_i(n)=\omega_{\mathcal B_i}(n)\). For each \(i\in J\),
\[
 1_{u_i(n)>0}=\sum_{\substack{\ell\in\mathcal B_i\\\ell\mid n}}\frac1{u_i(n)},
\]
with an empty sum when \(u_i=0\). In the bilinear part put \(mn+2=th\), \(t=\prod_{i\in J}\ell_i\), with one selected genuine prime in each of the \(K\) disjoint bands. If \((t,h)=1\), the extracted sign is \(\mu(t)\mu(h)=(-1)^K\mu(h)\), all the \(S\) divisors occur in \(h\), and the new exact-pattern factor left in \(h\) is
\[
 \prod_{i\in J}\frac1{1+u_i(h)}
 \prod_{i\in I\setminus J}1_{u_i(h)>0}
 \prod_{i\in[H]\setminus I}1_{u_i(h)=0}.
\]
It is bounded by one and independent of every particular extracted prime. In LWW (4.5)–(4.8) this factor may be placed with \(\mu(h)S(h)\) in the first Cauchy factor, costing at most the original \(O((MN/Y)L^3)\) bound for \(\sum_{h\ll MN/Y}\tau(h)^2\). The second factor \(Q_Y\), its major term, and its subsequent spectral estimate are unchanged. The band normalizers \(V_i\) used by LWW are bounded away from zero and infinity for fixed \(K\); removing them changes only a constant.

If an extracted prime divides \(h\), \(mn+2\) has a square prime divisor in a band above \(\exp(L^{1/10})\). The divisor-moment counting proof in polynomial-rough-holes.md pays both genuine and newly introduced bad pairs by \(O_B(xL^{-B})\) for every fixed \(B\), including all possible extracting tuples. The product-window collar and Mellin-tail bounds there apply as well, since the new quotient factor is bounded. This deals with the step removing the coprimality constraint and justifies literally using the same unconditioned \(Q_Y\).

For Type I work with the unrearranged indicators. At each band use the inclusion–exclusion expansion of \(1_{u_i=0}\), or its complement, through \(J_0=\lceil C_A\log L\rceil\) distinct prime factors; the Bonferroni remainder is dominated by \(\binom{u_i}{J_0+1}\). Absolute retained coefficients have size at most one, and each band's total prime harmonic mass is bounded. The harmonic remainder is \(O_{A,H}(L^{-A'})\) for every required fixed \(A'\) on choosing \(C_A\) sufficiently large. Each retained union of band primes is \(x^{o(1)}\). The divisor \(d\) uses no band prime and the bands are disjoint, so the fold into the output modulus is unique and gives \(d_1\le x^{.001+o(1)}\) with bounded coefficients. All CRT errors, non-squarefree correction factors, and the Möbius Bombieri–Vinogradov bounds are exactly those of the previously proved marked divisor-polynomial lemma. The original Vaughan correction and ordinary prime-power replacement enjoy the same bounds. These facts prove (2).

### Bracketing each actual pattern

For either of the dimension-one sieve polynomials \(S^\pm\) bracketing \(R\), ordinary prime Bombieri–Vinogradov and precisely the preceding band-indicator expansion give
\[
  M(S^\pm P_I)=x\pi_I(x)
       \sum_d\frac{l_d^\pm}{\varphi(d)}+O_{A,H}(xL^{-A}).
\]
The folded moduli remain \(x^{.001+o(1)}\). Over the reduced fraction classes, absence has probability \(q_i\) and disjoint bands are independent; \(d\) has no prime in any band. Brun–Titchmarsh controls the positive Bonferroni errors as in the earlier positive-mass proof. The fundamental lemma bounds the last main-term multiplier between \((1-\theta_s)V\) and \((1+\theta_s)V\). Multiply the pointwise bracketing inequality by the nonnegative exact \(P_I\) to obtain the positive asserted estimate. For \(|I|\ge K\),
\[
 |M(\mu RP_I)|\le |M(\mu S^-P_I)|+M((S^+-S^-)P_I).
\]
The first term is \(o_{H,\beta}(xV)\) by (2) and the second is at most \(2\theta_s xV\pi_I+o_{H,\beta}(xV)\). This proves (1), with the factor \(\pi_I\) retained in the fixed-\(\beta\) sieve allowance.

### Full perforated source and the surviving zero pattern

The positive cost of all remaining patterns is explicit. By disjointness and finiteness,
\[
 \limsup_{x\to\infty}\frac{|M(\mu R)|}{xV}
 \le
 2\theta_s+(1+\theta_s)2^{-H}\sum_{j=0}^{K-1}\binom Hj.
\]
For fixed \(K\) the second term is \(O_K(H^{K-1}2^{-H})\). One may choose the fixed sieve ratio \(s\) large enough before sending \(x\) to infinity to keep the sieve error at the chosen precision. The actual fully unperforated pattern \(I=\varnothing\) has mass \((1+O(\theta_s)+o(1))2^{-H}xV\), and it contains every true twin. All the specifically controlled patterns in (1) consist exclusively of composites. Their signed precision does not imply any positive lower bound for the unperforated twin mass. The estimates and the blind-sector construction are consistent at the exact absolute terminal scale.

### A precision floor even with every admissible subpower interval

There is also a classical statement on the full, unsieved actual prime-input population. Let \(E^*=(\exp(L^{1/10}),\exp(2L^{1/5})]\cap\mathbb P\) and \(Z^*(n)=1_{q\nmid n\ {\rm for\ all}\ q\in E^*}\). Every admissible Lü–Wang–Wu auxiliary band, including \(x\)-dependent overlapping choices within the stated exponent range, is contained in \(E^*\). Mertens yields
\[
 V^*=\prod_{q\in E^*}(1-1/(q-1))
       \sim \frac{1}{2L^{1/10}} .
\]
Apply the same positive upper/lower sieve at level \(x^{.001}\); now its sieve parameter is \(.0005 L^{4/5}\to\infty\). Prime BV therefore proves
\[
 M(Z^*)\sim xV^*,\qquad M(\mu^2 Z^*)\sim A_2 x V^*,
 \qquad A_2=\prod_{q>2}\left(1-\frac1{q(q-1)}\right).
\]
For the second formula first exclude squares of the fixed primes \(q\le Y\) by CRT and apply the same sieve; their moduli are fixed and eventually coprime to \(E^*\). For \(Y<q\le L\), insert the upper sieve with the progression \(p\equiv-2\bmod q^2\). The folded modulus \(q^2d\le L^2 x^{.001}\) has one representation (the factor from primes \(\le L\) recovers \(q^2\)); these \(q\) are all below \(E^*\). The main upper is \(O(xV^*/Y)\) after summing \(q\), and BV covers the folded discrepancies. For \(L<q\le x^{1/4}\) discard the band restriction and use Brun–Titchmarsh, giving \(O(x/L)=o(xV^*)\). Larger squares contribute \(O(L(x^{3/4}+\sqrt{x}))\) by counting integers. Sending \(x\) to infinity and then \(Y\) to infinity proves the formula.

For any family, however large, of allowed marks, any function \(G_x\) of them which vanishes when they are all zero obeys at each large scale
\[
 M\big(\mu^2|G_x-1|\big)\ge M(\mu^2 Z^*)\sim
          A_2 x/(2L^{1/10}).
\]
Thus even nonlinear, overlapping, or adaptive missing-mark approximations of this specified kind cannot recover the constant on genuine squarefree shifted-prime outputs in absolute variation to \(o(x/L)\) from occupancy alone. This differs in scope from the earlier Gold 4.67 packing observation for a particular disjoint linear-average method. The inequality concerns absolute approximation, not the true value of any signed Möbius sum, and leaves other estimators free to handle the zero pattern independently.

**Sources.** The dispersion inputs are the conditional-on-the-preprint-proof steps in Lü–Wang–Wu v2, (4.5)–(4.8) and (5.33), along with the classical fundamental lemma in Koukoulopoulos, Theorem 19.1. This packet does not independently verify the spectral estimate itself. [Lü–Wang–Wu](https://arxiv.org/html/2610.20242v2) and [Koukoulopoulos](https://dms.umontreal.ca/~koukoulo/documents/publications/primes.pdf).
