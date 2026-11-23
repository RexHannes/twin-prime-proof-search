# The actual signed contribution at two small input primes

This calculation concerns the compensated source of SMALL_INPUT_COMPENSATION, taken at genuine subpower small-input cutoffs. It computes the contribution of the physical prime factors in the first three small-factor strata. The result separates a large favorable aggregate from the adverse two-factor stratum it contains, including both channels of the original outside profile.

Write \(L=\log x\), \(I=(x/2,x]\), \(k=n-2\), \(w=\exp(L^a)\), and \(f=f_x(n)=\Phi_x(n)-\psi_x(n)\) on the native squarefree rough output. Its positive and negative parts have ordinary angular masses \(\Pi(f_\pm)\), normalized so that \(\sum_I f_\pm\sim\Pi(f_\pm)x/(2L)\) when the mass is positive. In particular \(\Pi(f_-)>0\) by the open balanced-three-prime chamber where the actual profile is \(-2\). Fix \(a<b<1\), \(1/3<h<1/2\), and a smooth probability law for \(\tau\) supported in \([1,2]\). Put \(V=\exp(L^b)\), \(U_\tau=\exp(\tau L^b)\), \(T=\exp(2L^b)\), \(H=x^h\), and \(\mathcal F(u)=\Pr(\tau<u)\). Write \(F(p)=\mathcal F(\log p/L^b)\) for any positive integer \(p\). The letter \(T\) here denotes the small-prime cutoff, not the twin-prime mass.

Let \(B(k)\) be the native averaged large Vaughan coefficient at these cutoffs and product threshold \(V\). Its composite squarefree prime row for \(\ell>V\) is
\[
b_\ell(k)=-\log\ell\sum_{m\mid k/\ell}\mu(m)(1-F(m)).
\]
On prime \(k\) the true row is zero. Put \(W(\ell,k)=1+F(\ell)\log(k/\ell)/\log\ell\), \(B'=B-\sum_{V<\ell\le H,\ \ell\mid k}W(\ell,k)b_\ell(k)\), summing prime labels. Both channels retain \(R_w(k)\mu^2(k)\). The complete corrected sum of \(f_+B-f_-B'\) equals the original sharp complete outside sum up to \(o(x/L)\). The proof is the complete native Type I argument and the low-row proof in SMALL_INPUT_COMPENSATION. At these subpower cutoffs the required Euler cancellation still has arbitrary fixed logarithmic saving because \(\log U_\tau\ge L^b\), \(\log w=L^a\), and the harmonic Euler convolution tail is \(O(L^a\exp(-cL^{b-a}))\). The support of its primitive AP fold is \(\le x^{h+o(1)}\), strictly below one half. The weights and truncated divisor counts grow by at most fixed log powers, including \(W\ll L\). The input squareful removal and the upper internal prime powers cost \(o_A(xL^{-A})\) using \(R_w\), the divisor moment and \(V\to\infty\) faster than any log power.

For \(r=0,1,2\) define \(Z_r(x)\) as the exact \(f_+B-f_-B'\) sum restricted to \(k\) with exactly \(r\) distinct prime divisors at most \(T\); all its divisors exceed \(w\). Put
\[
c_0=1,\qquad c_1=\mathbb E_\tau \log(2/\tau),\qquad
c_2=\frac12\mathbb E_\tau\!\left[\log^2(2/\tau)-\frac{\pi^2}{6}\right].
\]
Then the actual signed asymptotic is
\[
\lim_{x\to\infty}\frac{Z_r(x)}{S_b L^{1-b}\log L}
=-\frac{e^{-\gamma_E}}2(1-b)c_r\,\Pi(f_-),\qquad 0\le r\le2. \tag{1}
\]
Thus \(c_2<-.58\). The physical two-small-prime contribution is adverse and diverges positively on the \(S_b\) scale. Yet \(c_0+c_1+c_2\ge1-\pi^2/12>.17\), so the complete at-most-two contribution diverges *negatively*. Since the entire outside sum is \(O_f(S_b)\), the integer inputs with at least three small primes have the precisely opposite positive leading term. This also applies with a bounded fixed output-sector restriction for which \(\Pi(f_-)>0\).

## Proof of the physical coefficients

Put \(j=\#\{\ell\mid k:\ell\text{ prime},\ T<\ell\le H\}\). At \(r=0\) on composites all row prefixes are one, so \(B=-\log k,\ B'=(j-1)\log k\). Returning the true prime boundary costs \(O(S_b)\) in either channel, by the genuine-prime upper for these fixed nonnegative profiles. At \(r=1\) with small \(p\),
\[
B=-1_{p>V}\log p-F(p)\log(k/p),\qquad B'=jF(p)\log k
\]
because \(F(p)=0\) below \(V\) and otherwise the \(p\)-row subtraction pays \(B\). At \(r=2\) write the small primes \(p<q\), and put \(d(p,q)=F(p)+F(q)-F(pq)\). For a large owner its divisor prefix equals \(d(p,q)\); the two small owners have prefixes \(F(q),F(p)\), respectively. Therefore
\[
\begin{aligned}
B={}&-1_{p>V}(\log p)F(q)-1_{q>V}(\log q)F(p)
-d(p,q)\log(k/(pq)),\\
B'={}&-d(p,q)\log(k/(pq))+F(p)F(q)(2\log k-\log(pq))
+j\,d(p,q)\log k.
\end{aligned}
\tag{2}
\]
These retain every small or large owner of the input. Apart from the \(j\)-terms, their normalized size is \(O_f(L^{1-b})+o(L^{1-b}\log L)\), as follows also from the explicit harmonic estimates below.

## Actual progression counts

Write \(g_T=\prod_{2<s\le T}(1-1/(s-1))\), with \(s\) prime. For each fixed \(r\le2\), the prime set \(D\) of size \(r\) specifying the small divisors has \(w<p\le T\). Initially allow squareful inputs when summing this sector after extending its displayed coefficients to depend only on distinct small primes. With the built-in \(w\)-roughness, nonsquarefree inputs cost \(O_A(xL^{-A})\) even after all displayed divisor/log weights, by the original squareful argument. Enforce \(p\mid k\) for the named primes and exclude every remaining odd prime \(\le T\). Bonferroni order \(J=\lceil C_A\log L\rceil\) gives folded modulus \(T^{r+J+1}=x^{o(1)}\), or \(x^{h+o(1)}\) if one further large \(\ell\) for \(j\) is named. The small labels are reconstructed up to at most \(\binom{r+J+1}{r}\) choices, and the one prime \(>T\) is uniquely identified. The original primitive fixed-profile BV estimate (2) of analytic_contracts, including its common prefix, gives total discrepancy \(O_A(xL^{-A})\) with every displayed coefficient. Positive Bonferroni remainders use \(|f|\) and their factorial reciprocal tails absorb all fixed log powers. Coprimality with the marked small primes and small Bonferroni divisors is automatic on \(n\), since all its prime factors exceed the polynomial cut \(x^\delta>T\). Removing \(\ell\mid n\) from its primitive principal costs \(O(L^Cx^{-\delta})\) per output, since there are at most 255 output primes.

Consequently, after summing the chosen \(D\) with any of the displayed bounded-log coefficients, the physical local multiplier of \(D\) in (2) is
\[
g_T\prod_{p\in D}\frac1{p-2}.
\]
Indeed a forced prime replaces \(1-1/(p-1)\) by \(1/(p-1)\). Naming \(j\) adds the factor
\[
J_H=\sum_{T<\ell\le H}\frac1{\ell-1}
=(1-b)\log L+\log(h/2)+o(1).
\]
These are signed evaluations on actual integers in the physical window. The argument allows \(\log k\) by partial summation. In summing error estimates it may also be replaced by \(L+O(1)\).

## Evaluation of the two-prime coefficient

On every fixed logarithmic interval \(0<d<u\le2\), the measures
\[
\sum_{w<p\le T}\frac{\delta_{\log p/L^b}}{p-2}
\]
converge weakly there to \(du/u\) by Mertens. The single-prime \(F\) vanishes below \(u=1\). Its limit gives \(c_1\). For the two-prime \(d(p,q)\), if \(u<d<1/2\) its magnitude is \(O(d)\) and, more sharply, \(O(u)\), because \(\mathcal F\) is uniformly Lipschitz and \(\mathcal F(u)=0\). It vanishes also when the other exponent is below \(1-d\). The corresponding small-edge harmonic mass in the weighted integral is \(O(d)\), since \(\sum_{p\le\exp(dL^b)}(\log p)/(p-2)\ll dL^b+1\). Thus the signed coefficient and its absolute value are integrable uniformly at the origin. Repeated primes cost \(O(1/w)\). Its limit is
\[
\frac12\int_0^2\int_0^2\frac{\mathcal F(u)+\mathcal F(v)-\mathcal F(u+v)}{uv}\,du\,dv .
\]
For a fixed threshold \(t\in[1,2]\), replace \(\mathcal F(u)\) by \(1_{u>t}\) under the expectation. Its integrand numerator equals \(+1\) when both exceed \(t\), and \(-1\) when both are at most \(t\) but their sum exceeds \(t\); otherwise it is zero. The positive integral is \(\log^2(2/t)\). The negative integral is independent of \(t\) after scaling and equals \(\int_0^1 -\log(1-s)\,ds/s=\pi^2/6\). The absolute integral is uniformly finite, so Fubini proves the formula for \(c_2\).

All \(r=2\) terms with \(F(p)F(q)\) have bounded absolute harmonic mass; the same holds for \(d(p,q)\) by the edge argument. The two terms \(1_{p>V}\log p\,F(q)\) and its swap have size \(O(L^b)\) in harmonic norm, since both variables then exceed \(V\). Thus only \(j\,d(p,q)\log k\) contributes to order \(L\log L\) in (2). At \(r=0,1\) exactly the \(j\)-terms similarly contribute at that order. Use \(g_T\sim\mathfrak S_2e^{-\gamma_E}/(2L^b)\), \(S_b\sim\mathfrak S_2x/(2L)\) and \(\sum f_-\sim\Pi(f_-)x/(2L)\) to obtain (1). The retained true prime term is lower order on this logarithmic comparison scale, since \(O(1)=o(L^{1-b}\log L)\).

## A legal pair correction and its debt

For completeness, at fixed \(r\le2\) one can also remove the two-small sector from a newly compensated signed sum pointwise. For a given \(p<q\) insert the full prefix \(\sum_{m\mid k/(pq)}\mu(m)(1-F(m))\), and similarly after adding a low large owner \(T<\ell\le H\). This prefix is one whenever the complementary input has no small factors, as happens for either insertion on the targeted sector. Its values on higher sectors are kept. Use as coefficients the negatives of the appropriate \(B\) and the two parts of \(B'\) in (2), taking \(j\) via the explicit additional prime \(\ell\). In particular neither new correction has any support at \(r<2\). Their complete totals are \(o(x/L)\) against \(f_\pm\) separately. At fixed chosen \(s=pq\) or \(pq\ell\), the primitive prefix is exactly
\[
\frac1{\varphi(s)}\sum_{d\mid s}\frac{\mu(d)}d A_{ns,w}(U_\tau/d).
\]
The \(d=1\) term has arbitrary logarithmic savings using \(b>a\); for \(d>1\) the trivial harmonic bound and \(d>w\) suffice. Levels are \(x^{h+o(1)}\) and every fixed label multiplicity is bounded by a log power. This modification moves the precisely quantified signed contribution (1) into its higher-sector companions. It cannot be assigned a positive terminal saving. The unmodified source with at most two small factors and the newly supported remainder are different quantities.

## All fixed small-factor ranks and their leading cancellation

For every fixed integer \(r\ge0\), (1) holds with \(c_r\) determined by the entire generating function

\[
\sum_{r=0}^\infty c_r z^r
=\mathbb E_\tau\!\left[\frac{e^{\gamma_E z}(2/\tau)^z}{\Gamma(1-z)}\right].
\tag{3}
\]

To check the fixed-rank extension, put \(g(v)=1-\mathcal F(v)\), and for a set \(S\) of \(r\) labeled small primes put \(q_S=\prod_{p\in S}p\) and
\[
M_S=\sum_{A\subseteq S}(-1)^{|A|}g\!\left(\sum_{p\in A}\frac{\log p}{L^b}\right),\qquad M_\varnothing=1.
\]
This is their exact low-divisor prefix. On composites the physical formulas at all ranks are
\[
\begin{aligned}
B&=-M_S\log(k/q_S)-
\sum_{\substack{p\in S\\p>V}}(\log p) M_{S\setminus\{p\}},\\
B'&=-M_S\log(k/q_S)+j M_S\log k+
\sum_{p\in S} F(p)M_{S\setminus\{p\}}\log(k/p).
\end{aligned}
\]
Each \(M_S\) is an iterated finite difference, bounded in absolute value by \(\|g^{(r)}\|_\infty\prod_{p\in S}(\log p/L^b)\) for fixed \(r\ge1\) by the repeated fundamental theorem of calculus. Thus \(M_S\), and the products involving \(F(p)\) or \(1_{p>V}\), have bounded absolute harmonic norms in all \(r\) variables; intervals tending to zero in one exponent have vanishing mass uniformly by the logarithmic prime estimate above. The same Bonferroni proof now has a fixed \(r\)-subset multiplicity at most \(\binom{J+1+r}{r}\) and level \(H T^{J+1+r}=x^{h+o(1)}\). The only term of harmonic size \(L\log L\) is again \(j M_S\log k\) on the negative channel. Consequently its coefficient is the ordinary labeled integral of \(M_S\) over \((0,2]^r\), with measure \((r!)^{-1}\prod_i du_i/u_i\).

Here is a Laplace proof of (3). For a deterministic endpoint \(t>0\), use the test \(g(v)=1_{v\le t}\) in that integral, regarded first as a distribution in \(t\). This is well-defined after testing with a smooth compactly supported \(\tau\)-density, by the uniform finite-difference bound just proved. Equivalently truncate every \(u_i\) below a positive cutoff and then take it to zero after smooth testing. The Laplace transform of the shifted threshold \(1_{\sum_{i\in A}u_i\le t}\) in \(t\) is \(e^{-s\sum_{i\in A}u_i}/s\). Hence the transformed exponential generating sum, coefficient by coefficient at \(z=0\), is
\[
\frac1s\exp\!\left(z\int_0^2(1-e^{-su})\frac{du}{u}\right)
=\frac1s\exp\big(z[\log(2s)+\gamma_E+E_1(2s)]\big),\qquad
E_1(2s)=\int_2^\infty e^{-su}\frac{du}{u},\quad s>0 .
\]
The scalar identity follows by differentiation with respect to \(s\) and the small-argument constant of the exponential integral (equivalently the standard integral definition of \(\gamma_E\)). In a fixed neighborhood of \(z=0\), \(s^{z-1}\) is the Laplace transform of \(t^{-z}/\Gamma(1-z)\), an ordinary locally integrable function. Each term involving a positive power of \(E_1(2s)\) convolves it with a measure supported in \([2,\infty)\), so has zero inverse transform on \(0<t<2\). This reasoning can be applied coefficient by coefficient using finitely many convolutions at each order. On \([1,2]\) the smooth endpoint density has no atom at 2. Testing gives (3) in a neighborhood of zero. Its right side is entire and thus gives the Taylor coefficients at every order. Expanding \(\log\Gamma(1-z)=\gamma_Ez+\sum_{m\ge2}\zeta(m)z^m/m\) recovers \(c_1,c_2\).

In particular \(\sum_{r\ge0}c_r=0\) by the reciprocal-gamma zero at \(z=1\), with absolute convergence. Since the complete genuine source is \(O_f(S_b)\), the ordered signed limit
\[
\lim_{R\to\infty}\ \lim_{x\to\infty}
\frac{\sum_{r>R}Z_r(x)}{S_b L^{1-b}\log L}=0
\]
follows by subtracting each finite partial sum before taking \(R\to\infty\). This argument supplies no uniform bound on growing-rank absolute errors and does not reduce the scale of the undecided complete source to \(o(S_b)\).
