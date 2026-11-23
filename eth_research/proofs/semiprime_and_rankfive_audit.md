# Checks on the semiprime slab and the rank-five comparator

The native source is \(\mathrm{Direct.outsideProfile}\) at commit 43facedcf40b2f998aa47f7198d6b9b5feb5b792. The semiprime calculation uses the full source signs in the physical interval \(x/2<n\le x\) and \(k=n-2\). Write \(\epsilon=10^{-9}\), \(S^\circ=\mathfrak S_2 x/(2\log x)\sim S_b\).

## Audit of the true semiprime inputs

Take \(k=pq\) with \(x^{.492}<p\le x^{.494}\) and \(P^-(n)>x^{.21}\). The prime factors of \(k\) are distinct, larger than the original owner cutoff \(x^{.24}\), and \(k>x^{.49}\). By the native semiprime identity, both owners combined give \(-\log k\). At most four primes divide a squarefree \(n\). For composites the good-set witness assigns rank one to each coordinate at most \(1/2+\epsilon\) and rank two to the unique remaining coordinate, if present. All tiny costs vanish. The resulting outside value is \(f=-\max(-H,0)\); a prime and a two-prime output both contribute zero. On triples \(-f\le2\). On quadruples all singles contribute and no triple contributes, so \(-f\) counts complementary pair partitions whose two sums both lie strictly between \(1/2-2\epsilon\) and \(1/2+2\epsilon\). The boundary equality creates no extra contribution. Each failed partition has two semiprime divisors. For the full slab \(-f\le 2+(-f)\mathbf1_{\rm rank=4}/3\), including the maximal case \(3=2+3/3\).

For the product \(pq\), write \(E\) for its unconstrained dyadic input population. Its count is asymptotic to \(a_E x/(2\log x)\), where
\[
a_E=\int_{.492}^{.494}\frac{dt}{t(1-t)}
=\log(31369/31119)=.00800157898663073897925\ldots .
\]
Fouvry–Radziwiłł Theorem 1.1 supplies the absolute primitive discrepancy in each dyadic product rectangle for modulus exponent between .499 and .504. The long prime exponent is between .506 and .508 up to \(o(1)\), and \((56\cdot.508-17)/23=.497739130434\ldots<.499\). Both ends have power slack. The long prime coefficient is Siegel–Walfisz on any fixed subinterval: subtraction of two prime prefix estimates handles small moduli, trivial bounds handle larger moduli, and prime divisors of the auxiliary integer \(r\) cost at most \(\omega(r)\le\tau(r)\). Liu–Park–Song Theorem 3.2 covers moduli up to \(x^{.499}\). An outer rectangle cover with relative mesh \(1+\eta\) increases the unconstrained main by \(O(\eta x/\log x)+o_\eta(x/\log x)\). Positivity permits this on both counted populations, first at fixed \(\eta\), then as \(\eta\downarrow0\).

Each sieve-prime factor of the moduli used is \(<x^{.291}\); it is automatically coprime to the two input primes. Thus the primitive mean is exactly the same unrestricted mass times \(1/\varphi(h)\). The ordinary linear upper sieve with cutoff \(x^{.21}\) and level \(x^{.504}\) gives a total positive rough mass, including logarithmic weight, of at most \((2a_E/.504+o(1))S^\circ\). For quadruples, each possible \(M=rs\) has two distinct primes in \([x^{.21},x^{.291}]\) and \(\log M/\log x\in[.5-3\epsilon,.5+3\epsilon]\). Its unordered reciprocal density obeys the upper bound \(.081\cdot6\epsilon/[2(.21)^2]\) by two-variable Mertens integration. The extra sieve of cutoff \(x^{.001}\) and level \(x^{.002}\) recovers \(M,d\) uniquely from \(Md\), which is less than \(x^{.504}\). With the second division by two for complementary pairs the upper is
\[
\limsup U_{E,4}/S^\circ\le
500 a_E\frac{.081\cdot6\epsilon}{2(.21)^2}
=2.2045166595819383\ldots\times10^{-8}.
\]
Accordingly \(0\le\limsup U_E/S_b <.063504602798657\), using \(2.3\times10^{-8}/3\) for the quartic correction. This is a positive cost and is not a favorable deduction in the full outside-source comparison. The numerical upper cannot be subtracted from a separately bounded upper for a larger population.

## Exact sign and size of the good rank-five positive comparator

The native good-support rank-five lemma requires every active coordinate to exceed \(a=1/5-\epsilon\). Conversely, every ordered five-tuple with all coordinates \(>a\) and sum one is good, by assigning rank one to each. Put
\[
t_i=a+\epsilon s_i,\qquad s_i>0,\qquad\sum_{i=1}^{5}s_i=5.
\]
Every \(t_i\le1/5+4\epsilon\), all lie below the upper singleton cutoff \(\beta=1/2-2\epsilon\), and every pair has sum \(<\beta\). There are no active three-prime terms in the good kernel. Let \(N=\#\{i:s_i>1\}\). The native balance formula gives
\[
H=1-N+\binom N2=(N-1)(N-2)/2\ge0.
\]
The height is one for \(N=3\) and three for \(N=4\); \(N=0\) is the single barycenter. Under ordinary uniform measure on the labeled four-dimensional simplex, \(\Pr(s_1>1)=(4/5)^4\) and \(\Pr(s_1>1,s_2>1)=(3/5)^4\), by translating the marked coordinates and dilating the simplex. Therefore \(\mathbb E H=1-5(4/5)^4+10(3/5)^4=31/125\). Restoring the angular weight \(1/\prod t_i\), the Jacobian \(\epsilon^4\), the labeled simplex volume \(5^4/4!\) and the ordering factor \(1/5!\) gives
\[
J_{p,5}=\frac{96875}{576}\epsilon^4(1+\theta),\qquad
0\le\theta\le \exp\!\left(\frac{250\epsilon^2}{(1-5\epsilon)^2}\right)-1
<2.51\cdot10^{-16}.
\]
Indeed AM–GM gives \(1/\prod t_i\ge5^5\). If \(y_i=t_i-1/5\), then \(\sum y_i=0\) and \(\sum y_i^2\le20\epsilon^2\), by maximizing that convex sum at a simplex vertex. Taylor's inequality for \(-\log(1+5y)\) with \(|(1+5y)^{-2}|\le(1-5\epsilon)^{-2}\) bounds the multiplicative error as stated. This \(J_{p,5}\) is strictly positive and of size \(1.6818576388889\cdot10^{-34}\). It is the rank-five part of \(\mathrm{Ledger.goodMass}\), not the five-box integral \(J_\psi\). Its sign agrees with the native positive projection and the older rough bound.

Primary references. Fouvry and Radziwiłł, Theorem 1.1, https://arxiv.org/pdf/1812.00562. Liu, Park and Song, Theorem 3.2, https://doi.org/10.1007/s40993-017-0089-3. Matomäki and Zuniga Alterman, Definition 2.4 and Lemma 2.5, https://doi.org/10.1017/S0305004125000258.
