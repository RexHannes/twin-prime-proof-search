# The sharp owner cutoff has a macroscopic positive tail

**Exact scope.** This counterexample concerns the proposed extension to arbitrary bounded output weights supported on polynomially rough outputs. The REAL 1B source has the additional prescribed weight \(f=\Phi-\psi\). Its value on the constructed family is unspecified. This result books zero terminal credit.

Let \(I_x=(x/2,x]\), \(L=\log x\), \(U=x^{.24}\), \(D=x^{.49}\) and \(w=\exp(L^a)\) with fixed \(0<a<1\). For squarefree input \(k\) with \(P^-(k)>w\) use the literal native coefficient
\[
 B(k)=\sum_{\ell\mid k,\;\ell\ {\rm prime},\;\ell>U}
 (\log\ell)\sum_{d\mid k/\ell,\;d>U,\;d\ell>D}\mu(d).
\]
Fix \(0<\zeta\le .01\). For every sufficiently small fixed \(\eta>0\) there are \(0\le f_{x,\eta}\le1\) supported on \(n\in I_x\) with \(P^-(n)>x^\zeta\) such that, for all sufficiently large \(x=x(\eta,\zeta,a)\), the sum of \(B(k)f_{x,\eta}(k+2)\) over inputs with a non-owner prime \(\le x^{2\eta}\) is at least \(c_\zeta x/L\). Here \(c_\zeta>0\) is independent of \(\eta\). For any prescribed fixed rank threshold \(K\), shrinking \(\eta\) also permits \(\omega(k/\ell)\ge K\) throughout, with the same lower bound up to an absolute factor.

## Construction

Assume \(0<2\eta<.005\). Take distinct primes and a squarefree integer as follows.

- \(x^{.24-\eta/2}<q<x^{.24-\eta/4}\).
- \(x^\eta<p\le x^{2\eta}\).
- \(m\le x^{.05}\) is any squarefree product of primes in \((x^{2\eta},x^{.01}]\); impose a rank condition on \(m\) only when required.
- Set \(r=qpm\). Take a genuine prime \(.6x/r<\ell\le .8x/r\) with \(P^-(r\ell+2)>x^\zeta\), and put \(k=r\ell\).

For large \(x\), \(k+2\in I_x\) and all factors of \(k\) exceed \(w\). Its unique owner is \(\ell\), which exceeds \(x^{.69}\) eventually. Indeed \(r<x^{.24+.005+.05}=x^{.295}\). Both \(q\) and every prime of \(pm\) are below \(U\), and \(pm<U\). Every divisor of \(r\) above \(U\) is exactly \(qd\) with \(d\mid pm,\ d>1\). Conversely each such divisor qualifies since \(q x^\eta>U\). The product cutoff is automatic, since \(\ell>D\). As \(pm>1\) is squarefree and coprime to \(q\),
\[
 \sum_{d\mid pm,\ d>1}\mu(qd)
 =-\sum_{d\mid pm,\ d>1}\mu(d)=1,\qquad B(k)=\log\ell.
\]
All parameterizations are unique. The factor near exponent .24 is \(q\), the sole prime in \((x^\eta,x^{2\eta}]\) is \(p\), and the owner is \(\ell\). Define \(f_{x,\eta}\) as the indicator of the constructed \(k+2\).

## The genuine prime and output roughness

Put \(N=x/r\ge x^{.705}\). For prime \(\ell\in(.6N,.8N]\) and \(s\nmid 2r\) prime, sieving \(s\mid r\ell+2\) removes one nonzero residue class. For \(s\mid 2r\) no class is removed, since \(r,\ell\) are odd. Use a dimension-one lower linear sieve with level \(N^{.4}\) and limit \(z=x^\zeta\). The sieve parameter is at least \(28\) for all large \(x\); the product over a subset of the odd primes satisfies the ordinary dimension-one bound uniformly in \(r\), and the lower sieve coefficient is bounded below by a fixed positive constant. For a squarefree modulus \(d\) composed of sieve primes, \(r\) is invertible modulo \(d\), and the residue for \(\ell\) is the primitive class \(-2/r\pmod d\). The Bombieri–Vinogradov maximum over residues, applied to genuine-prime log weights at the two interval endpoints and level \(N^{.4}\), bounds the sum of all lower-weight remainder terms by \(O_A(N/(\log N)^A)\) uniformly in \(r\). The principal product is at least
\[
 \prod_{2<s\le z,\ s\ {\rm prime}}\left(1-\frac1{s-1}\right)\gg1/\log z.
\]
Consequently, uniformly in \(r\),
\[
  \sum_{\substack{.6x/r<\ell\le.8x/r\\\ell\ {\rm prime},\ P^-(r\ell+2)>x^\zeta}}\log\ell
   \gg_\zeta \frac{x}{rL}.
\]
Both the primality of the owner and the output roughness have been imposed. No assertion of output primality is needed.

## Harmonic population and rank

For fixed \(\eta\) and then sufficiently large \(x\), Mertens' theorem gives
\[
 \sum_q\frac1q\ \gg\eta,\qquad\sum_p\frac1p\ \gg1,\qquad
 E=\prod_{x^{2\eta}<s\le x^{.01}}\left(1+\frac1s\right)
   \sim \frac{.01}{2\eta}.
\]
Constants in the first two inequalities can be chosen absolute once \(x\) is sufficiently large for the given \(\eta\). Give each unrestricted squarefree product \(m\) of the last primes probability \(E^{-1}/m\). Its independent Bernoulli inclusion probabilities are \(1/(s+1)\). Therefore
\[
 \mathbb E[\log m]=\sum_s\log(s)/(s+1)\le(.01+o(1))L .
\]
Markov gives probability at least \(0.79\) of \(m\le x^{.05}\), for sufficiently large \(x\). In addition, \(\mathbb E\omega(m)=\log(.01/(2\eta))+o(1)\) and \(\operatorname{Var}(\omega(m))\le\mathbb E\omega(m)\). For fixed \(K\), choose \(\eta\) sufficiently small and then \(x\) sufficiently large that \(\Pr(\omega(m)<K)<.2\) by Chebyshev. Intersecting costs at most .2 of the unconditioned probability. Thus \(\sum_m1/m\gg1/\eta\), also after this optional rank cutoff. Combining with the uniform lower sieve and the absence of multiplicity gives
\[
 \sum_{k}f_{x,\eta}(k+2) B(k)
 \gg_\zeta \frac{x}{L}\left(\sum_q\frac1q\right)
     \left(\sum_p\frac1p\right)\left(\sum_m\frac1m\right)
 \gg_\zeta x/L .
\]
For example, an upper bound uniform over this bounded rough output-weight class of \(C(\delta+2^{-K})x/L\) for the native sharp tail is impossible: use \(\delta=2\eta\), take \(K\) large, then \(\eta\) small, and \(x\) large last.

## Implication for the smoothed proof

For the averaged cutoff row a smooth function of \((\log d)/L\) has Fourier transform of rapid decay. The squarefree divisor sum gains the product of factors \(\left|1-e^{it\log s/L}\right|\le\min(2,|t|\log s/L)\). The sharp step does not supply this absolute summability. The family above shows that a sharp small-prime tail can have nonvanishing signed mass even after restricting to actual prime owners and polynomially rough outputs. Applying an **independent signed native calibration to the complete source** can still show that its sharp total agrees with a smooth total to \(o(S_b)\). This compares complete sums and allows the compact approximation of the smooth total. It does not identify the two sector contributions.

At the stronger, primitive-progressions hypothesis for \(f\) and its positive approximating envelope, Gold 4.58 (10.6) and (11.1) justify the asymmetric parameter compactness. With \(.23\le u\le.24\), \(V=x^{.24}\), \(.48\le d\le.49\), the largest two moduli are \(x^u V\le x^{.48}\) and \(x^d\le x^{.49}\). Coefficients are bounded by \(\log e\) and the smooth presieve divisor satisfies \(w^{O(\log L)}=x^{o(1)}\). The Euler principal arguments \(x^u\) and \(x^d/\ell\), when the short range is nonempty, are at least \(x^{.23}\); the shared-prime terms at shorter arguments come with \(1/\ell\) and cost \(O(L^C/V)\). Finite-rank output exclusion bounds and the proper-power debit are uniform. This transfers the **total** if the progression inputs hold. The single-parameter Lean endpoint does not by itself provide these uniform progression inputs.

**References.** Montgomery and Vaughan, *Multiplicative Number Theory II. Primes and Sieves*, Chapters 20–21. [Authors' text](https://personal.science.psu.edu/rcv4/Vol2/Vol2.pdf) Gold 4.58 original manuscript §§10–12 and the current native FM source.
