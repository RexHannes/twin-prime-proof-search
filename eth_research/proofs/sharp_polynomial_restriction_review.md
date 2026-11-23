# Audit of sharp complete-source localization to polynomially rough inputs

Take the original sharp large-product coefficient at \(U=V=x^{.24}\), \(D=x^{.49}\), with \(k=n-2\), \(x/2<n\le x\). Write \(\mathcal U_y(f)\) for the same sum with the input mask \(R_y(k)\mu^2(k)\). Assume the native fixed piecewise factor profile \(f\) has the primitive progression estimate proved in uniform_native_transfer.md, also for \(|f|\), and \(\sum|f|\ll_f x/L\). All active output factors exceed \(x^{b_0}\) for fixed \(b_0>0\) and their number is bounded. For fixed \(w=\exp(L^a)\) in the sense of fixed \(a\in(0,1)\), the claim
\[
 \lim_{e\downarrow0}\limsup_{x\to\infty}
  \frac{|\mathcal U_w(f)-\mathcal U_{x^e}(f)|}{S_b}=0
\]
passes my analytic review, subject to those native inputs. Here \(e\) is fixed first, with \(e<b_0\), and \(S_b\asymp x/L\).

Set \(z=x^e\) and \(g_z=\prod_{2<q\le z}(1-1/(q-1))\). In the signed Vaughan Type I and short-product sums, the original divisor \(m\), \(m\ell^j\), or \(m\ell\) is \(z\)-rough. Fundamental-lemma upper and lower weights of level \(x^{.002}\) for the \(z\)-presieve produce uniquely folded moduli with exponent at most \(.492\), inside the primitive progression range. The two weights differ in the local model by \(O(g_z\sigma_s)\) with \(s=.002/e\) and \(\sigma_s=s^{-s/2}\) for \(s\) large. Since \(e<b_0\) the output \(n\) is coprime to the sieve primes. The fixed-\(e\) harmonic absolute cost before multiplying by \(g_z\) is \(O(L/e)\), using
\[
 \sum_{\substack{m\le x\\P^-(m)>z}}
 \frac{\mu^2(m)}{\varphi(m)}
 \le \prod_{z<q\le x}\left(1+\frac1{q-1}\right)\ll 1/e,\qquad
 \sum_{\ell^j\le x}\frac{\log\ell}{\varphi(\ell^j)}\ll L.
\]
The positive comparison uses \(|f|\) and the absolute Type I coefficients. The factor \(1/\varphi(m\ell^j)\) at a shared prime is at most \(1/[\varphi(m)\varphi(\ell^j)]\). As \(g_z\ll1/(eL)\), this bounds the sift discrepancy by \(O_f(e^{-2}\sigma_s)x/L+o_e(x/L)\). A bound of the form \(O(L^C\sigma_s)\) at fixed \(e\) would be insufficient. The same coefficient envelopes and the primitive prefix estimate pay moving physical \(\log k\) weights. Squareful \(z\)-rough inputs and internal large proper prime powers cost \(o_e(x/L)\) by the original divisor-moment calculation.

For fixed \(e\), the signed angular cumulative
\[
 A_z(v)=\sum_{\substack{m\le x^v\\P^-(m)>z}}\frac{\mu(m)}{\varphi(m)}
 \quad\longrightarrow\quad \rho(v/e).
\]
Indeed group squarefree products by their finitely many ranks and pass to ordered distinct prime integrals using the prime number theorem. The absolute angular prime measure converges with density \(dt/t\) on \([e,1]\). Its product measures have atom-free positive-rank sum distributions and repeated primes have negligible total weight. Therefore convergence of the cumulative is uniform in \(0\le v\le1\), after treating the unit separately. The factor \(1/\varphi(q)\) may be replaced by \(1/q\) with an \(o_e(1)\) error. One may recognize the limiting alternating integral by differentiating the finite series, giving \(s\rho'(s)=-\rho(s-1)\). Partial summation gives the logarithmic moment divided by \(\log z\) at \(u\) as
\[
 (u/e)\rho(u/e)-\int_0^{u/e}\rho(t)\,dt+o_e(1).
\]
Excluding the finitely many polynomially large prime divisors of \(n\), and one additional \(\ell>z\), costs \(O_e(x^{-e})\) in the unweighted cumulatives and \(O_e(Lx^{-e})\) in the logarithmic moments. Their harmonic tail is bounded by the preceding positive Euler product. This exclusion is uniform in the separate \(\ell\)-sum.

Mertens gives \(g_z\log z\to\mathfrak S_2 e^{-\gamma}\). The first Type I principal on dividing by \(\sum f\) formally has scalar
\[
 \mathfrak S_2 e^{-\gamma}
 \left[\frac{1-u}{e}\rho(u/e)+\int_0^{u/e}\rho(t)\,dt\right],
 \qquad u=.24.
\]
Equivalently this scalar multiplies \(\sum f\); all absolute errors can be bounded using \(\sum|f|\), even when \(\sum f=0\). Here \(\log k/L=1+O(1/L)\). The second Type I principal and the short-product principal are bounded on the same absolute scale by \(O_f(e^{-1}\rho(.24/e))+o_e(1)\). In the latter both unsubtracted arguments are at least \(U\). An exceptional shared-prime term always has the additional \(1/\ell<1/z\), and may use a crude \(O(1/e)\) harmonic bound. The normalized scalar error from replacing the first principal by \(\mathfrak S_2\) is
\[
 O\left(e^{-1}\rho(.24/e)+\int_{.24/e}^\infty \rho(t)\,dt\right).
\]
This tends to zero by \(\int_0^\infty\rho=e^\gamma\) and the factorial tail. The prime boundary in the Vaughan identity is identical at both roughness cutoffs for large \(x\). The preceding bounds prove the claimed double limit. They do not estimate the absolute mass of discarded rows or treat output multipliers chosen from their factorization after shifting.

**Historical comparison.** Gold 4.63–4.66 combined papers (5.2) at line 6654 already prove the rough harmonic Dickman identity on a restricted native \(K\) annulus. The balanced-output lane retained \(x^{.12}\)-rough inputs only and explicitly left the nonrough inputs unpaid. Its calculation supplies the Dickman ingredient, not this complete original sharp sum comparison. My counterexample in sharp-collar-counterexample.md uses indicators built from the factorization of \(n-2\); it has no native uniform primitive-progression guarantee. A large absolute collar at some signs is compatible with cancellation in this signed total. No parity advantage or positive reserve is obtained here.

**Classical references.** Fundamental-lemma weights in Koukoulopoulos, Theorem 19.1. The normalization of the Dickman function in Lagarias, Theorem 3.5.1. [Sieve text](https://dms.umontreal.ca/~koukoulo/documents/publications/primes.pdf) and [Dickman normalization](https://www.ams.org/bull/2013-50-04/S0273-0979-2013-01423-X/S0273-0979-2013-01423-X.pdf).
