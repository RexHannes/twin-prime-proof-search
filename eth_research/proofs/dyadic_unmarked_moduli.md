# Absolute mean for all squarefree moduli in a small polynomial dyadic interval

Fix \(0<\kappa<1/1000\), \(L=\log x\), \(D=x^\kappa\), and let \(\mathcal D\) consist of all odd squarefree integers \(D<d\le2D\). For functions on \(p+2\) set
\[
M_d(F)=\sum_{\substack{x<p\le2x\\p\equiv-2\pmod d}}(\log p)F(p+2).
\]
As a consequence of the cited unconditional estimates in the Lü–Wang–Wu v2 preprint and classical distribution theorems,
\[
\sum_{d\in\mathcal D}|M_d(\mu)|=o_\kappa(x),\qquad
\sum_{d\in\mathcal D}M_d(1)\sim\frac{\log 2}{2}\,x .
\tag{1}
\]
This covers composite moduli having small prime factors, including moduli divisible by helper primes. No disjointness or roughness condition is imposed on \(\mathcal D\). In the earlier Gold 4.20 relative proper-divisor result the permitted moduli had \(P^-(d)>x^\alpha\) for fixed \(\alpha>0\). The present result gives no relative bound for an individual modulus of polynomial size. Each divisor here is proper and forces \(p+2\) composite.

## A group which is disjoint from a particular modulus

Use the signed sieve-polynomial estimate proved in polynomial-rough-holes.md, formula (1). Its Type I and Type II source proofs precede all final sieve brackets. For a single fixed group \(j\) of \(K\) disjoint LWW bands let \(E_j\) denote their prime union and \(W_j\) their usual nonnegative product weight at \(\rho=1/2\). Use \(K\) for a fixed saving \(A>3\). If \(d\) lacks every prime in \(E_j\), applying that estimate with row coefficients equal to the signs of \(M_d(\mu W_j)\) gives
\[
\sum_{\substack{d\in\mathcal D\\(d,\prod_{q\in E_j}q)=1}}
  |M_d(\mu W_j)|\ll_j xL^{-A}.
\tag{2}
\]
Indeed \(2D<x^{.001}\) eventually and each coefficient is supported away from the current group's own primes. For all moduli together the exact \(K\)-group union need not be avoided. Applied individually, (2) is uniform over bounded row coefficients, so they may depend on \(d\) and \(x\).

Here is the unsigned estimate for fixed disjoint groups, with \(H=1,W_j,W_jW_k\) (use \(j\ne k\) for the product). With \(|c_d|\le1\) supported on the moduli coprime to all helper primes occurring in \(H\), one has
\[
\sum_{d\in\mathcal D}c_dM_d(H)=x\,m_H
 \sum_{d\in\mathcal D}\frac{c_d}{\varphi(d)}+O_{A,H}(xL^{-A}).
\tag{3}
\]
The exact finite-\(x\) reduced-residue expectations \(m_H\) are \(1,m_j,m_jm_k\), respectively, with \(m_j\to 2^{K(\rho-1)}>0\). Truncate the label divisors to \(C_A\log L\) prime factors per band as in the cited polynomial estimate. Every folded modulus \(de\le x^{\kappa+o(1)}\) recovers \(d,e\) uniquely, by membership in the helper bands occurring in \(H\). Its coefficients are uniformly bounded. Ordinary prime Bombieri–Vinogradov bounds the retained discrepancy; Brun–Titchmarsh on each reduced progression and the factorial harmonic tail bound all absolute truncation errors. The harmonic cost of \(d\) is at most \(O(L)\), already absorbed by choosing the order sufficiently large. The local model factorizes exactly on these disjoint supports.

## The distribution of group avoidance amongst the moduli

For fixed disjoint \(E_j,E_k\) and \(E\) equal to either one group, their union, or the empty set, we claim
\[
\sum_{\substack{d\in\mathcal D\\q\nmid d\ \forall q\in E}}\frac1{\varphi(d)}
=\frac{\log2}{2}\prod_{q\in E}(1-1/q)+o(1).
\tag{4}
\]
Notice the \(1/q\), describing a random squarefree *modulus* with this harmonic weight. The density \(1/(q-1)\) in (3) describes divisibility of a *shifted prime* instead.

For squarefree odd \(h\) consisting of \(j\) primes of \(E\), with \(j\) fixed, \(h=x^{o(1)}\) and all its factors exceed \(\exp(L^{1/10})\). Put \(a(u)=\mu^2(u)u/\varphi(u)\), \(a_h(u)=a(u)\mathbf1_{(u,2h)=1}\). The convolution \(a_h=1*b_h\) has local coefficients \(b_h(q)=1/(q-1),\,b_h(q^2)=-q/(q-1)\) at \(q\nmid2h\), \(b_h(q)=-1\) at \(q\mid2h\), and zero on higher powers. Thus \(\sum |b_h(r)|r^{-3/4}\ll_j1\). Its value at \(s=1\) without absolute values is
\[
\sum_r b_h(r)/r
=\tfrac12\prod_{q\mid h}(1-1/q)=1/(2a(h)).
\]
The local factors at every \(q\nmid2h\) are exactly one. Summing the convolution by floors gives \(\sum_{u\le T}a_h(u)=T/(2a(h))+O_j(T^{3/4})\), including the tail beyond \(T\). Partial summation applied at \(T=D/h\) yields
\[
\sum_{\substack{d\in\mathcal D\\h\mid d}}1/\varphi(d)
=\frac{\log 2}{2h}
+O_j\!\left(\frac{a(h)}h (D/h)^{-1/4}\right).
\tag{5}
\]
For each fixed order, the sum of those errors is \(o(1)\), since \(D=x^\kappa\), \(h=x^{o(1)}\), \(a(h)=O_j(1)\) and \(\sum 1/h\) is bounded. To prove (4) sandwich the avoidance indicator between the two adjacent Bonferroni truncations at fixed orders \(J,J+1\). The harmonic difference is at most \((\sum_{q\in E}1/q)^{J+1}/(J+1)!\). Its numerator base is bounded for each fixed one- or two-group \(E\). Let \(x\to\infty\) at fixed \(J\), then \(J\to\infty\). The Euler product in (4) tends to \(\theta=2^{-K}\) for one group and \(\theta^2\) for two groups by Mertens. For \(E=\varnothing\) this gives the total divisor harmonic mass, which with (3) proves the second assertion of (1).

## A different subset of groups for each modulus

Now take a fixed number \(b\) of mutually disjoint \(K\)-band groups. For \(d\in\mathcal D\) let \(I(d)\) be the set of groups which have no prime factor in \(d\). From (4), the first and second moments of \(|I(d)|\) under the measure proportional to \(1/\varphi(d)\) tend to those of a binomial count with parameters \(b,\theta\). Pairwise moments suffice. Chebyshev gives
\[
\limsup_{x\to\infty}\sum_{\substack{d\in\mathcal D\\|I(d)|<b\theta/2}}
 \frac1{\varphi(d)}\ll_K b^{-1}.
\]
Equation (3) for \(H=1\) shows that these exceptional moduli contribute at most \(O_K(x/b)+o_b(x)\) to the sum of absolute signed rows.

For the other moduli set \(G_d=|I(d)|^{-1}\sum_{j\in I(d)}W_j/m_j\). Inequality (2) bounds \(\sum_d|M_d(\mu G_d)|\ll_b xL^{-A}\). For the variance, expand \((G_d-1)^2\), applying (3) separately for each fixed \(j\) and ordered \(j\ne k\) with the appropriate \(d\)-dependent coefficients. When that coefficient is nonzero, \(d\) avoids exactly the groups needed in (3). The off-diagonal terms have product mean; the diagonal bound \(W_j^2\ll_{K,\rho} W_j\) applies on the actual positive prime measure. The constants in the pointwise diagonal bound and the limiting reciprocal means can be taken independent of the group. Thus
\[
\sum_{\text{nonexceptional }d} M_d(|G_d-1|^2)
\ll_K x\sum_d \frac{1}{\varphi(d)}\,\frac{2}{b\theta}+o_b(x)
\ll_K x/b+o_b(x).
\]
Cauchy–Schwarz over all pairs \((d,p)\), with the same positive measure and total mass \(O(x)\), bounds the residual unmarked rows by \(O_K(x/\sqrt b)+o_b(x)\). Sending \(x\to\infty\) first and then \(b\to\infty\) proves (1). No individual theorem on a growing tuple, nor an individual polynomial-modulus prime theorem, has been invoked.

**Sources and status.** This is a paper deduction from the v2 preprint's unconditional estimates, not an independent verification of its deep internal dispersion theorem. See Lü, Wang and Wu, §§2–5, https://arxiv.org/html/2610.20242v2. Equation (2) uses the separately derived marked divisor-polynomial lemma. The proof supplies no prime lower bound, since even a positive incidence in these rows has a divisor \(d>1\).
