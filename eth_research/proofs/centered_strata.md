# Centering finite small-factor populations

Let \(X=x/2,\ L=\log x,\ U=x^t,\ H=x^{1/2-\eta},\ z=x^e\), where \(0<\eta<1/6\) is fixed. Fix any positive integer \(J\) before taking \(t\) sufficiently small. Choose \(0<e<t\). Write \(S(k)=\{p:p\mid k,\ p\le U\}\) and \(m(k)=\#\{p\mid k:U<p\le H\}\). Use the original angular profiles \(f_\pm\) and the deterministic densities \(d_\pm=\mathfrak S_2\Pi(f_\pm)/L\). All costs use the same dyadic \(S_b\). The positive- and negative-channel coefficients are \(B-P\) and \(B^\dagger\) from higher_rank_charge. The lower cutoff \(e\) is fixed before \(x\to\infty\) and may subsequently be chosen small depending on \(t\).

For every fixed \(1\le r\le J\), the arithmetic statement is
\[
\lim_{t\downarrow0}\ \sup_{0<e<t}\ \limsup_{x\to\infty}
\frac{\left|\sum_{\substack{k+2\in I_x,\ R_z(k)\mu^2(k)=1\\|S(k)|=r}}
\left[(f_+(k+2)-d_+)(B-P)(k)-(f_-(k+2)-d_-)B^\dagger(k)\right]\right|}{S_b}=0.
\tag{1}
\]
The same conclusion holds on finitely many angular subregions in the \(r\) short-prime logarithms, cut out by fixed affine faces. Finite extra conditions on the presence or absence of specified prime bands with endpoints between \(U\) and a fixed power \(U^C\) are permitted. At fixed \(r,C,\eta\), \(t\) is taken sufficiently small before the other limits.

## The named short primes

On any such fixed positive rank the true prime-input term is zero, since a prime input in the dyadic window has no prime factor \(\le U\). Write \(s=\prod_{p\in S}p\). The remaining coefficient depends on the \(r\) named primes and at most one additional prime label for \(m\). Its normalized logarithmic factors \(\log k/L,\log s/L,\log(k/(pq))/L\) are bounded. The associated sharp profile factors are
\[
M(S)=\sum_{A\subseteq S}(-1)^{|A|}1_{\sum_{p\in A}u_p\le1},\qquad
1_{u_p+u_q>1}M(S\setminus\{p,q\}),\quad u_p=\log p/\log U .
\]
Their absolute integrals in \(\prod du_i/u_i\) over \([e/t,1]^r\) have an upper bound depending only on \(r\), even as \(e/t\downarrow0\). For the first kernel at rank \(r\ge2\), fix the smallest \(u\). If the signed difference is nonzero, some subset of the other coordinates has sum in \((1-u,1]\). For \(u<1/2\) at least one such coordinate is \(\ge1/(2r)\) and, once the others are fixed, lies in an interval of length \(u\). Integrating the other coordinates above \(u\) gives the convergent bound \(O_r(\int_0^{1/2}(1+\log(1/u))^{r-2}du)\); the region of larger minimum is compact. At rank one the sharp kernel is zero on this interval and rank zero is a constant. For the marked pair term the pair condition has harmonic mass \(\int_0^1-\log(1-u)du/u=\pi^2/6\), and the other coordinates have the preceding bound. At each fixed \(e,t\), prime harmonic sums of the kernels and their absolute values tend to these integrals by Mertens and finite polyhedral approximation. Their ranks are fixed and repeated labels have vanishing mass.

To force the named primes \(S\) to be exactly the prime set below \(U\), impose \(\prod_{p\in S}p\mid k\) and sieve the cofactor against all primes \(\le U\). This excludes a square of any named prime, which is permitted after the squarefree input payment. If a medium label \(\ell\) is named, divide it out too. Prescribed occupancy of finitely many optional bands is expanded by inclusion–exclusion of their absence. Any sieving term forbidding its own named \(\ell\) gives zero and is dropped before treating its cofactor. The distinct input prime labels in each kernel are aggregated with at most a fixed polylogarithmic multiplicity. Split signed profiles and coefficients into nonnegative parts before using upper/lower sieve polynomials.

Use a fundamental sieve level \(x^{\eta/4}\). Its prime set ends at \(U\), or \(U^C\) with optional bands. The combined modulus is at most \(x^{1/2-\eta+rt+\eta/4}\), strictly inside the native finite-rank primitive progression theorem for \(t\) small. The corresponding ordinary-integer discrepancies have power savings by elementary floor counts at the same moduli, even with the polylogarithmic label multiplicities. The primitive collision correction for \(f_\pm\) is \(O(x^{-\delta}L^c)\) per output after absolute harmonic summation, since all their prime factors exceed \(x^\delta\). A shared prime between the named product and the cofactor sieve costs \(O_{e,t}(x^{-e}L^c)\) per output. Squareful inputs in the exact \(z\)-rough populations cost \(O_{e,t}(x^{1-e}L^c)\) after all fixed label and log factors.

In the native profile model every odd sieve prime \(p\) has density \(1/(p-1)\); the prime 2 is absent. In the ordinary model the local density is \(1/p\), including parity. The full product ratio at \(U\) tends to \(\mathfrak S_2\), the forced local reciprocals differ by \(1+o_{e,t}(1)\), and optional sieve bands above \(U\) have ratio \(1+o_t(1)\). Finally \(\sum f_\pm=\Pi(f_\pm)X/L+o(X/L)\) and \(\log k=L+O(1)\). Thus the two leading terms, one weighted by \(f_\pm\) and one by \(d_\pm\), agree up to \(o_{e,t}(S_b)\). Their combined upper/lower-sieve errors are
\[
O_{J,C,f}\!\left(\frac{1+\log(1/t)}{t}E_{\eta/(4Ct)}\right)S_b+o_{e,t}(S_b),\qquad
E_u\ll u^{-u/2}.
\]
The positive harmonic norms in the preceding paragraph provide the uniformity in \(e/t\) of the leading error bound. The factor \(\log(1/t)\) permits the full additional \(\ell\)-sum through \(H\). This proves (1). In particular the large physical debit in higher_rank_charge can be paid on its own event after centering. This comparison carries a matching, also large ordinary term.

## Direct proof over every nonempty small set together

The root's stronger complete calculation avoids any interchange in \(r\). Form \(\widetilde B,\widetilde B^\dagger\) by deleting \(1_{\mathbb P}(k)\log k\) from the two true coefficient definitions for every \(k\), and retain the pair correction. On the actual source with \(S(k)\ne\varnothing\), this deletion is exact. The selector on this source is \(R_z(k)-R_U(k)\). On **every** \(k\) the two prime-deleted coefficients consist of the fixed short-divisor expressions
\[
M_s(U)=\sum_{d\mid k,\ d\le U}\mu(d),\quad
\log s=\sum_{\substack{p\mid k\\p\le U}}\log p,\quad
m=\sum_{\substack{\ell\mid k\\U<\ell\le H}}1
\]
and the explicit pair probe. After bounded squareful removal the formulas may be used on arbitrary integers to evaluate both sieve sides. The products \(\log s\,M_s\) fold at \([p,d]\le U^2\). In the shared \(p\mid d\) case their total weight is bounded by \(\sum_{p\mid d}\log p\le\log d\), preventing an extra logarithmic loss. In \(m M_s\), \(\ell>U\ge d\), hence the combined modulus \(\ell d\le HU\) has no \(\ell,d\) collision. In the pair probe \(m_0\mid k/(pq)\) means that the true modulus is \(pqm_0\le U^3\), also when a prime divides both. Grouping all labels costs at most a fixed log power on the progression errors. On \(R_z\) the seed modulus \(d_0\) has primes \(>z\); the sieve divisor \(c\) from the remaining cofactor has primes \(\le z\), so they fold uniquely after this first grouping.

The native and ordinary seed reciprocals differ by \(1+O(L/(z\log z))\), and \(g'_z/V_z\to\mathfrak S_2\) because of parity. The sums of the absolute seed weights, after division by the single explicit logarithm \(L\), are bounded at fixed \(t\) by a polynomial in \(1/e,\ 1+\log(t/e)\). This follows from \(\sum_{d\le U,R_z(d)=1}1/\varphi(d)\ll t/e+1\), the named prime harmonic sums, and the shared-prime bound above. For a shared factor of \(pqm_0\), \(1/\varphi(pqm_0)\le1/(\varphi(pq)\varphi(m_0))\) remains sufficient. The level \(x^{\eta/4}\) therefore gives a normalized total comparison error tending to zero as \(e\downarrow0\) at fixed sufficiently small \(t\).

On \(R_U\) the prime-deleted pair of coefficients is simply \(-\log k\) and \((m-1)\log k\); \(P=0\). Its analogous normalized comparison error is \(O_f((1+\log(1/t))E_{\eta/(4t)}/t)+o_t(1)\). Subtracting the two comparisons proves
\[
\lim_{t\downarrow0}\limsup_{e\downarrow0}\limsup_{x\to\infty}
\frac{\left|\sum_{\substack{k+2\in I_x,\ R_z(k)\mu^2(k)=1\\|S(k)|\ge1}}
\left[(f_+-d_+)(B-P)-(f_--d_-)B^\dagger\right]\right|}{S_b}=0.
\tag{2}
\]
No full-source signed identity is used in evaluating this nonempty-set contribution.

The distinction at \(S=\varnothing\) is exact. The same \(R_U\) calculation pays its prime-deleted portion, but the genuine numerator still contains \(\sum_{k\ {\rm prime}}\log k[f(k+2)-(d_+-d_-)]\), shared by the two channels with the original signs. After ordinary PNT this is \(A(f)-\mathfrak S_2\sum f+o(S_b)\), the original complete prime-profile covariance. Equations (1)–(2) leave the canonical positive twin-prime reserve open.
