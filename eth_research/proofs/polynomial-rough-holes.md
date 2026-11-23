# A polynomial roughness cutoff with finitely many exceptional bands

**Claim ETH-PERF-01.** Analytic deduction from the stated unconditional second-moment estimates of Lü–Wang–Wu's November 19, 2026 preprint (v2) and classical sieve theorems. No independent reproof of that preprint's internal spectral estimate or Lean verification is claimed. The result quantifies cancellation on a prime-input population of weighted order \(x/\log x\). Its fixed exceptions are essential.

## Statement

For each \(\varepsilon>0\) there are fixed \(0<\beta<.001\), a positive integer \(H\), and pairwise distinct fixed \(a_1,\ldots,a_H\in(1/10,1/5)\) with the following properties. Set \(L=\log x\), \(z=x^\beta\). Allow the primes in the union
\[
 E_x=\bigcup_{i\le H}\{q:\exp(L^{a_i})<q\le\exp(2L^{a_i})\}.
\]
Let \(R(n)\) indicate that no odd \(q\le z\) outside \(E_x\) divides \(n\), and put \(V=\prod_{2<q\le z,\ q\notin E_x}(1-1/(q-1))\) with prime indices. Give the genuine primes \(x<p\le2x\) weight \(\log p\), and write \(M(F)=\sum_p(\log p)F(p+2)\). Then
\[
 \limsup_{x\to\infty}\left|\frac{M(R)}{xV}-1\right|\le\varepsilon,\qquad
 \limsup_{x\to\infty}\frac{|M(\mu R)|}{xV}\le\varepsilon,\qquad
 V\sim\frac{2^{H+1}e^{-\gamma}C_2}{\beta L},
\]
where \(C_2=\prod_{q>2}(1-1/(q-1)^2)\). Consequently each squarefree Möbius sign has mass within \(\varepsilon xV+o(xV)\) of \(xV/2\). The parameters \(H,\beta\) can depend on the requested accuracy; a fixed-source \(o(xV)\) estimate is not established.

### The signed sieve-polynomial estimate

Set \(D=x^{.001}\). Let \(|l_d|\le1\) be arbitrary and supported on squarefree odd \(d\le D\) with no prime factor in the \(H\) bands. Define \(S(t)=\sum_{d\mid t}l_d\). For a family of \(K\) of these bands use the LWW auxiliary weight \(W=\prod_i\omega_i\rho^{\omega_i-1}/V_i\), where \(\rho=1/2,\ V_i=\sum_{q\in\mathcal P_i}1/q\). For any prescribed \(A\), choose \(K\) for sufficiently strong logarithmic saving in LWW's Proposition 4.2 and §§4–5. Its \(K\) is independent of the fixed band exponents. Then, uniformly in the displayed divisor coefficients,
\[
  M(\mu W S)\ll_{A,\rho,K,\mathbf a}xL^{-A}. \tag{1}
\]
The argument below records the changes to the source proof, since (1) cannot be imported by multiplying the final HLC conclusion by \(S\).

**Type I.** Use the sifted Vaughan decomposition in LWW Proposition 2.1, with their input presieve \(Z\) and \(U=V_{\rm Vaughan}=x^{1/5}\). Its correction is \(x^{o(1)}\), since the factors besides \(S\) are bounded and \(|S|\le\tau=x^{o(1)}\) at these arguments. The prime-power replacement has error \(x^{1/2+o(1)}\). Follow LWW §3. Include \(l_d 1_{d\mid qk+2}\) first, and truncate the input \(R_Z(k)\) and each output label factor after \(J=\lceil C\log L\rceil\) primes. The input positive Bonferroni error is supported at order \(J+1\); its harmonic coefficient norm is \(O_B(L^{-B})\) on choosing \(C\) large. A single label factor has retained coefficient \(j(\rho-1)^{j-1}/V_i\) on a product of \(j\) distinct band primes and absolute Taylor remainder bounded by \((J+1)\binom{\omega_i}{J+1}/V_i\). Its harmonic norm of the error is again \(O_B(L^{-B})\) by bounded band harmonic mass. In replacing one factor at a time the other already expanded factors have absolute harmonic norm \(L^{O(1)}\), and the exact unexpanded factors are bounded. The extra \(l_d\) costs \(\sum_{d\le D}1/d\ll L\).

Fold the labels and \(d\) to \(d_1\). A divisor has a unique decomposition because only the labels have primes in these disjoint bands. The retained \(|l'_{d_1}|\ll_{K,\rho}1\), \(d_1\le x^{.001+o(1)}\), and \(\sum |l'_{d_1}|/d_1\ll L^{O(1)}\). Input presieve divisors \(r\mid k\) are \(x^{o(1)}\). The progression for \(k\) at modulus \(r d_1\) is empty unless \((d_1,2qr)=1\). Its count is \(O(x/(qr d_1)+1)\), for the Vaughan modulus \(q\le x^{2/5}\). The \(+1\) terms for each positive truncation error cost \(x^{.401+o(1)}\), since even its support is of the same size. This proves an arbitrarily large log saving for the truncation after summing the original \(|\varpi_q|\le L\).

For squarefree \(d_1\), remove it from the Möbius argument by the exact divisor identity LWW (3.7). Write \(qrj+2=d_1at\) where the primes of \(a\) divide \(d_1\). For \(d_1a\le x^{1/20}\), \(t\) has a primitive progression mod \(2qr\le x^{2/5+o(1)}\) and length parameter \(\asymp x/(d_1a)\gg x^{19/20}\). The maximal divisor-weighted Möbius Bombieri–Vinogradov estimate used in LWW (3.8) gives any desired log saving after summing over \(q,r\). The remaining harmonic cost is \(\sum |l'_{d_1}|/d_1\prod_{s\mid d_1}(1-1/s)^{-1}\ll L^{O(1)}\). For \(d_1a>x^{1/20}\) we have \(a>x^{1/25}\) eventually. For each \(d_1\),
\[
 \sum_{\substack{a>x^{1/25}\\s\mid a\Rightarrow s\mid d_1\ (s\ {\rm prime})}}\frac1a
 \le x^{-1/50}\prod_{s\mid d_1}(1-s^{-1/2})^{-1}
 =x^{-1/50+o(1)}.
\]
The number of such supported \(a\le3x\) is \(\le(3x)^{1/20}\prod_{s\mid d_1}(1-s^{-1/20})^{-1}=x^{1/20+o(1)}\). Both \(o(1)\) exponents are uniform since \(\omega(d_1)=O(L/\log L)\), by the elementary factorial bound on products of distinct primes. Count the progression trivially \(O(x/(d_1aqr)+1)\). Its two parts cost \(x^{49/50+o(1)}\) and \(x^{.4+.001+.05+o(1)}\). Thus both Type I terms have arbitrary-log savings, also after partial summation for the logarithm.

**Type II.** After the label extraction \(mn+2=th\), every prime in \(t\) is excluded from every \(d\) in \(S\). Hence \(S(th)=S(h)\). In LWW (4.6), Cauchy now uses
\[
  \sum_{h\ll X/Y}|S(h)|^2\le\sum_{h\ll X/Y}\tau(h)^2\ll(X/Y)L^3,
\]
where \(X=MN\asymp x\) and the label product \(Y=x^{o(1)}\). The second factor \(Q_Y\), including the character–Mellin coefficients in §5, is unchanged. Its arbitrary-log saving absorbs the extra \(L^3\).

For the step preceding (4.5) that removes repeated labels, the bad \(s=mn+2\) have a square factor from a prime \(>\exp(L^{1/10})\). There are \(O(x\exp(-L^{1/10})+\sqrt x)\) such integers. Counting pairs \(mn\) costs \(\tau(s-2)\); counting label tuples costs at most \(\tau(s)\) since their distinct products divide \(s\). Also \(|S(h)|\le\tau(s)\), and the Vaughan coefficient costs \(O(L)\). Cauchy and log-power bounds for fixed moments of divisor functions, with Hölder on the two shifts, make the total \(O_B(x L^{-B})\) for every fixed \(B\). At the product-window approximation in (4.1)–(4.4), the same argument with a collar of \(O(xL^{-B_0}+1)\) integers gives \(O(xL^{C-B_0/2})\) with some fixed \(C\). Choose \(B_0\) sufficiently large first. The Mellin tails are absorbed with stronger log precision by \(\sum_{s\ll x}\tau(s)\tau(s-2)\ll xL^{O(1)}\). These estimates also justify the decomposition after introducing a divisor-polynomial weight with no pointwise constant bound. Equations (4.8), (5.31)–(5.33) now give (1).

### Bracketing only on the positive prime measure

Apply Koukoulopoulos, *The Distribution of Prime Numbers*, Theorem 19.1, to the odd sieve primes \(q\le z\) outside \(E_x\), local density \(g(q)=1/(q-1)\) and level \(D\). This is a dimension-at-most-one system with constants uniform in the omitted set, since on every prime interval its inverse Euler product is bounded above by the full odd product. It yields divisor polynomials \(S^-\le R\le S^+\) of the above kind, and
\[
 V^\pm=\sum_d l_d^\pm/\varphi(d)
   =(1+O(\delta_s))V,\qquad s=.001/\beta,\qquad \delta_s=s^{-s/2}
\]
for sufficiently large \(s\), with a uniform dimension-dependent implied constant.

Let \(J_0\) be 1, one auxiliary product \(W_j\), or a product \(W_iW_j\) of disjoint groups. Its local expectation \(m_{J_0}\) on reduced residues is given by LWW (2.14), with \(m_1=1\) and \(m_{W_iW_j}=m_i m_j\). The actual primes satisfy
\[
 M(S^\pm J_0)=xV^\pm m_{J_0}+O_{A,b,K}(xL^{-A}). \tag{2}
\]
Expand the label factors to order \(C\log L\) as in the Type I calculation, keeping the sieve coefficients. Their prime supports are disjoint; the folded modulus is \(\le x^{.001+o(1)}\), has one representation and bounded coefficient. Ordinary prime Bombieri–Vinogradov controls all retained errors. For each positive truncation error, Brun–Titchmarsh gives \(O(x/\varphi(d_1))\) in its reduced class \(-2\bmod d_1\). The extra sieve factor costs only \(\sum_{d\le D}1/\varphi(d)\ll L\). The same absolute estimates hold in the independent local divisibility model. Factoring the local mean gives the right side of (2).

For \(b\) disjoint groups of \(K\) bands define \(G=b^{-1}\sum_jW_j/m_j\), and let the hole set consist of precisely these \(H=bK\) bands. From (1), (2), \(W_j\ge0\), and \(0\le R-S^-\le S^+-S^-\),
\[
 |M(\mu R W_j)|\le |M(\mu S^- W_j)|+M((S^+-S^-)W_j)
       \le O(\delta_s)m_j xV+o(xV).
\]
Bounding \(M(R)\), \(M(RW_j)\), and the off-diagonal \(M(RW_iW_j)\) by (2) gives relative errors \(O(\delta_s)+o(1)\). As \(W_j^2\ll_{K,\rho} W_j\) and \(m_j\to2^{K(\rho-1)}>0\),
\[
 M(R|G-1|^2)\le\big(C_{K,\rho}/b+O_{K,\rho}(\delta_s)+o_{b,s}(1)\big)xV.
\]
Cauchy on this same positive measure and the preceding signed estimate prove the stated bounds after choosing first \(K,\rho\), then \(b\), then sufficiently large fixed \(s\), then \(x\to\infty\). All these choices precede the limit. Mertens' theorem and the disjoint band harmonic sums yield the formula for \(V\). Every prime factor of a retained \(p+2\) exceeds \(\exp(L^{1/10})\) for large \(x\), so repeated prime factors contribute \(o(x/L)\) by the same elementary square-divisor count. Decomposition into the two signs follows.

### Why the fixed exceptions remain load-bearing

All genuine twins survive. The subpopulation on which \(p+2\) has no prime factor in any exceptional band also contains every polynomially rough odd composite of the required mask. On that unperforated subpopulation, every \(W_j\) is identically zero. Each computed \(O(\delta_s)\) or \(O(b^{-1/2})\) bound refers to \(xV\), with coefficient of order \(2^{bK}/\beta\) in units of \(x/L\). The source contains odd composites, including marked odd composites, and the argument supplies no lower bound for twins after charging them. Increasing \(b\) changes the population, even though the scale \(x/\log x\) stays fixed. The complete terminal effect is zero.

**Primary references:** Lü, Wang and Wu, *On the Hardy–Littlewood–Chowla conjecture*, v2, §§2–5, especially Proposition 4.2 and (3.7), (3.8), (4.6), (5.33). [Preprint](https://arxiv.org/html/2610.20242v2) Koukoulopoulos, *The Distribution of Prime Numbers*, Theorem 19.1. [Author text](https://dms.umontreal.ca/~koukoulo/documents/publications/primes.pdf)
