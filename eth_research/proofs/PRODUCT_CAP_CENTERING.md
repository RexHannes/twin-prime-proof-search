# Centering the physical source at a cap on the product of its small factors

Let $f=\Phi-\psi=f_+-f_-$ be the actual outside output profile, $L=\log x$, $k=n-2$ and $\lambda=\log k$. We use its original fixed primitive progression estimate with a common prefix separately for $f_\pm$, its bounded polynomially rough output support, and $S_b\sim\mathfrak S_2x/(2L)$. Let $C_w(f)$ denote the original sharp signed outside sum. The transfer proved in the polynomial-presieve and simultaneous-core packets applies to the retuned $U=V=x^t$, $D=U^2$ and the centered large-owner measurement, whenever its fixed level remains below $1/2$.

Fix $0<t<\theta$ with $\theta+2t<1/6$. Put
$$
Y=x^\theta,\qquad H=x^{1/2-\theta-2t},\qquad U=x^t,
\qquad z=x^e,\quad 0<e<\min(t,\zeta).
$$
For a squarefree input $k$ let $S=\{p\le U:p\mid k\}$, $q_A=\prod_{p\in A}p$ for $A\subseteq S$, $s=q_S$, and $m=\#\{U<p\le H:p\mid k\}$. Set
$$
M(S)=\sum_{\substack{A\subseteq S\\q_A\le U}}(-1)^{|A|},\qquad
B=1_{\mathbb P}(k)\lambda-(\lambda-\log s)M(S),\qquad
D=1_{\mathbb P}(k)\lambda+[(m-1)\lambda+\log s]M(S).
$$
These expressions keep the exact prime boundary and satisfy the full native transfer for $f_+B-f_-D$. The lowered $H$ leaves extra room for divisor tags.

## All configurations of small-part product at most $Y$

For functions of finite sets of distinct small primes write
$$
(v_1*v_2)(A)=\sum_{D_0\subseteq A}v_1(D_0)v_2(A\setminus D_0)
$$
and let $\delta$ be one at the empty set and zero elsewhere. Define $N=M^{-1}$ for this convolution. It exists because $M(\varnothing)=1$. Put
$$
C_0=\delta-N,\qquad C_1=((\log q)M)*N,\qquad
P_i(S)=\sum_{\substack{A\subseteq S\\q_A\le Y}} C_i(A)M(S\setminus A).
$$
The argument $\log q$ in $C_1$ is the set function $A\mapsto\log q_A$. In particular both $C_i$ vanish at the empty set. Define the new physical coefficient
$$
 Z=f_+[B+\lambda P_0-P_1]
     -f_-[D-(m-1)\lambda P_0-P_1].
$$
Write $\mathcal Z(E)=\sum_{x/2<n\le x}\mu^2(k)R_z(k)1_E Z$. Then
$$
 \lim_{e\downarrow0}\limsup_{x\to\infty}
  \frac{|C_w(f)-\mathcal Z(\text{all})|}{S_b}=0
 \tag{1}
$$
at each fixed $(t,\theta)$. For every $1<s\le Y$ one has $Z=0$ exactly. The entire $s=1$ sector, including its true prime inputs, is retained unchanged.

Indeed $C_0*M=M-\delta$ and $C_1*M=(\log q)M$. For $s\le Y$ the product cutoff retains every subset needed in these identities. The two channels become $[1_{\mathbb P}(k)-\delta(S)]\lambda$ and $[1_{\mathbb P}(k)+(m-1)\delta(S)]\lambda$, respectively. At $s=1$ and input rank at least three, $m\ge1$ since $H>x^{1/3}$ with fixed slack. Thus both signed contributions there are nonpositive. The possible adverse semiprimes at $s=1$ have both factors $>H$ and cost $O_f(\theta+t)S_b+o_{t,\theta}(S_b)$ by the two-form upper sieve as in the simultaneous-core proof.

Here are the uniform costs needed to justify (1). A nonempty block at which $M$ is nonzero must have product $>U$, by full Möbius cancellation at product $\le U$. On $q_A\le Y$ the Neumann expansion of $N=\sum_{j\ge0}[-(M-\delta)]^{*j}$ therefore has at most $K_0=\lfloor\theta/t\rfloor$ nonempty blocks. Since $|M(A)|\le2^{|A|}$ and ordered partitions among $j$ labeled blocks number at most $j^{|A|}$, there is a constant $C_{t,\theta}$ such that
$$
 |C_0(A)|+L^{-1}|C_1(A)|
 \le C_{t,\theta}(2K_0+2)^{|A|}\qquad(q_A\le Y).
$$
On $R_z$, the absolute harmonic sum of this majorant over all tag sets is
$$
 \ll_{t,\theta}\prod_{z<p\le U}
     \left(1+\frac{2K_0+2}{p-1}\right)
 \ll_{t,\theta}(t/e)^{2K_0+2}
$$
in the large-$x$ limit at fixed $e$. Removing $\mu^2$ during the fold costs $o_{t,\theta,e}(S_b)$. A nonsquarefree $z$-rough input has a repeated prime $>z$, their count is $O(x/z+\sqrt{x})$, and at fixed $e$ every input has $O_e(1)$ divisors on this support.

Expand each prefix with squarefree $d\le U$, $(d,q_A)=1$ and, in the $m$ term, name its one prime $\ell\in(U,H]$. These coprimalities can be imposed before expanding the squarefree indicator. The initial modulus $q_A d$ or $\ell q_A d$ is $\le HYU=x^{1/2-t}$. Every prime of this modulus exceeds $z$. Sieve the remaining input cofactor by primes $\le z$ with upper/lower fundamental-lemma weights of level $x^{t/2}$. The product remains below $x^{1/2-t/2}$. All bounded-profile progression discrepancies are $o_{t,\theta,e}(S_b)$ after the finite label multiplicities and at most one common $\log k$ have been allowed. For fixed $e$ there are at most $1/(2e)$ prime factors in any folded initial modulus. The fundamental-lemma relative error $E(t/(2e))\ll (t/(2e))^{-t/(4e)}$ as $e\downarrow0$ is charged against the *absolute ungrouped harmonic sum* above, times $O_t(e^{-2})$: $\sum_{d\le U}R_z(d)/\varphi(d)\ll 1/e$, $g_z L\ll1/e$ and $\sum_{U<\ell\le H}1/(\ell-1)\ll_t1$. Here $g_z=\prod_{2<p\le z}(1-1/(p-1))$. The implied fundamental-lemma constant is independent of $e$ at fixed $t$.

For the signed principal, after the factors $1/\varphi(q_A)$ and, when present, $1/(\ell-1)$, the inner harmonic Euler prefix is
$$
 \sum_{\substack{d\le U\\(d,2nq_A\ell)=1}}
   \frac{\mu(d)R_z(d)}{\varphi(d)}
   =\rho(t/e)+o_{t,e}(1).
$$
Omit $\ell$ when absent. Uniformity at fixed $e$ follows from the polynomial-Möbius-prefix proof and the bounded number of excluded primes $>z$, each of reciprocal size $o_e(1)$. The condition $(q_A\ell,n)=1$ can be dropped only in our absolute estimate of this signed principal. Its normalized magnitude is $\ll_{t,\theta}(t/e)^{2K_0+2}\rho(t/e)/e+o_{t,\theta,e}(1)$. Dickman factorial decay and the fundamental-lemma error overcome these fixed powers of $1/e$. This proves the negligibility of all added probes in (1), after applying the original retuned transfer. No uniform in $e$ constant was extracted from the fixed-$e$ progression discrepancy.

## What the remaining product region actually carries

For $\theta=\sqrt t$ and $t$ sufficiently small, let $Q_{t,e}(x)=\mathcal Z(s>Y)$. The full signed sum of this region has the following ordered-limit estimate:
$$
 \lim_{t\downarrow0}\limsup_{e\downarrow0}\limsup_{x\to\infty}
 \left|\frac{Q_{t,e}(x)}{S_b\,t^{-1}\log(1/t)}
        -e^{-\gamma_E}\Pi(f_-)\right|=0.              \tag{2}
$$
All favorable and adverse terms in the region are included. In particular an absolute small bound on this region in the displayed representation is impossible. The ordinary weighted population has a two-sided large-deviation estimate. Write $K=\theta/t=t^{-1/2}$ and define
$$
 p_{t,\chi}(x)=
 \frac{\sum_{x/2<n\le x}|f_x(n)|\,\chi(k)1_{s>x^\theta}}
      {\sum_{x/2<n\le x}|f_x(n)|\,\chi(k)},
 \qquad \chi=1\ \ \text{or}\ \ \chi=R_z\mu^2 .
$$
For $\chi=1$ take the upper and lower limits as $x\to\infty$. For $\chi=R_z\mu^2$ take the successive upper and lower limits first as $x\to\infty$, then as $e\downarrow0$. Every resulting probability $p(t)$ satisfies
$$
\log p(t)=-K\big(\log K+\log\log K-1+o(1)\big)
\qquad(t\downarrow0).                                \tag{3}
$$
For the unmasked probability define $s$ on all inputs as the product of their distinct prime divisors at most $U$.

For (2), the entire $s=1$ sector is independent of $e<t$ and equals
$$
 A(f)-\sum_n R_U(k)\mu^2(k)\lambda[f_x(n)+m f_{-,x}(n)].
$$
This identity returns the true genuine-prime boundary exactly. For $t<\zeta$ all output factors exceed $U$. For the sums over $R_U$ use a two-sided dimension-one sieve of level $x^{\theta/3}$. The same sieve works after a marked $\ell\in(U,H]$, since $H x^{\theta/3}<x^{1/2-2\theta/3}$. The unique large prime $\ell$ gives an injective fold with the sieve divisor. Coprime exclusions $\ell\mid n$ have total reciprocal weight $O_f(x^{-\zeta})$ per output. The Euler means are $g_U$ and $g_U P$, respectively, where
$$
 P=\sum_{U<\ell\le H}\frac1{\ell-1}
   =\log((1/2-\theta-2t)/t)+o_t(1).
$$
The relative sieve error for each positive profile is $O(E(\theta/(3t)))+o_t(1)$, and signed errors charge $|f|$. The squareful removal costs $o_t(S_b)$. Replacing $\lambda$ by $L$ costs $o_t(S_b)$ since the weighted sums of the positive profiles without $\lambda$ are $O_t(S_b/L)$. Subtract the exact $s=1$ value from (1) and use $C_w(f)=A(f)-\mathfrak S_2\sum f+o(S_b)$; the prime terms cancel. Mertens gives $L g_U\to\mathfrak S_2e^{-\gamma_E}/t$ at fixed $t$. Since $P/\log(1/t)\to1$, $\sum f_-/S_b\to\Pi(f_-)/\mathfrak S_2$ and $E(\theta/(3t))\to0$, (2) follows. Positivity of $\Pi(f_-)$ follows, for example, on a compact inside the balanced three-prime output chamber with $f=-2$.

For (3), put $X_s=\log s/\log U$, $\lambda_0=\log K+\log\log K$ and $J=\lfloor K\lambda_0\rfloor$. At each fixed small $t<\zeta$, $Jt<.49$ since $tJ=O(\sqrt t\log(1/t))$. In the expansion of $X_s^J$, the product of all distinct odd marked primes is therefore $\le U^J<x^{.49}$. Its collected coefficients are nonnegative and $O_J(1)$, since a fixed modulus has at most $J$ primes and each mark has weight $\log p/\log U\le1$. The progression estimate for $|f|$ identifies its normalized $J$th moment, up to $o_t(1)$, with the $J$th moment of $X^*=\sum_{2<p\le U}(\log p/\log U)\xi_p$, where the independent $\xi_p$ take value one with probability $1/(p-1)$. The coprimalities are automatic at $t<\zeta$. The positive mean of $|f|$ is bounded below by that of $f_-$.

By the Euler product and the logarithmic Mertens estimate, at fixed $t$,
$$
 \mathbb E e^{\lambda_0 X^*}
 \le\exp\!\left(\sum_{2<p\le U}
  \frac{e^{\lambda_0\log p/\log U}-1}{p-1}\right)
 = \exp\!\left(\int_0^{\lambda_0}\frac{e^v-1}{v}\,dv+o_t(1)\right).
$$
The convergence at the lower endpoint uses $e^{\lambda_0 u}-1=O_t(u)$ and $\sum_{p\le U^\delta}\log p/(p-1)\ll\delta\log U+1$. The integral is $(1+o(1))e^{\lambda_0}/\lambda_0=(1+o(1))K$ as $t\downarrow0$, by l'Hôpital's rule. Markov's inequality and $(X^*)^J\le J!\lambda_0^{-J}e^{\lambda_0X^*}$ bound the limsup probability by $J!(K\lambda_0)^{-J}\exp((1+o(1))K)$. Stirling's formula and $J=\lfloor K\lambda_0\rfloor$ yield (3).

For the matching lower bound use the band's prime exponents $u=\log p/\log U$ in $(1/2,1]$. Its unforced reciprocal prime mass is $\log2+o_t(1)<1$. Choose $\lambda_*>0$ by
$$
 G=\int_{1/2}^1 e^{\lambda_*u}\,du=K+K^{2/3},\qquad
 A=\int_{1/2}^1 e^{\lambda_*u}\frac{du}{u},\qquad r=\lfloor A\rfloor .
$$
Then $\lambda_*=\log K+\log\log K+o(1)$, $A=(1+o(1))K$ and $(r+1)t=o(1)$. Sum the indicators of all unordered $r$-element prime sets in the band for which $\sum_i u_i>K$ and all $r$ labels divide $k$. For each such tuple subtract the multiplicity obtained by labeling one additional distinct band prime dividing $k$. The resulting quantity is a lower bound for the event in (3): it is one on the prescribed configurations of exactly $r$ band primes and nonpositive whenever more occur. At fixed $t$, all moduli have size $\le U^{r+1}<x^{.49}$. Applying the native primitive progression estimate and Mertens convergence at this fixed rank gives the probability lower bound
$$
 (1-\log2)\frac{1}{r!}
 \int_{\substack{1/2<u_i\le1\\\sum_i u_i>K}}
       \prod_{i=1}^r\frac{du_i}{u_i}.
$$
The sum threshold has boundary measure zero and repeated primes contribute $o_t(1)$. For independent $u_i$ with probability law $e^{\lambda_*u}du/(Au)$, their sum has mean $rG/A=K+K^{2/3}+O(1)$ and variance $O(K)$. Chebyshev's inequality gives probability $1-o(1)$ on $(K,K+2K^{2/3}]$. The integral divided by $r!$ is at least $(A^r/r!)e^{-\lambda_*(K+2K^{2/3})}(1-o(1))$. Its logarithm is at least $A-\lambda_*K+o(K)$ by Stirling, proving the lower side of (3). The single fixed-rank form of the tilting argument was independently derived in the referee audit.

For the conditional law with $\chi=R_{x^e}\mu^2$, choose $e<t/2$. In the upper moment every active mark exceeds $z$, and all the lower-bound band labels also exceed $z$. Apply the same dimension-one two-sided sieve of level $x^{.01}$ to the remaining input cofactor, separately to the positive marked sums, the lower-bound subtractand and the denominator. All initial moduli are $\le x^{\max(Jt,(r+1)t)}$, where the exponent tends to zero with $t$. The ensuing moduli are below the available fixed level. The smooth sieve divisor is uniquely parsed from each initial $z$-rough modulus. Its relative error is $O(E(.01/e))$ times each positive arithmetic main, and every main has the same factor $g_z$. At each fixed $t,e$ squareful inputs cost $o_{t,e}(g_zS_b)$ after these fixed-order moments or labels: on $R_z$ their population is $O(x/z+\sqrt x)$ and all multiplicities and weights are bounded in terms of $t,e$. The denominator is bounded below by a fixed fraction of $g_z\sum |f|$ for small $e$. In the upper moment the independent $p>z$ sum is bounded by the earlier full one. In the lower calculation the band is entirely above $z$ and the extra-label to main ratio stays $\le\log2+o_t(1)$ before sieve errors. Sending $e\downarrow0$ after $x\to\infty$ yields the same two bounds for the polynomially rough squarefree physical population.

## An explicit parameter choice and the physical weight on rare inputs

Equations (2) and (3) continue to hold along $e=t^2$, with $x\to\infty$ first at each fixed $t$, and then $t\downarrow0$. In (1) the normalized discrepancy tends to zero along the same path. This statement follows by tracking the constants that survive the first limit. Put $u=t/e$ and $K_0=\lfloor\theta/t\rfloor$. The inverse estimate above gives
$$
 |C_0(A)|+L^{-1}|C_1(A)|
 \le 3(K_0+2)(2K_0+2)^{|A|}.
$$
The large-$x$ limsup of the absolute harmonic sum over sets is therefore at most $3(K_0+2)u^{2K_0+2}$, by the limiting reciprocal prime sum $\log u$. The absolute $d$-sum is $\ll1/e$, the normalized presieve factor is $g_z L\ll1/e$, and the optional large-prime label costs at most $O(1+\log(1/t))$ in the limit. All three implied constants are absolute. The principal on each prefix after all $x$-errors is bounded by $\rho(u)$. For the base Type I, $\sum_{\ell^j\le U}\log\ell/\varphi(\ell^j)\ll L$ and the only additional main error comes from the logarithmic prefix, bounded by $O(\rho(u)/e+\int_u^\infty\rho(v)dv)$. Hence the total surviving error in $S_b$ units is bounded by
$$
 O_f\!\left((K_0+2)(1+\log(1/t))u^{2K_0+2}
   \left[\frac{\rho(u)}{e}+\frac{E(u/2)}{e^2}\right]
   +\int_u^\infty\rho(v)\,dv\right).
$$
The constants from the fixed-profile progression discrepancy multiply quantities that tend to zero at each fixed $t,e$. Taking $\theta=\sqrt t$, $e=t^2$ gives $u=K^2$, $K_0\le K=t^{-1/2}$. Dickman factorial decay and $E(u/2)\ll (u/2)^{-u/4}$ dominate $u^{2K+2}$ and every displayed polynomial factor. The relative error in the conditional probability is $O(E(.01/e))$ on each positive marked sum, so the same parameter choice preserves its logarithmic upper and lower bounds.

This yields a pointwise statement on actual inputs. For this explicit $e$ let $G_t(x)$ be the maximum of $Z/(|f_x(n)|\log k)$ over physical inputs with $R_z(k)\mu^2(k)=1$, $s>Y$ and $|f_x(n)|>0$, assigning zero for an empty set. Then
$$
 \log\!\left(\liminf_{x\to\infty}G_t(x)\right)
 \ \ge\ K\big(\log K+\log\log K-1+o(1)\big).
$$
Indeed the high-product signed mass is bounded below by a positive constant times $S_b t^{-1}\log(1/t)$ for small fixed $t$. The ordinary conditional denominator times $L$ is $O_f(S_b/e)$ by the same upper sieve. Equation (3) bounds the conditional fraction in the high product region from above. Division proves the displayed lower bound since $e\,t^{-1}\log(1/t)=t\log(1/t)$ has logarithm $o(K)$. Thus arbitrarily large positive coefficients occur on real source inputs and survive the full signed bookkeeping in this representation.

Equations (1)–(3) provide a product-capped exact reduction, its actual signed leading debit, and the two-sided ordinary size of its surviving physical cohort. The strict $S_b$-scale upper on the complete source remains unresolved.
