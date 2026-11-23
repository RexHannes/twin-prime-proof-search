# Concentrating the complete signed upper on inputs with arbitrarily many small prime factors

Fix a positive integer $J$ and $0<t<1/[6(J+2)]$. Set $Y=x^t$, $H=x^{1/2-(J+2)t}$, and $L=\log x$. Write $k=n-2$ and use the dyadic interval, $S_b$, $S^\circ$, native signed outside $W(f)$, squarefree physical inputs, and $w=\exp(L^a)$ of *Removing the true semiprime inputs from the complete signed source*. Here $f=f_+-f_-$, both unsigned parts satisfying its bounded-rank profile progression estimate. The original sharp large coefficient and output cutoffs are preserved in $W(f)$.

For actual squarefree $k$ let $S=\{p\mid k:p\le Y\}$ and $m=\#\{p\mid k:Y<p\le H\}$. For any $T\subseteq S$ define
$$
 M(T)=\sum_{A\subseteq T,\,\prod A\le Y}(-1)^{|A|},\qquad
 h(T)=\sum_{p\in T}\log p .
$$
For $v=0,1$ write $D_v(T)=[(vm-1)\log k+h(T)]M(T)$. The quantities $m,k,Y$ remain the actual ones even when the argument of $D_v$ is a proper subset. For every $1\le|T|\le J$ set recursively
$$
 c_v(T)=-D_v(T)-
   \sum_{\varnothing\ne A\subsetneq T}c_v(A)M(T\setminus A).
\tag{1}
$$
Put
$$
 b_{v,J}(k)=1_{\mathbb P}(k)\log k+D_v(S)
   +\sum_{\varnothing\ne T\subseteq S,\,|T|\le J}
           c_v(T)M(S\setminus T).
\tag{2}
$$
For fixed $J,t$ we have
$$
 W(f)=\sum_{k+2\in I}R_w(k)\mu^2(k)
       [ f_+(k+2)b_{0,J}(k)-f_-(k+2)b_{1,J}(k)]+o_{J,t,f}(S_b).
\tag{3}
$$
For $z=x^\epsilon$ define $T_{>J,z}$ to be the right side of (3) restricted to $|S|>J$, with $R_w$ replaced by $R_z$ and the same squarefree restriction. For any $\eta>0$ one can choose $t$ and then $\epsilon\ll\min(t,\zeta)$, both fixed before the limit, so that
$$
 \limsup_{x\to\infty}\frac{W(f)-T_{>J,z}}{S_b}\le\eta .
\tag{4}
$$
Every input in $T_{>J,z}$ is squarefree, has at most $\lfloor1/\epsilon\rfloor$ prime factors, and at least $J+1$ of those lie in $(x^\epsilon,x^t]$. The two physical signs and all of their residual terms on this set are included.

## Primitive source accounting

Without the subset correction, (3) is the combination of the retuned base on $f_+$ and the single-marker retuned base on $f_-$. Both have exactly the same original prime-input term and primitive $-\mathfrak S_2\sum f_\pm$. The proof in the preceding paper also applies to this smaller $H$.

On inputs with $R_w(k)=1$ each selected prime in (1) exceeds $w$. The coefficient $c_v(T)$ depends only on the displayed factors of $T$, on $\log k$, and affinely on $m$. It is a sum of expressions $A(T)\log k+B(T)m\log k+E(T)$, where $|A|+|B|+|E|/L\le C_J$ with a finite constant depending on $J$ alone. For example an inductive majorant is $C_0=0$ and
$$
 C_j=3\cdot2^j+\sum_{i=1}^{j-1}\binom ji 2^{j-i} C_i.
$$
The term $h(T)\le L$ on every physical configuration and every grouped modulus below. Constants from this recursion can grow rapidly.

The complementary prefix $M(S\setminus T)$ expands into $e\mid k/\prod T$, $e\le Y$, with coefficient $\mu(e)$ and $(e,\prod T)=1$. On expanding the optional $m$, a label $Y<p\le H$ is distinct from all chosen small factors. A grouped modulus before the presieve is
$$
 d=e\prod_{r\in T}r\quad\text{or}\quad
 d=p e\prod_{r\in T}r\le H Y^{J+1}=x^{1/2-t}.
$$
The possible medium label is the unique factor of $d$ above $Y$; at most $O_J(L^J)$ identifications of $T$ share a modulus. Thus all errors of the bounded-rank primitive progression result fit with a fixed log loss at fixed $J$. Restoring subpower $R_w$ costs its usual arbitrarily accurate Bonferroni bracket, and the removal of rough nonsquarefree inputs uses Cauchy–Schwarz with the polynomial-in-$L$ multiplicity and $O(x/w)$ exceptions.

In the principal part the remaining Möbius sum $A_w(Y)$ excludes primes of $n$, $T$, and the optional $p$. The change in the full prefix caused by these exclusions is $O_J(L(1/w+x^{-\zeta}))$. The prime harmonic of each of the $J$ chosen factors costs $O(\log L)$, that of the optional medium factor is $O_t(1)$, and the logarithmic multiplier is at most $C_J L$. Consequently every added complete correction in (2) has mean $o_{J,t}(S_b)$ against either actual output profile. This proves (3). For ungrouped nonsquarefree majorants one can bound the number of choices of $T$ by $O_J(L^J)$ and the prefix terms by $\tau(k)$, which suffices with the same squareful deletion.

## The zero-small and nonempty strata

On true prime $k$ the medium and small sets are empty, so (2) gives zero from $\log k-\log k$. On composites with $1\le|S|\le J$, the last term with $T=S$ is $c_v(S)$, since $M(\varnothing)=1$. Recursion (1) cancels all displayed terms of (2) exactly. No intermediate sign bound is invoked.

On composite $S=\varnothing$, $b_{0,J}=-\log k$, hence $f_+b_{0,J}\le0$. For $\omega(k)\ge3$, $H^3>x$ ensures $m\ge1$, hence $-f_-b_{1,J}=-f_-(m-1)\log k\le0$. If $k=pq$ with $p<q$, $S=\varnothing$, and $p\le H$, its larger factor exceeds $H$ eventually and $m=1$. The negative channel is zero. Only $p>H$ can give positive mass there. The factor-product PNT, its level below one half and the upper sieve on $n=k+2$ prove that the normalized limsup of this last adverse mass is at most
$$
 \|f_-\|_\infty e^{-\gamma}F(\theta/\zeta)\zeta^{-1}
 \log\frac{1/2+(J+2)t}{1/2-(J+2)t},
$$
for fixed $\zeta<\theta<1/2$. This is $O_{f,J}(t)$. The complete zero-small pieces above are retained in the equality (3). Only the upper (4) can discard their favorable contributions.

## Polynomial input presieve

To transfer the added rows to $R_z$ use the fundamental lemma with auxiliary level $x^{t/2}$, as in the preceding paper. Every pre-sieve modulus is $\le x^{1/2-t}$. For each of the $J$ chosen variables between $z$ and $Y$ the additional absolute harmonic is $O(1+\log(t/\epsilon))$. The optional medium harmonic is at most $O_t(1)$. Their collective primitive per unit $S_b$ is
$$
 O_{J,t,f}\!\big((1+\log(t/\epsilon))^J
       [\epsilon^{-1}\rho(t/\epsilon)
                +\epsilon^{-2}E_{t/(2\epsilon)}]\big)+o_{J,t,\epsilon,f}(1).
$$
Here one uses the rough harmonic Möbius prefix $A_z(Y)=\rho(t/\epsilon)+o_\epsilon(1)$, the absolute $e$ harmonic $O(1/\epsilon)$, and $g_zL\ll1/\epsilon$. The factors removed by coprimality are now $>z$ or polynomial output primes, which cost $o_{J,t,\epsilon}(1)$ at fixed $\epsilon$. Marked-modulus coincidences are counted through the ungrouped absolute harmonic majorant in the main terms and through the $O_J(L^J)$ bound only for the progression discrepancies. No growing power of $L$ multiplies the fixed fundamental-lemma error. The retuned base also pays its Dickman tail as in the preceding paper. All these errors tend to zero at fixed $J,t$ as $\epsilon\downarrow0$. For (4) first make the true semiprime cost less than $\eta/2$, then pay the presieve replacement with the remaining tolerance.

Constants, modulus headroom and prime thresholds depend on $J$. Inequality (4) alone gives no uniform integrability of its compensated high-order terms, no bound after taking $J\to\infty$ with the other cutoffs fixed, and no positive advantage on a genuine-prime class. The unknown quantity is the ordinary signed physical sum $T_{>J,z}$. Any uses at terminal scale must evaluate that sum or retain its full cost.

The distribution and sieve theorem numbers and primary references are in *Removing the true semiprime inputs from the complete signed source*. The subpower moment method in *The first small-factor strata of the compensated signed source* motivates the finite-subset expansion. Here its corrected sharp coefficients, polynomial moduli, two different output channels, and fixed-accuracy order of limits are explicit.
