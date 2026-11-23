# Signed compensation of semiprime input and localization at two small prime factors

For fixed $0<c<1/400$ set $L=\log x$, $V=x^c$, $U=x^{c\tau}$ with a fixed smooth probability density supported in $1<\tau<2$, and $D=x^c$. The product cutoff is automatic on the retained rows. Write $F(y)=\mathbb P(U<y)$, $T=x^{2c}$, and $H=x^{1/2-3c}$. Retain $R_w(k)\mu^2(k)$, $k=n-2$, and the original physical window throughout. Denote the averaged complete coefficient by $B(k)$. The original sharp complete outside sum against $f=\Phi-\psi$ equals the sum against $B$ up to $o_c(x/L)$ under the fixed-profile calibration proved in the first packet: $UV\le x^{3c}$, the lower Euler range is $U\ge x^c$, and the short-product block is empty. Apply the same calibration separately to $f_+=\max(f,0)$ and $f_-=\max(-f,0)$, fixed bounded piecewise profiles on the same output support.

Define the smooth prefix $M(r)=\sum_{d\mid r}\mu(d)(1-F(d))$. On every squarefree composite $k$ the physical $\ell$-row for $\ell>V$ equals $b_\ell(k)=-(\log\ell)M(k/\ell)$. On prime $k$ the true row is zero because the unit boundary cancels it. Introduce the explicit correction
$$
 W(\ell,k)=1+F(\ell)\frac{\log(k/\ell)}{\log\ell},\qquad
 B'(k)=B(k)-\sum_{\ell\mid k,\ V<\ell\le H,\ \ell\text{ prime}} W(\ell,k)b_\ell(k).
$$
At large $x$ the low rows in the sum have composite input, since $k\ge x/2-2>H$.

**Low-row identity.** For any fixed bounded-profile test $g$ satisfying the physical primitive progression bounds (PC) both for $g$ and its absolute envelope as in the first packet,
$$
 \sum_{n\in I_x}R_w(k)\mu^2(k)g(n)
       \sum_{\ell\mid k,\ V<\ell\le H} W(\ell,k)b_\ell(k)=o_{c,a,g}(x/L),
$$
where the sum is over prime labels. The proof retains all divisors in the prefix, including the unit. Write
$$
 W(\ell,k)\log\ell=(1-F(\ell))\log\ell+F(\ell)\log k.
$$
Thus both parts have scalar $\ell$ coefficients, and the second uses a smooth physical prefix via partial summation. After writing the prefix as its integral of sharp cutoffs, the modulus is $\ell m\le Hx^{2c}=x^{1/2-c}$. The $w$-smooth Bonferroni factor multiplies this by $x^{o(1)}$, leaving level below $x^{1/2-c/2}$. Each folded modulus has $O_c(1)$ possibilities for the distinguished prime since $\ell>x^c$; its smaller-prime factors determine the presieve fold uniquely. Replacing squarefree inputs before this calculation costs $o_c(x/L)$ by the divisor moment proof in the first packet: $W\le1+1/c$ and the corresponding absolute coefficients are $O_c(\tau(k)L)$. The formula $m\mid k/\ell$ becomes $\ell m\mid k$ even allowing a shared prime. Its primitive main per $\ell$ uses
$$
 \frac{g_w}{\ell-1}
 [ A_{n\ell,w}(U)-\ell^{-1} A_{n\ell,w}(U/\ell)].
$$
The first term has arbitrary logarithmic cancellation uniformly in $\tau$ since $U\ge x^c$. The second has the factor $\ell^{-1}\le x^{-c}$. These conclusions persist after multiplying by the indicated $\ell$ coefficients and summing their harmonic weights. This proves the low-row identity solely at the complete signed level.

Accordingly the following full *signed* expression has the same total as the native outside sum up to $o_c(x/L)$:
$$
 \sum_{n\in I_x} R_w(k)\mu^2(k)
  [ f_+(n)B(k)-f_-(n)B'(k)].
$$
All original higher-rank companions and their new multipliers are included. The correction is applied only to the negative output channel.

**Physical sectors.** The contribution of the prime input itself is zero. On a distinct semiprime $k=pq$ with $p<q$, if $p\le V$ the raw and corrected totals are zero. If $V<p\le H$, the two raw rows are $-\log p$ and $-F(p)\log q$. Since $q>H$ for large $x$, the $W$-weighted low $p$-row equals their entire sum. Hence $B'=0$ and $B\le0$. If $p>H$ both primes lie in the band $[x^{1/2-3c},x^{1/2+3c}]$. Its absolute contribution is $O_{f,\zeta}((c+1/L)x/L)$ uniformly in $c$: for fixed $p$ upper-sieve $q$ and $pq+2$ as in the first packet and sum $\sigma(p)/p$ over that band. Here, in all cases, two primes both $\le H$ cannot produce an input $k\in(x/2-2,x]$, since $H^2=x^{1-6c}$.

If $k$ is squarefree composite with no prime factor $\le T$, all its row prefixes are 1, $B=-\log k$, and $B'=(j-1)\log k$, where $j$ counts all its primes $\le H$. At rank at least three, $j\ge1$ since three primes above $H$ cannot divide $k\le x$. Hence $f_+B-f_-B'\le0$ on this entire sector.

Suppose $k$ has exactly one prime factor $s\le T$ and at least one other factor. Every row for a prime exceeding $T$ has prefix $F(s)$, since its divisor subsets of size at most $T$ can only be $1,s$. If $s\le V$ no eligible small label exists and all rows vanish. If $V<s\le T$, the small owner's quotient has prefix 1. Consequently
$$
 B=-\log s-F(s)\log(k/s)\le0.
$$
Its $W$-weighted small row equals this expression. Each other low label $p>T$ adds $F(s)\log k$ to the corrected coefficient. Thus $B'\ge0$ and the total is nonpositive. When *all* factors of $k$ are $\le T$ and there is just one, $k$ is prime and was already covered.

If the nontrivial product of *all* the primes of $k$ at most $T$ is $\le V$, none of these small primes is an eligible label. For each large owner the prefix is the complete divisor Möbius sum of this nontrivial product, hence all rows vanish. This argument is exact, including the weak face at $V$.

**One-sided complete localization.** Define $\mathcal E_{c,\delta,K}$ to consist of squarefree $k$ with $3\le\omega(k)\le K$, $P^-(k)>x^\delta$, at least two distinct prime divisors at most $x^{2c}$, and the product of all its prime divisors at most $x^{2c}$ greater than $x^c$. For $0<\delta<c$, the whole outside source has the upper bound
$$
 \begin{aligned}
 \mathcal U_{\mathscr B^c}(x)
 &\le\sum_{\substack{n\in I_x\\k=n-2\in\mathcal E_{c,\delta,K}}}
 R_w(k)\mu^2(k)[f_+(n)B(k)-f_-(n)B'(k)]\\
 &\quad +O_{f,\zeta}(c x/L)
   +O_{c,f,\zeta,\mathrm{density}}((\delta+2^{-K})x/L)
   +o_{c,a,f}(x/L).
 \end{aligned}
$$
To trim the small-prime and large-rank tails, apply the smooth Fourier–Euler proof to every raw and corrected row before restricting: the prime owner is now $\ell>x^c$, so the two-form sieve can use $z=x^{\min(\zeta,c/100)}$; $W\le1+1/c$; and the uniformly smooth cutoff has scale $cL$. A prime $p\le x^\delta$ in $k$ must belong to the quotient because $\delta<c$. For $\omega(k)>K$, every owner's quotient has rank at least $K$. This proves the displayed error. Constants in the second error may grow as $c$ shrinks; choose $c$ first and then $\delta,K$. No uniform limit in all three variables is asserted. The first error has a constant independent of $c$ for every sufficiently large $x$ after fixing $c$.

Bound the last residual with its full original $f_+$ and $f_-$ and a fixed margin to prove the desired outside estimate, after paying the indicated errors. This paper reduction supplies no favorable bound for that residual and credits zero net terminal saving. In particular, the fact that its inputs have two small primes does not imply the residual is negligible: their allowed range and the signed coefficients both depend on $c$. The same statement holds for the balanced output triple sector alone by multiplying $f_\pm$ by its exact fixed-profile indicator.
