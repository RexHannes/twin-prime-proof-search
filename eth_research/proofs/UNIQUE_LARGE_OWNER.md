# Reduction to one input prime above a near-half threshold

This is a second application of the smooth-owner argument to the complete physical outside profile. It selects one large input prime with an absolute error that can be made arbitrarily small on the terminal scale. The input prime can have exponent well above one half.

Fix a smooth nonnegative probability density with compact support in $(1,2)$. Write $\tau$ for a random variable with this density. For fixed $0<c<1/400$ change the Vaughan parameters to
$$
 U=x^{c\tau},\quad V=x^{1/2-3c},\quad D=x^{.49}.
$$
Keep $w=\exp((\log x)^a)$, $0<a<1$, and every physical input and output mask in the original sum. Since $V>D$ and $b>U>1$, the inner product cutoff is automatic for eligible rows. The total large-sum calibration from the first packet holds uniformly in $\tau$ at each fixed $c$. Its Type-I product modulus satisfies $UV\le x^{1/2-c}$. After the usual presieve folding there is still a fixed power gap to $x^{1/2}$, for example level $x^{1/2-c/2}$. The lower range in the Euler argument is $x^c$, and $\tau$ lies in a fixed compact interval. The short-product term is empty. In the second Type-I sum the shared-prime calculation still splits at $\sqrt U$, even though $V$ is much larger than $U$. The prime boundary in the comparison is the same original $A(f)$. Thus this new total equals the original sharp full outside sum up to $o_{c,a,f}(x/\log x)$ under the native fixed-profile (PC) transfer. A single instantiation of the historical endpoint at the original cutoffs would be insufficient for this assertion.

There are at most two eligible owners in each physical input since $3(1/2-3c)>1$. Denote the smoothed sum restricted to inputs with exactly one eligible owner by $C_c^{(1)}$. For every bounded test $|g_x|\le M$ supported on $P^-(n)>x^\zeta$, the total absolute sum of the two-owner rows is
$$
 \ll_{M,\zeta,\mathrm{density}}(c+1/\log x)\,x/\log x.
$$
In this estimate the implied constant is independent of $c$. The range of $x$ from which the enclosing asymptotics hold may depend on $c$.

To prove this, write a squarefree two-owner input as $k=pqs$. Then $s\le x^{6c}$, and each owner lies in
$$
 x^{1/2-3c}<p,q\le x^{1/2+3c}.
$$
At the row for $q$, the quotient is $ps>1$. The whole divisor sum is zero. Neither $p$ nor any divisor containing $p$ belongs to the inner smooth prefix, since $p>x^{2c}$. Thus the row is $-(\log q)S(s)$, where
$$
 S(s)=\sum_{b\mid s}\mu(b)\,h(\log b/(c\log x)),\qquad
 h(t)=\mathbb P(\tau\ge t)\quad(0\le t\le6).
$$
The row for $p$ has coefficient $-(\log p)S(s)$. This includes the case $s=1$, when $S(1)=1$. Extend $h$ with a compact smooth bump equal to one on $[0,6]$. Its differentiability constants are independent of $c$.

For each $p,s$, apply the two-form sieve of the first packet to the prime owner $q$ and $psq+2$, with $N=x/(ps)\ge x^{1/2-3c}$ on the nonempty rows. It gives
$$
 \sum_q(\log q)1_{P^-(psq+2)>x^\zeta}
   \ll_\zeta x\,\sigma(p)\sigma(s)/(ps\log x).
$$
Interchanging which prime receives the logarithm counts the two rows with the correct upper multiplicity. The harmonic sum of $\sigma(p)/p$ over the near-half band is $O(c+1/\log x)$ by the precise Mertens estimate on primes, since the endpoints stay a fixed distance from zero and $\sigma(p)=1+O(1/p)$. The harmonic sum
$$
 \sum_{s\le x^{6c}}\frac{\mu^2(s)\sigma(s)}s\, |S(s)|\ll_h1
$$
is uniform in $c$: apply the Fourier–Euler estimate from the first packet with base length $c\log x$, and restrict all primes in its product to $p\le x^{6c}$. Splitting at $x^{c/|t|}$ gives an Euler bound $O((2+6|t|)^2)$, with a uniform constant. This proves the absolute estimate on the entire two-owner population.

Consequently, for the exact native $f$ under the same analytic calibration,
$$
 \mathcal U_{\mathscr B^c}(x)=C_c^{(1)}(x)
   +O_{f,\zeta,\mathrm{density}}(c x/\log x)
   +o_{c,a,f}(x/\log x).
$$
Fix $c$ sufficiently small for a target tolerance and then let $x$ grow. The result does not exchange the limits. The one-owner sum includes every composite quotient of that prime and preserves the signed value of $f_x(\ell r+2)$. When the input itself is prime its single row is zero. A fixed $c$ also permits the bounded-rank and polynomial lower-factor approximation in the first packet, with constants that are allowed to depend on this already fixed $c$. Apply those two approximations in this order.

This argument gives no estimate for the sign of $C_c^{(1)}$. For example a semiprime input with one prime well above $V$, a second prime in $(x^{2c},V]$, and $f_x(n)<0$ has a positive contribution. The unique owner is its larger prime. The family includes many possible second-prime sizes even when the physical input has only two factors.
