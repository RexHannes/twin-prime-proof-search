# Complete payment on outputs with a prime factor above the half face

Use the original *sharp* physical owner coefficient, all its input labels, and $f_x=\Phi_x-\psi_x$ at commit 43facedcf40b2f998aa47f7198d6b9b5feb5b792. Let $\epsilon=10^{-9}$, $\nu=1/5-2\epsilon$, $\beta=1/2-2\epsilon$. Write $Q=P^+(n)$. On the complete output sector
$$
 Q>n^{1-\beta}=n^{.500000002}
$$
and on the physical dyadic window $n\in I_x$, the native outside profile equals, for sufficiently large $x$, precisely the indicator $g_x$ of the following family:
$$
 n=q_1q_2Q\ \text{squarefree},\quad q_1<q_2,\qquad
 n^\nu\le q_1<q_2\le n^{1/5},\qquad q_1\le n^{1/5-\epsilon}.
$$
The formula identifies $f_x$ restricted by the displayed sector. Every member of the indicated family automatically satisfies that sector for large $x$.

**Kernel calculation.** Nonsquarefree inputs to the output profile have weight zero. For squarefree $n$, no divisor involving $Q$ satisfies the cutoff for $H$. Every divisor of $n/Q$ satisfies both the total and large-subsums cutoffs since $n/Q<n^\beta$. A divisor containing a factor with normalized logarithm in $[\nu,1/5]$ has $g_0=0$. For all other divisors the coefficient is its Möbius value: the small factors carry their original Möbius sign and at most two factors can have exponent $>1/5$, with their joint sum below $\beta<1/2$. Thus $H$ is exactly 1 if every prime divisor of $n/Q$ lies in the collar $[n^\nu,n^{1/5}]$, and 0 otherwise.

Write $X=x/2$. Each labelled divisor in $K$ has size greater than $X^{.0265+.0105+.0115+.463}=X^{.5115}$. Every prime factor of that divisor divides one of its four slots, each of size at most $X^{.465}$. This includes the original general-integer fourth slot. Therefore $Q$ cannot divide it, and $n/Q<n^\beta\le(2X)^\beta<X^{.5115}$ for large $X$ prevents it dividing the cofactor either. Hence $K=0$ throughout the sector.

Since $H\ge0$, the subtracted good-set part $G$ vanishes. A nonzero retained rank now requires exactly two primes besides $Q$, both in the indicated collar: $3\nu>\beta$ and rank two is omitted. The polynomial output roughness holds. The five-box mask vanishes by rank. For a good-set rank witness each collar prime must receive positive rank (the cost of rank zero would exceed $\epsilon$); its coordinate is at most $1/5$, so it must have rank one and exceed $1/5-\epsilon$. Conversely, if both exceed $1/5-\epsilon$, assign ranks $(1,1,2)$ to $(q_1,q_2,Q)$. These satisfy the strict lower faces and have zero tiny cost. The good set is therefore exactly the complement of the last stated inequality inside this collar. This proves the pointwise characterization, including the weak faces of the lower and upper cutoffs.

**Arithmetic bound.** Let $\mathcal U_{\mathrm{hi}}$ denote the original sharp outside sum restricted to this entire output sector. The fixed-rank three-factor version of the (PC) calibration in the first packet gives
$$
 \mathcal U_{\mathrm{hi}}=A(g_x)-\mathfrak S_2\sum_{n\in I_x}g_x(n)+o(x/L).
$$
Here $A$ retains true primality of $n-2$. The box is defined by finitely many affine faces in the normalized factor logs, so its primitive progression estimate follows from Liu–Park–Song Theorem 3.2 with the dyadic-prefix and collar argument in the first packet. On this profile all three primes are polynomially large, with $q_1,q_2$ distinct and ordered. Genuine prime powers, input squarefreeness and both Vaughan subtractions are handled by the same uniform calibration.

For fixed $b=q_1q_2$ and $N=x/b\ge x^{.6}$ upper-bound the number of primes $Q\le N$ for which $bQ-2$ is prime on the physical sector. Both primes exceed $z=x^{.02}$ there. For odd $p\le z$ neither $q_i$ divides $p$ for large $x$, hence $Q(bQ-2)$ has exactly two root classes. With Montgomery's large sieve at $D=\lfloor N^{1/3}\rfloor$ the product mass lost from moduli above $D$ is at most
$$
 2\sum_{2<p\le z}\frac{\log p}{p\log D}
 \le \frac{.04 L+O(1)}{.199 L}<1/4.
$$
The full product before truncation is at least $(\log z)^2/4$, because $(1-2/p)^{-1}\ge(1-1/p)^{-2}$ for $p>2$, and $\prod_{p\le z}(1-1/p)^{-1}\ge\sum_{j\le z}1/j\ge\log z$. The large-sieve numerator is at most $2N$ for all sufficiently large $N$. The pair count is therefore at most
$$
 \frac{2N}{(3/16)(.02L)^2}<40000\,N/L^2.
$$
The harmless rounding of the harmonic lower bound can alternatively be absorbed into the slack of 40000.

Every physical collar prime belongs to $[(x/2)^\nu,x^{1/5}]$, whose reciprocal prime mass is $\log((1/5)/\nu)+o(1)$ by Mertens. An unordered distinct pair contributes at most half the square of that mass. Since $\log(n-2)\le L$,
$$
 A(g_x)\le(20000[\log((1/5)/\nu)]^2+o(1))x/L.
$$
For the opposite sign, the prime number theorem gives $\pi(N)\le4N/L$ uniformly here, since $N\ge x^{.6}$. Thus the ordinary count satisfies $\sum g_x\le(2[\log((1/5)/\nu)]^2+o(1))x/L$. Finally $S_b\sim \mathfrak S_2 x/(2L)$, where
$$
 \mathfrak S_2=2\prod_{p>2}\left(1-\frac1{(p-1)^2}\right)\ge
 2\prod_{m=2}^{\infty}(1-m^{-2})=1.
$$
With $b_0=\log((1/5)/\nu)=-\log(1-10^{-8})<10^{-8}/(1-10^{-8})$ we get, with outward slack,
$$
 \boxed{\quad(-5\cdot10^{-16}-o(1))S_b\ \le\ \mathcal U_{\mathrm{hi}}\
       \le (5\cdot10^{-12}+o(1))S_b.\quad}
$$
This is a bound on the complete signed sharp input sum on the stated outputs. Its upper coefficient is an adverse cost when the complement is put back into the ledger. A sufficient outside target for the remaining $Q\le n^{1-\beta}$ outputs is then $(0.317014679959-\kappa+o(1))S_b$, under the same lower-ledger and box premises. No independent upper bound is supplied for that complement.

Applying the unique-large-owner argument to the complementary profile $f_x-g_x$ uses the same finite-profile progression contract: either partition it into the same disjoint fixed-rank rank/profile cells, or retain the extra $Q\le n^{1-\beta}$ face in its bounded-rank description. The resulting single-prime-owner signed estimate still requires proof.
