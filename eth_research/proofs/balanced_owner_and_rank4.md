# Reweighting every near-threshold input owner on the balanced triple source

Use $L=\log x$, $U=x^\alpha$, $D=x^d$, $\alpha=.24$, $d=.49$, $b=d-\alpha=.25$, $w=\exp(L^a)$ for fixed $0<a<1$, and $I=(x/2,x]$. Let $g(n)=2$ on the squarefree three-prime outputs in the original Gold 4.63 family, all coordinates $\log r/\log n\in(.2001,.4999)$, and zero elsewhere. Its native outside coefficient is $-g$. Write $J_C$ for its ordinary mass in units $x/(2L)$. The source-level inequality below uses $S^\circ=\mathfrak S_2x/(2L)\sim S_b$.

For $n=k+2\in I$, restrict to $w$-rough squarefree $k$ and use this restriction on every displayed physical sum. Put $P=\{p\mid k:U<p\le x^b,\ p\ \mathrm{prime}\}$, $m=|P|$, let $Q$ be the product of the prime divisors of $k$ greater than $x^b$, and $s$ the product of those at most $U$. Write $M_s(v)=\sum_{e\mid s,\ e\le v}\mu(e)$ and take this as zero for $v<1$. Define

$$
 b^*(k)=-\log Q\,M_s(U)+\sum_{p\in P}(\log k-\log p)M_s(D/p)
                  +1_{\mathbb P}(k)\log k.
$$

The complete native contribution $W_C=-\sum g(k+2)B_\sigma(k)$ satisfies

$$
\frac{W_C}{S^\circ}
=\underbrace{\frac{2-d}{d}\log\frac{d-\alpha}{\alpha}}_{0.12579839127670\ldots}\,J_C
 -\frac{1}{S^\circ}\sum g(k+2)b^*(k)+o(1).
\tag{1}
$$

This includes every input rank and prime boundary. For $1<s\le U$ the residual $b^*$ vanishes on every configuration. For $s=1$ it equals $(m-1)\log k+1_{\mathbb P}(k)\log k$. In particular every input with one near-threshold prime and $s\le U$, including genuine semiprimes of this shape, disappears from the residual. Reweighting creates the *positive* surface debit in (1). Outputs on other chambers retain their original contribution. Only the net right-hand side can enter a terminal bound.

## Exact divisor accounting

For an eligible label $p$ write $C_p$ for its complete native inner divisor sum without $\log p$. When $k$ is composite, summing all divisors of $k/p$ gives zero. Thus $C_p$ is the negative of the sum with divisor at most $a_p=\max(U,D/p)$. For $p\in P$, any such divisor uses zero or one other prime in $P$, and none in $Q$. If it uses $p'\in P$ then its remaining divisor is at most $D/(pp')\le x^{.01}$. It follows that

$$
 C_p=-M_s(D/p)+\sum_{j\in P\setminus\{p\}} M_s(D/(pj)),\qquad
 C_q=-M_s(U)\quad(q\mid Q).
$$

For a genuine prime $k$ the original row is zero. It has $s=1,m=0,Q=k$ and the explicit prime term in $b^*$ supplies the required correction. Addition over all original labels gives the finite identity

$$
 B_\sigma(k)-\sum_{p\in P}\log k\,C_p
 = b^*(k)-\sum_{\{p,j\}\subset P}(2\log k-\log(pj)) M_s(D/(pj)).
\tag{2}
$$

When $s>1$ and $s\le U$, $M_s(v)=0$ for every $v\ge U$. When $s=1$ these terms equal one. The residual evaluations follow.

## Small moduli and the boundary principal

On the actual balanced output family the absolute sum of progression discrepancies in the reduced residue $2$ over odd moduli $h\le x^{.495}$ is $O_A(xL^{-A})$ for every $A$, also with an interval prefix. This follows from Liu–Park–Song Theorem 3.2 on boxes in three distinct primes. One can cut the prime exponents $\log r_i/L$ at mesh $L^{-K}$. All faces comparing $\log r_i$ and $\log n$ are linear. Dyadic ends of the product are handled by the product cutoff or interval collars. The PNT estimate in intervals with polynomial prime size, after partial summation in two variables, bounds the crossing collars by $O_B(xL^{-B})$ on taking $K$ large. Under the discrepancy sum their actual incidence is at most $(\#\mathrm{collar})^{1/2}(\sum_{k\le x}\tau(k)^2)^{1/2}$ and the primitive term costs $O(L)$ times the collar population. The fixed power of $L$ boxes is absorbed in the log precision. This is the same bounded-profile transfer as Gold 4.66 at a fixed gap below one half.

Use this estimate after expanding $R_w(k)$. Truncate Bonferroni at $O_A(\log L)$ factors and apply its two adjacent orders to the absolute unsigned remainder. A sieve divisor of primes at most $w$ has size $x^{o(1)}$ at these orders. The presieve factor and the $w$-rough part of a modulus are uniquely recovered. The unsieved incidence in the first sum of (2) has modulus $pe\le D$, with $p\in P$ and $e\le D/p$; there are at most two eligible labels in a modulus of this size. In the pair term the modulus is $pje\le D$ with $e\le x^{.01}$ and the two larger primes are uniquely recovered as an unordered pair. For physical rows $e$ may be recovered inside the squarefree integers. Removing or restoring the squarefree restriction on $w$-rough integers costs $O_A(xL^{-A})$ by Cauchy–Schwarz from $O(x/w)$ squareful integers, $\sum\tau(k)^2\ll xL^3$, and the bounded number of prime divisors greater than $x^{.24}$. The squareful deletion also permits using ordinary product moduli in place of an incidence defined only on squarefree inputs. In the first sum explicitly restrict $(p,e)=1$, which is exact on squarefree $k$. The factorial Bonferroni tail is smaller than any prescribed inverse log power after allowing for the fixed powers of $L$ in the coefficient sums. Prefix partial summation supplies $\log k$.

Put $g_w=\prod_{2<r\le w}(1-1/(r-1))$ and let $A_w(T)=\sum_{u\le T,\ u\ \mathrm{odd}}\mu(u)R_w(u)/\varphi(u)$. For a modulus containing $p$ or another prime forbidden by primitive coprimality with the output or the selected label, deleting terms of $A_w$ containing that prime costs $O(Lx^{-.19})$ per excluded factor. There are at most four such factors. The corresponding deletion in the prime sums costs the same type of power saving. The excluded factors of the output exceed $x^{.19}$ and the pair cutoff for $e$ is less than $x^{.01}$.

For the first sum in (2), complementary divisors produce the primitive inner factor $A_w(D/p)$, up to the preceding exclusions. Its argument is at least $x^{.24}$. The Möbius PNT and subpower convolution give $A_w(D/p)=O_A(L^{-A})$ uniformly here. Hence the average of the entire first sum against $g$ is $o(S^\circ)$. In this application the replacing logarithm is $\log k$, which depends only on the product endpoint. Input ownership remains complete.

For the pair term the corresponding primitive factor is $A_w(D/(pj))$. Its argument can be one. That boundary contributes at leading order. The signed measures
$$
 d\mu_x(v)=g_w L A_w(x^v)\,dv,\qquad v\ge0,
$$
have uniformly bounded total variation and converge weakly to $\mathfrak S_2\delta_0$. To see this let $A$ omit the presieve in $A_w$. The Euler series for $\mu(u)/\varphi(u)$ on odd integers is $G(z)/\zeta(1+z)$, with $G(0)=\mathfrak S_2$ and an absolutely summable correction with some positive power moment. The classical Möbius prime number theorem implies $A(e^v)=O_B((1+v)^{-B})$ for all fixed $B$. Its integral over $v\ge0$ is $\mathfrak S_2$, by taking $z\downarrow0$ in the Laplace transform $G(z)/(z\zeta(1+z))$. The inverse Euler factors for $2<p\le w$ form a positive Dirichlet series $h_w$ of total mass $g_w^{-1}$. The normalized law of $\log d$ with weight $g_w h_w(d)$ has tail $O(\exp(-cL/\log w))$ above each fixed $cL$, because $g_w\sum_d h_w(d)d^{1/\log w}\ll1$. Indeed $\sum_{p\le w}(p^{1/\log w}-1)/p\ll1$, and the finitely many small-prime factors are uniformly bounded for large $w$. Convolution with the integrable signed kernel $A(e^v)$ proves the assertion, including total variation outside each fixed neighborhood of zero.

Use the PNT twice to replace $\sum_{p,j}$ by $dt\,du/(tu)$, where $t=\log p/L$, $u=\log j/L$. For a fully uniform replacement first expand $A_w(D/(pj))$ over $e\le x^{.01}$. The remaining moving upper endpoint $pj\le D/e$ and the bounded polynomial in $\log(pj)/L$ permit ordinary partial summation, with arbitrary log precision uniformly in $e$. The sum of the absolute $e$ coefficients is $O(L)$. Removing the diagonal and changing $1/(p-1)$ to $1/p$ cost a power saving. Divide by two for unordered pairs. For fixed $n$ the primitive sum is consequently
$$
\frac12\int_0^{d-2\alpha}
\left(2\frac{\log k}{L}-d+v\right)
\left(\int_{\alpha}^{d-v-\alpha}\frac{dt}{t(d-v-t)}\right)d\mu_x(v)+o(1).
$$
The inner integral is continuous at zero. The bounded variation estimate pays $\log k/L=1+O(1/L)$ uniformly on the dyadic interval. In the limit this equals $\mathfrak S_2(2-d)d^{-1}\log((d-\alpha)/\alpha)$. Summing against $g$ and using its PNT mass proves (1).

## Direct adversarial test and the first unpaid term

At $x=10^9$ the following actual balanced outputs certify both residual signs when $s>U$. For example take the fixed presieve exponent $a=1/20$, for which $w<5$ at this $x$.

| $k$ | $s$ | $Q$ | $n=k+2$ | $b^*(k)$ |
| --- | --- | --- | --- | --- |
| $500253215$ | $5\cdot7\cdot11$ | $1299359$ | $359\cdot409\cdot3407$ | $-\log Q$ |
| $500237699$ | $13\cdot17$ | $2263519$ | $463\cdot929\cdot1163$ | $+\log Q$ |

These are finite tests of signs. They also disprove a uniform pointwise completion claiming $b^*\ge0$ on this class of inputs. They do not give a density on an infinite sequence of scales. To close this approach one still needs a signed mean for $s>U$ and the $s=1,m=0$ composite inputs. Estimating the computable low-divisor pieces of $b^*$ eventually exposes $1_{\mathbb P}(k)\log k$ on the balanced three-prime output. Its independent favorable lower bound is precisely prime-sensitive information not supplied by (1).

## Independent rival bound for the whole rank-four semiprime-input row

For rank-four outputs the retained part $F$ is zero. A nonzero $f$ requires a squarefree good output and $H\ne0$. The exact native small-prime cancellation and good-set gap imply every output coordinate $t_i>1/5-\epsilon$ (`FMGoodSupport.lean`, `small_prime_cancels` and `gap_excluded`). All four coordinates are below $.401$. If each $t_i>1/5$, then $-f$ equals the complementary-pair count of the first packet. If a coordinate falls in $(1/5-\epsilon,1/5]$, the native lower $H\ge-3$ bounds $-f\le3$. The signs and the degree-two kernel follow directly from the native divisor sum. No omitted off-good rank-four residual is added.

The angular mass $J_4^-$ of the complete nonnegative function $-f$ on rank four is therefore at most $10\epsilon$. Here is an explicit volume bound. For a chosen singleton collar coordinate, its interval has width $\epsilon$, the other three have exponents at least $.199$, and the area of the remaining positive simplex is at most $(1-(.2-\epsilon)-3(.199))^2/2$. Divide by $4! (.199)^4$ and multiply by 12 for the four choices and weight three. If there is no singleton collar, for each of three pair partitions two coordinates can be integrated in intervals of length $.101$ and the third in an interval of width $4\epsilon$. Divide by $4! (.2)^4$ and multiply by three. The two coefficients of $\epsilon$ are less than 6.57 and 3.19 respectively.

Now reverse the source and sieve $k=n-2$ for every prime factor at most $x^{.24}$. On the complete semiprime-input contribution, both factors of $k$ must exceed $x^{.24}$ for the physical coefficient to be nonzero, and each such coefficient is $-\log k$. Count the larger rough population with the same nonnegative output envelope. It is an angular profile of four polynomially large primes with fixed polyhedral boundaries, so the same source version of Liu–Park–Song gives fixed level $\theta<1/2$. Primitive coprimality with an output prime of size $>x^{.19}$ costs $o(x/L^A)$ in the summed main term by $\sum_{d\le D,p\mid d}1/\varphi(d)\ll L/(p-1)$. Letting $\theta\uparrow1/2$ in the upper linear sieve gives
$$
0\le\limsup \frac{U_{\mathrm{semiprime},4}}{S^\circ}\le4J_4^-<4\cdot10^{-8}.
$$
This bound covers all semiprime inputs and all native rank-four outputs. It can coexist with the stronger direct slab estimate by taking disjoint pieces or the smaller valid upper on their intersection. Adding the two bounds for the same inputs would double count. A crude unconditional result for the whole unrestricted balanced triple on semiprime inputs from the same reverse sieve is $4J_C$. Formula (1) identifies a different signed charge, but does not establish the full outside upper.

## Reproducibility and source trail

The independent rerun of the exact four-way box integral reproduced the two endpoint integers in `J4_replay.json` over 400,896 subcubes. In the original integrand $1/\prod t_i$ is jointly convex, because its logarithm is a sum of convex negative logarithms of positive affine factors. Jensen gives the lower bound and coordinate-by-coordinate chord interpolation the upper. Tests of the four indicator faces preserved the two distinct displacements. This confirms the reported geometric enclosure at the level of exact arithmetic. Its transfer to an outside bound uses analytic premises.

- The ordinary three-prime chamber and archived small-label treatment are documented in `REAL1B_Gold463-466_FULL_PAPERS.md`, Gold 4.63 and 4.66. The physical ledger and cutoffs are those of the repository at `43facedcf40b2f998aa47f7198d6b9b5feb5b792`.
- Theorem 3.2. [Liu, Park and Song](https://people.math.harvard.edu/~pspark/boundedgaps.pdf)
- Theorem 1.1 and its continuously bridged range. [Fouvry and Radziwiłł](https://arxiv.org/html/1812.00562v2)
- Lemma 2.5. [Matomäki and Zuniga-Alterman](https://www.utupub.fi/bitstream/handle/10024/185534/Matom%C3%A4ki_and_zuniga_weighted_sieves_2025.pdf?sequence=1)
