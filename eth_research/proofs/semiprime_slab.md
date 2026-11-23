# Complete semiprime-input slab for the native outside source

Let $x/2<n\le x$, $k=n-2$, $L=\log x$, $\epsilon=10^{-9}$ and $S^\circ=\mathfrak S_2 x/(2L)$. Put $f=\Phi-\psi$ as in `REAL1B.FM.Direct.outsideProfile` at `43facedcf40b2f998aa47f7198d6b9b5feb5b792`. Let $E$ denote $k=pq$, both factors prime, $x^{.492}<p\le x^{.494}$. Both factors exceed $x^{.24}$, $p<q$, $k>x^{.49}$, and for every fixed $0<a<1$ the subpower input presieve is one eventually. The native owner coefficient is exactly $-\log k$. Define $U_E$ to be the contribution of these inputs and $P^-(n)>x^{.21}$. Define $U_{E,4}$ to include just the rank-four outputs within this same population. With $a_E=\log(31369/31119)$,

$$
0\le\limsup U_{E,4}/S^\circ < 2.3\cdot10^{-8},\qquad
0\le\limsup U_E/S^\circ \le (4/.504)a_E+(2.3\cdot10^{-8})/3 < .063504604 .
$$

This controls a true positive contribution to the outside upper bound. The remaining triples in this slab and the unsieved complement of the slab still enter the full calculation. $S^\circ\sim S_b$ by the independent shifted-prime normalization argument.

## Physical signs

A nonsquarefree output has zero weight. On a squarefree output with the stated roughness all prime coordinates $t_i=\log p_i/\log n$ exceed $.21$. There are at most four. For a composite assign $r_i=1$ to each coordinate at most $1/2+\epsilon$ and $r_i=2$ to a larger coordinate. The latter can occur at most once, exceeds $2(1/5-\epsilon)$, and every assigned coordinate has zero tiny cost. The witness sum is at most five. Thus every such composite is good. The box selector needs five factors, so $f=-\max(-H,0)$. The prime itself has zero native weight. A semiprime has at most the smaller singleton in $H$ and hence $H\ge0$. On three primes $H\ge 1-3=-2$ since pair coefficients are nonnegative and the full product exceeds the cutoff.

On four primes every singleton enters and all three-prime products exceed the cutoff. Each pair contributes precisely when $t_i+t_j\le1/2-2\epsilon$. Within each of the three complementary pair partitions exactly one pair contributes unless its sums have distance strictly less than $2\epsilon$ from $1/2$. In that case neither contributes. Hence $-f$ equals the number of these exceptional partitions. Each is counted twice by the semiprime divisors on its two sides. Its largest value is three. On the whole slab the pointwise cost is at most two times the rough-output weight plus one third of the rank-four cost.

## Distribution for the specific input primes

Elementary prime partial summation gives the mass of the unweighted $E$ in the interval as $(a_E+o(1))x/(2L)$, using $a_E=\int_{.492}^{.494}dt/[t(1-t)]$. The logarithmic weight on every row may be bounded above by $L$.

For divisor moduli $h$, the relevant residue is $k=-2\pmod h$. In dyadic product rectangles, $X_0=MN\asymp x$ and the longer prime factor has $\log N/\log X_0\in[.506-o(1),.508+o(1)]$. Fouvry–Radziwiłł Theorem 1.1 supplies an absolute mean of the primitive discrepancy in the range $N^{56/23}X_0^{-17/23+\eta}\le Q\le NX_0^{-\eta}$. Since $(56\cdot .508-17)/23<.498$ and $.504<.506$, every dyadic block between $x^{.499}$ and $x^{.504}$ is covered with a fixed margin. The two prime coefficients are bounded by one. The longer one satisfies Siegel–Walfisz, including the auxiliary coprimality parameter, by the prime theorem in small progressions and the divisor bound for primes dividing that parameter. Below $x^{.499}$ use fixed prime product Bombieri–Vinogradov, for example Liu–Park–Song Theorem 3.2 for the two disjoint prime intervals.

For positive upper bounds, use disjoint short rectangles with coordinate mesh ratio $1+\eta_0$ and retain every rectangle meeting the dyadic hyperbolic interval. Their union lies in the original interval enlarged by $O(\eta_0 x)$ at its two ends. The longer prime identifier has uniform Siegel–Walfisz on intervals by subtracting prefix estimates. Across rectangles and dyadic modulus blocks the logarithmic losses are bounded powers for each fixed $\eta_0>0$. The primitive discrepancies sum to $O_A(x L^{-A})$. The PNT mass of the enlarged union is at most $(a_E+O(\eta_0)+o(1))x/(2L)$. Take $x\to\infty$ before $\eta_0\downarrow0$. This supplies the two positive sieve applications without a modulus-dependent boundary loss.

All primes of the sieve moduli actually used are less than $x^{.291}$, hence none can divide the semiprime input. The primitive main on odd moduli is exactly $1/\varphi(h)$ times the total mass. Even moduli have no incidence on these odd inputs for the sieve of $k+2$. The dimension-one local product is $V(z)=\prod_{2<r<z}(1-1/(r-1))\sim \mathfrak S_2e^{-\gamma}/\log z$. The linear upper sieve has $F(s)=2e^\gamma/s$ for $1\le s\le3$.

Apply it first to $P^-(k+2)>x^{.21}$ with level $x^{.504}$. The sieve parameter is $2.4$. Multiplication by $L$ gives normalized mass at most $(2/.504)a_E+o(1)$.

## The complementary pairs

Every exceptional divisor $M=rs$ is a product of distinct primes exceeding $x^{.21}$. For all sufficiently large $x$ its logarithm divided by $L$ lies in $[.5-3\epsilon,.5+3\epsilon]$. Its two factors each have exponent in $[.21,.291]$. Over all such $M$, Mertens' theorem applied to both variables bounds

$$
\limsup\sum_M\frac1{\varphi(M)}\le
\frac{(.291-.21)6\epsilon}{2(.21)^2}.
$$

The denominator two accounts for ordering. The strip has the displayed width for each fixed first exponent. Divide by two again at the final counting step, since the two complementary products represent one failed partition.

For each $M$ impose $M\mid k+2$ and remove small prime factors of $k+2$ at threshold $x^{.001}$ using an upper linear sieve of level $x^{.002}$. All original rough outputs survive. For every sieve divisor $d$, $(M,d)=1$ and $Md< x^{.504}$. The two prime factors of $M$ exceed $x^{.21}$ and the factors of $d$ are at most $x^{.002}$. Thus $Md$ recovers both parts uniquely. The full sum of sieve remainders is bounded by a single mean of the absolute discrepancies. Equivalently apply the linear sieve once to the nonnegative aggregate weight counting the permitted divisors $M$ of each $k+2$. All unrestricted $d\le x^{.002}$ also satisfy the same recovery. With $s=2$ the normalized upper is $(2/.002)a_E\sum_M1/\varphi(M)+o(1)$. Including the complementary-pair factor yields

$$
\limsup U_{E,4}/S^\circ\le
500 a_E\frac{.081\cdot6\epsilon}{2(.21)^2}
=2.2045166596\ldots\cdot10^{-8}.
$$

Combining the two bounds proves the assertions above. No upper for another source is allocated to this slab.

## Sources

- Theorem 1.1 and its overlap following the theorem. [Fouvry and Radziwiłł](https://arxiv.org/html/1812.00562v2)
- Theorem 3.2 on products of distinct primes. [Liu, Park and Song](https://people.math.harvard.edu/~pspark/boundedgaps.pdf)
- Lemma 2.5, upper and lower linear sieve. [Matomäki and Zuniga-Alterman](https://www.utupub.fi/bitstream/handle/10024/185534/Matom%C3%A4ki_and_zuniga_weighted_sieves_2025.pdf?sequence=1)
