# A prime-factor bilinear estimate for the actual five-prime upper sieve

Native source at `43facedcf40b2f998aa47f7198d6b9b5feb5b792`. Write $I=(x/2,x]$, $L=\log x$, $z=x^{6/25}$ and $S_2=2\prod_{p>2}(1-(p-1)^{-2})$. For $j=0,\ldots,5$ let $A_j$ denote the actual set of squarefree integers in the 1,566 ordered five-prime boxes and the $j$-th original face test. Let $J_j=\mathrm{Profile.sliceIntegral}(j)$ and $S^\circ=S_2x/(2L)$. This argument gives the following written source estimate.

$$
\limsup_{x\to\infty}
\frac{\sum_{n\in I\cap A_j}1_{P^-(n-2)>z}\log(n-2)}{S^\circ}
\le \frac{10}{3} J_j.                                      \tag{1}
$$

The recent endpoint requires the same six quantities with factor $3.4002754$. The following application of a bilinear proposition uses the small prime factor in each actual box. It uses the unmodified upper Rosser sieve.

## 1. Separate the five physical primes

Write an output as $n=p_1\cdots p_5$ in increasing order. On our boxes $x^{.039}<p_1<x^{.191}$ eventually, and every prime is $>x^{.039}$. Partition the five prime axes into disjoint multiplicative bins of ratio $1+L^{-B}$, splitting at dyadic boundaries if needed. Use all cells meeting the selected continuum region with $n\in I$ and the original log-$n$ faces and ordering. This is a positive covering. Each cell is an independent product of five one-variable intervals. Its integers satisfy $n\in(x(1-O(L^{-B}))/2,x(1+O(L^{-B})]$. An ordered labeling belongs to at most one cell, and there are at most $5!$ labelings per integer in their union. Equal primes and unordered labelings need only be allowed on the outer side of the cover.

The unconditioned total mass $U_j$ of the union, with labeled-tuple multiplicity, obeys $U_j=(J_j+o(1))x/(2L)$. The lower side follows because the original set is covered. For the upper side, remove the two enlarged-window collars, which cost $O(x L^{-B}+1)$ by the bounded multiplicity. Normalize the coordinates to $\log p_i/L$. The remaining extra tuples lie in arbitrarily small fixed neighborhoods of the finite list of ordering, box, or face hyperplanes. Their mass divided by $x/L$ tends to zero as the width tends to zero by counting the last prime in the actual dyadic window and applying the uniform PNT and the product harmonic-prime weak limit for the first four primes. The density $1/(t_1\cdots t_5)$ is bounded on these compact regions. This is the ordinary unit-count argument of `analytic_packet.md`, including repeated-coordinate boundaries. We may use the upper-window scale $2x$ in coarse trivial discrepancy estimates.

On a cell take $N$ to be the dyadic length scale of the first prime and $M$ the scale of the product of the last four. Split the latter into a bounded number of dyadic pieces if necessary. The short coefficient $\alpha_u$ is the indicator of primes in an interval on $u\sim N$. It is supported above $x^{1/(\log\log x)^3}$ and satisfies Pascadi's Definition 4.3, uniformly in the endpoints. For small modulus this follows from ordinary prime Siegel–Walfisz at both endpoints, removing primes dividing an arbitrary auxiliary $d$ at cost $O(\omega(d))$. For modulus $q> (\log N)^{2A+4}$, trivial progression counting and $\varphi(q)\gg \sqrt q$ give the required $O_A(\tau(d)^{O(1)}N/(\log N)^A)$ bound. The long coefficient $\beta_v$ counts factorizations of $v$ into four primes in their respective intervals. It is bounded by $4!$ and can be divided by that constant in the bilinear theorem. The principal is the primitive principal with $1_{(uv,m)=1}/\varphi(m)$ at modulus $m$. The progression is the single reduced residue $2$ at every odd modulus used below. The construction incurs a fixed power of $L$ in the number of source cells for each fixed $B$.

## 2. A two-part upper sieve

Fix $0<\delta<10^{-5}$, set $\theta=3/5-50\delta$, $D=x^\theta$, $\rho=\delta/4$, and fix $0<\nu<\rho/2$. Use a standard dimension-one upper Rosser sieve of level $x^\rho$ on the odd small primes $p<x^\nu$. Independently use the ordinary upper Rosser weights of level $D$ on $x^\nu\le p<z$. Both divisor sums are nonnegative pointwise majorants, making their product a majorant for $1_{P^-(n-2)>z}$. Omitting a prime exactly at a boundary of the full sieve is safe for this upper bound. Write $c$ for the small-prime sieve divisor and $d$ for the medium-prime sieve divisor. Both are squarefree, $c,d$ have disjoint prime factors, their roles are recovered uniquely from $cd$, and $c\le x^\rho$, $d\le D$. The local dimension function is $g(p)=1/(p-1)$ for odd primes.

The ordinary upper Rosser bound on its main sum is $\sum\lambda_m^+g(m)\le V(P)(F(s)+o(1))$, where $P$ is the specified prime set, $s=\log(\mathrm{level})/\log(\mathrm{upper\ cutoff})$, and $V(P)=\prod_{p\in P}(1-g(p))$. This usual linear-sieve upper estimate is uniform under the one-sided dimension-one product condition. Deleting primes only decreases the reciprocal density product, so both prime sets have the same allowable dimension constant as the original odd primes. Each mean divisor sum is itself nonnegative, as is also seen by taking its expectation on independent prime divisibilities. Multiplying the two bounds gives
$$
 V(z)\,[F(\rho/\nu)+o(1)]\,[F(\theta/(6/25))+o(1)] ,
 \qquad V(z)=\prod_{2<p<z}(1-1/(p-1)).                    \tag{2}
$$
Here the limits are taken for fixed parameters. The intermediate small prime set is deliberate: it lets the medium divisor have bounded rank and unmodified Rosser support. We next verify the summed sieve remainders for these specific weights.

## 3. Complete error for exceptional medium divisors

For the fixed $\nu$, each medium $d$ has at most $r_0=\lfloor\theta/\nu\rfloor$ prime factors. Write them in decreasing order $l_1,\ldots,l_r$. The exact upper support $\mathcal D^+(D)$ is specified by the standard prefix inequalities $l_1\cdots l_{2i}l_{2i+1}^3\le D$ for the odd prefixes where applicable, with distinct ordered primes. Put these primes into multiplicative bins with ratio $1+L^{-B}$ and endpoints split at $x^\nu,z$. Discard bins with a tied prime-bin position or touching a support boundary, **only in the discrepancy calculation**. Their harmonic mass, including the exceptional integers themselves, is $O_\nu(L^{-B}+x^{-\nu})$. For ties fix all coordinates but one; the remaining prime lies in an interval of relative width $O_\nu(L^{-B})$. For an uncertain power-product inequality do the same with the variable whose exponent is three (a nonzero coefficient suffices). The sum of $1/l$ for all integers in such an interval above a constant times $x^\nu$ is $O_\nu(L^{-B}+x^{-\nu})$, including endpoint rounding. The remaining fixed-rank prime harmonic sums are bounded at fixed $\nu$ by Mertens. Summing over the finitely many affected prefixes proves the bound, including the full divisor size boundary if imposed separately.

After summing source cells with multiplicity at most $120$, the actual and primitive principal absolute errors for a single modulus $cd$ cost $O(x/(cd)+1+x/\varphi(cd))$. Since $d$ has bounded rank with factors $\ge x^\nu$, $1/\varphi(d)\ll_\nu1/d$. The small divisors satisfy $\sum_{c\le x^\rho}1/\varphi(c)\ll L^2$ by the divisor bound. The unit terms sum to $O(x^{\theta+\rho})$ since the splitting of $cd$ by prime size is unique. The total exceptional contribution is consequently
$$O_\nu\bigl(xL^2(L^{-B}+x^{-\nu})+x^{\theta+\rho}\bigr).$$
Take fixed $B>10$, for example $B=20$. This is negligible compared with $x/L^2$. One can further increase $B$ for any preassigned fixed logarithmic error.

## 4. Pascadi's source-compatible factorization

For every remaining nonempty medium-prime cell and each dyadic $N$ from §1, pick one representative integer $d\in\mathcal D^+(D)$. Proposition 5.2 of Pascadi applies since $x^{2\delta}<N<x^{1/3+\delta}$. It assigns its prime slots to three groups with products $d_1,d_2,d_3$ such that
$$
 d_1\le N x^{-\delta},\qquad
 N^2d_2d_3^2\le x^{1-\delta},\qquad
 N^2d_2^5d_3^2\le x^{2-\delta}.                           \tag{3}
$$
Use the same slot partition throughout this multiplicative cell. The coordinate changes in (3) are at most $(1+L^{-B})^{O_\nu(1)}$. The ordering and all support inequalities are constant there. The sign is the constant $(-1)^r$. Because all medium slot bins are disjoint, the coefficient for each group of slots is a 0-or-1 indicator on its integer products. Fold the *entire* small-divisor weight $\lambda_c^+$ into the first group $q_1=c d_1$. The integer $q_1$ determines $c$ and the individual large prime slots uniquely. Its resulting coefficient still has modulus at most 1. All three coefficients have odd support. Dyadic localization of the three groups (including the value 1) costs $O(L^3)$. The loss in the first inequality is at most $x^{\rho+o(1)}$; the second and third inequalities involve no $q_1$.

For example with $\epsilon=\delta/100$, the dyadic size parameters satisfy $Q_1\le Nx^{-\epsilon}$, $N^2 Q_2 Q_3^2\le x^{1-15\epsilon}$ and $N^2 Q_2^5 Q_3^2\le x^{2-40\epsilon}$ for large $x$. These are precisely the three conditions of Pascadi Proposition 4.4. Apply that proposition to each block with the coefficients of §1 to bound the sum of actual minus primitive progression counts by $O_A(xL^{-A})$. Prop. 4.4 applies directly to these separated coefficients, without identifying the physical five-prime output as a single prime. The number of medium cells is $O_{\nu,B}(L^{(B+1)r_0+O_B(1)})$, and the number of source cells and dyadic group localizations is bounded by another fixed power of $L$. Choose $A$ after all fixed parameters. The total good-cell discrepancy is $o(x/L^2)$. The case $d=1$ uses empty prime groups and the same bounds, or ordinary small-modulus BV on the prime slot.

In the remaining principal, replace the primitive total by the full total, preserving its signed small/medium coefficients until their absolute correction is bounded. For each physical output the sum of $1/\varphi(m)$ over $m\le x^{\theta+\rho}$ sharing a prime with it is $O(L^2x^{-.039})$. Indeed each of its five primes exceeds $x^{.039}$ and $\varphi(pk)\ge \varphi(p)\varphi(k)$. The unique splitting into $c,d$ prevents a duplicate-modulus cost. Bounded output-label multiplicity now makes the complete correction $o(x/L^2)$.

## 5. Constant, splice and scope

Combining the two positive sieves, their full discrepancies, and (2), our upper count is at most
$$
 U_j V(z)[F(\rho/\nu)+o(1)] [F(\theta/(6/25))+o(1)] + o(x/L^2).
$$
Bound the logarithmic weight by $L$. Mertens gives $LV(z)\to S_2e^{-\gamma}/(6/25)$. First let $x\to\infty$ at fixed $\delta,\rho,\nu$. Next let $\nu\downarrow0$ so $F(\rho/\nu)\to1$. Since $1<\theta/(6/25)<3$, one has $F(\theta/(6/25))=2e^\gamma(6/25)/\theta$. Finally let $\delta\downarrow0$. This yields (1). The factor two in $S_2$ comes from the omitted prime 2 in $V$.

Summing all six tests proves the stronger native rough-density comparison at paper level. For the genuine-prime box, its nonnegative height and the polynomially large input let us use the same upper. Thus the five-box cap conditional on the still required native Vaughan calibration and comparator normalization is $(10/3-1)J=(7/3)J$. With the separate rigorous enclosure this is at most $0.64307354150049252130$. With the inherited lower ledger, the sufficient upper for the full outside source is consequently **strictly below $0.35681923399850747870$**. This leaves the sign of the full outside source unresolved, and does not establish an unconditional terminal reserve or parity advantage. The argument supplies the six `hr` clauses of the current Lean endpoint as paper mathematics; it is not a Lean verification.

## Source contracts

- Pascadi, *On the exponents of distribution of primes and smooth numbers*, v2, Definition 4.3 and Proposition 4.4 for the full bilinear discrepancy, §5 and Proposition 5.2 for ordinary upper Rosser support at $x^{3/5-50\delta}$. [Author's paper](https://arxiv.org/html/2505.00653v2)
- Lichtman, *A modification of the linear sieve, and the count of twin primes*, (1.1), Remark 2.9, (2.5), §§3–4 for the ordinary Rosser sieve, its one-sided dimension input and its explicit $F$. [Author's paper](https://arxiv.org/html/2109.02851v2)
- Iwaniec, *Rosser's sieve*, for the uniform main-term inequality in the dimension-one upper sieve. [Original paper](https://www.impan.pl/shop/publication/transaction/download/product/102606?download.pdf=)

## Extension to the full prime-side signed source

The least-factor argument applies to every nonnegative part of the actual outside profile $f=\Phi-\psi$ and to $\Phi_+$ itself. Precisely, each **positive** value belongs to the retained off-good $F$ sector, whose squarefree rank $r$ is three or lies between five and 255. All its primes exceed $x^{1/(4\cdot 10^{11})}$. Thus the least prime satisfies
$$x^{1/(4\cdot10^{11})}<p_1\le x^{1/3}.$$
Take $\delta$ in the previous proof smaller than $1/(20\cdot10^{11})$. The upper restriction in Proposition 5.2 includes $N\le x^{1/3+\delta}$. A source microcell may now have up to 255 prime coordinates, but the exponent, total angular complexity, multiplicity and maximum long coefficient are all fixed independently of $x$. Once $\delta$ is fixed, the number of cells remains a fixed power of $L$. In the limit, finite-rank $H$, $K$, the good set, rank and five-box masks have only finitely many possible angular boundaries. The nonconstant factor $1-(\log d/\log n)^2$ in $K$ is smooth on the compact positive simplex. Its three labeled bank intervals and the arbitrary-quotient bank are all retained as subset-product conditions. The mark presieve on positive outputs becomes automatic for sufficiently large $x$ because the fixed common polynomial lower exponent eventually exceeds $1/(\log\log(x/2))^{10}$. Taking the cell supremum of the bounded nonnegative profile therefore has the same limiting ordinary integral. The growing-rank and singular-coordinate uniformity problems do not arise.

Let $A$ be the native actual weight $1_{P^-(n)>y}\vartheta(n-2)$, let $h$ be either $\Phi$ or $f$, and write $h_\pm=\max(\pm h,0)$. Let $\Pi(h)$ be its limiting ordered angular integral for ordinary outputs, in the native $S_b$ normalization. On $G$'s negative good-set support the active-rank/polynomial-roughness bound gives the same ordinary limit; no upper-sieve distribution on its possible rank-two configurations is needed. On the complete actual prime side, including both signs, positivity of $A$ yields the unconditional comparison
$$
\limsup_{x\to\infty} \left(\frac{A(h)}{S_b}-\Pi(h)\right)
\le \frac{7}{3}\Pi(h_+) +\Pi(h_-).                       \tag{4}
$$
It retains the entire negative comparator companion. Superseding the previous *same* nonnegative profile comparison coefficient $c_*$ gives an advantage on that upper-certificate functional of $(c_*-10/3)\Pi(h_+)$. This computation does not compare the certificate to other historical candidate upper bounds.

There is a genuine open positive chamber outside the five-box source. Center the first four coordinates at $(.103,.107,.150,.281)$ and vary each by at most $.001$; the fifth is $1-\sum t_i$, centered at $.359$. The first two coordinates lie in the same centile, so every point is outside the original boxes. Their rank is five and a coordinate below $1/5-\epsilon$ and above $\epsilon$ excludes the good set. All factors exceed the small label banks for $K$ at large scales, so $K=0$. Every subset sum at the center is at distance at least $.009$ from $1/2$. Each subset sum moves by at most $.004$ since for a subset involving the fifth coordinate one may instead consider its complement. All individual coordinates avoid the $1/5$ boundary. Consequently $H$ throughout the chamber equals $\sum_{s_A<1/2}(-1)^{|A|}=2$, by enumeration of the 32 center subsets. The profile is therefore $f=2$ there. AM-GM gives $1/\prod t_i\ge 5^5$, hence $\Pi(f_+)\ge 2\cdot5^5(.002)^4=10^{-7}$. For $\Phi$, positive box mass also supplies $\Pi(\Phi_+)\ge J+10^{-7}$.

Equation (4) improves the complete genuine-prime-side nonnegative certificate by at least $6.6942\times10^{-9}$ for $h=f$. The whole-source version improves its corresponding certificate by more than $.0184$. The prime-power error is separately controlled on these bounded profiles. Transfer of (4) to the full large-product $\mathcal U_{\mathscr B^c}$ requires the matching Vaughan cancellation in the pinned source. More importantly, even the improved right-hand side in (4) retains $\Pi(f_-)$ and exceeds the closing threshold under the historical lower estimate $\Pi(f_-)>.6378274$. No global parity credit follows. The old unconditional trivial lower $T\ge0$ continues to dominate any negative lower bound obtained from this information.

The main-sum theorem used in §2 is the ordinary beta-sieve upper theorem in Friedlander–Iwaniec, *Opera de Cribro*, Theorem 11.12, specialized to dimension 1, and its linear-sieve evaluation in Chapter 12. Lichtman (1.1) identifies these ordinary upper weights, and Remark 2.9 explicitly specifies that the upper estimate uses the one-sided product condition. In Iwaniec, *Rosser's sieve*, see the one-sided dimension hypothesis (1.3), the truncated sums in §3, and the upper estimate in the proof of Theorem 1. The smoothened-weight Theorem 2.10 is not needed in §2.
