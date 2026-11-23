# A smaller four-factor debit on the physical lower ledger

Native commit `43facedcf40b2f998aa47f7198d6b9b5feb5b792`. Write \(L=\log x\), \(I=(x/2,x]\), \(\epsilon=10^{-9}\), \(\delta=1/(4\cdot10^{11})\), \(\nu=1/5-2\epsilon\), \(a=1/5-\epsilon\), \(\beta=1/2-2\epsilon\), and \(\gamma=1/2-\epsilon\). \(A,B\) denote `Ledger.weighted actual` and `Ledger.weighted compare`. They are evaluated on identical outputs. \(P\) is `Ledger.positive`. \(W_j\) is the exact calibrated off-good source of rank \(j\), and \(R_j=A(W_j)-B(W_j)\). Define \(\Pi(W)\) by the ordinary ordered-prime angular integral, with measure \(dt_1\cdots dt_{r-1}/\prod_{i=1}^r t_i\) and \(t_r=1-\sum_{i<r}t_i\). Each physical squarefree output is counted once.

## Published one-sided sieve estimate for these profiles

For nonnegative bounded, piecewise continuous angular profiles on fixed, ordered lists of \(r\) primes in \(I\), all above \(x^c\) for fixed \(c>0\), the following holds for the profiles used below:

\[
\limsup\frac{A(W)}{S_b}\le\frac{32}{9}\Pi(W),\qquad
\frac{B(W)}{S_b}\to\Pi(W).                                             \tag{1}
\]

Allow the fixed finite polyhedral faces of the profile to move by \(O(1/L)\). This includes the cutoff \(p>x^\delta\) in coordinates normalized by \(\log n\), since \(L/\log n=1+O(1/L)\). The second statement follows from the largest-factor BV argument of `analytic_packet.md` and the ordinary PNT prime-product integral. Each relevant profile below has bounded variation when its largest prime varies along a fixed prefix. Positive and negative parts qualify separately.

Here is a source-exact proof of the first inequality using an ordinary linear sieve. Put \(u=3/16\) and take \(1/2<\theta<9/16=(3-u)/5\). For a short rectangle with upper prime endpoints \(e^{v_i}=H^{e_i}\), set \(H=\exp(\sum_i v_i)\), \(\sum e_i=1\), and use side widths \(\log(1+(\log H)^{-B_0})\) in the unnormalized logarithms of the primes. For all cells of interest the \(e_i\) are bounded away from zero. Every prime \(n-2\) on this support is odd and exceeds \(H^u\). Apply Lichtman's Theorem 2.10 to the sequence of shifted products from this single rectangle with \(z=H^u,D=H^\theta\), using the odd primes and \(g(d)=1/\varphi(d)\) on odd squarefree \(d\). The integer sequence may be taken with multiplicity: the combinatorial inequalities are termwise and the remainder is linear. Alternatively impose an outer fixed collar around repeated-coordinate planes and work with disjoint prime intervals in each interior rectangle. The products then label actual distinct elements. The discarded collars have the same positive majorization and vanish when their width tends to zero.

The remainder uses exactly \(d\mid P(H^u)\), \(d\le H^\theta\), residue 2. The empty-prefix case of Corollary 5.6, equation (5.24), is the fixed-product analogue of the explicitly written empty-vector case of Proposition 5.4. The proof replaces Theorem 2.5 by Proposition 5.5 in the same factorization, which leaves the smooth squarefree condition on \(d\) intact. It gives arbitrary fixed logarithmic savings with the principal product count restricted by \((n,d)=1\). The inequality \(\theta<(3-u)/5\) has fixed slack before any limit. All Hölder or sieve parameters denoted by \(\varepsilon\) in the paper can be chosen strictly smaller than that margin and the minimum prime exponent. To replace the primitive count by the full count, bound the total harmonic cost per tuple by

\[
\sum_{p\mid n}\sum_{p\mid d\mid P(H^u),\ d\le H^\theta}
\frac{|\widetilde\lambda^+(d)|}{\varphi(d)}\ll_{r,\varepsilon}H^{-c'}(\log H)^C
\]

for a common fixed \(c'>0\). This follows by writing \(d=pe\), using squarefreeness and the divisor-boundedness of the weights in Theorem 2.10. There are at most \(r\) colliding primes and each is at least \(H^{c'}\). The product \(V(z)=\prod_{2<p<z}(1-(p-1)^{-1})\) satisfies the dimension-one condition (2.3) and is asymptotic to \(\mathfrak S_2e^{-\gamma_E}/\log z\). With \(s=\theta/u\) we have \(1<s<3\), hence \(F(s)=2e^{\gamma_E}/s\). The resulting bound for each cell is its ordinary count times \((\mathfrak S_2/\log H)(2/\theta+O(\varepsilon)+o(1))\) plus \(O_A(H(\log H)^{-A})\). The implicit constant in the main-term \(O(\varepsilon)\) is uniform in the cell because the density is unchanged.

For completeness, a deterministic positive cover matches the variation of \(H\) across cells. Use the grid with unnormalized log side \(h_0=\log(1+(L+2)^{-B_0})\), keep all rectangles meeting the original dyadic, ordered support, and enlarge them downwards from the same upper endpoints to the exact published side at \(H\). For all retained rectangles \(\log H\in[L-\log 2,L+1]\) for large \(x\). Thus the enlarged side is between \(h_0\) and \((1+O_{B_0}(1/L))h_0\), and each retained point is covered. Use the supremum of \(W\) over the original cell as its nonnegative coefficient. PNT with its usual log-power remainder shows uniformly that the ordinary count of labeled prime tuples in each original or enlarged rectangle is \((1+o(1))\) times the product of its one-dimensional log integrals: their lower endpoints are fixed positive powers of \(H\) and their multiplicative widths are powers of \(1/\log H\). The ratio of the enlarged to original integrals is \(1+o(1)\) uniformly. The weighted sum of original integrals, divided by \(x/(2L)\), tends to \(\Pi(W)\). Indeed the change of variables \(T=\sum_i v_i,\ t_i=v_i/T\) turns the product density into \((e^T/T)dT\,dt_1\cdots dt_{r-1}/\prod t_i\). The window boundaries have log thickness \(O_r(h_0)\), and angular collars around the finitely many planes have vanishing measure on a compact region. Multisets near equality faces are included in this upper cover. There are \(O((L/h_0)^r)\) cells, absorbed by the arbitrary fixed precision \(A\). The genuine-prime weight is \(\log(n-2)\le L\); \(L/\log H=1+o(1)\) uniformly. First let \(x\to\infty\), then the sieve approximation error tend to zero, then \(\theta\uparrow9/16\). The comparator normalization in `analytic_packet.md` gives (1). [Lichtman, Theorem 2.10, Proposition 5.4, Corollary 5.6](https://arxiv.org/html/2109.02851v2)

## Rank-four signed divisor bound

On squarefree rank-four \(n\in I\), write \(t_i=\log p_i/\log n\), \(s_A=\sum_{i\in A}t_i\), \(B_0'=\{i:\nu\le t_i\le1/5\}\). The original marked kernel \(K\) vanishes. Indeed a nonzero marked divisor has three distinguished prime factors and a cofactor strictly greater than one. With four primes it must use the whole integer. Its bank upper exponents sum to \(.028+.0115+.0125+.465=.517<1\), so this would give \(n\le(x/2)^{.517}<x/2\).

The reference signed sum \(\sum_{s_A<1/2}(-1)^{|A|}\) vanishes. Complementary subsets have the same sign at even rank and exactly half contribute; equality would make the squarefree \(n>1\) a square. The full alternating sum is zero. In the actual \(H\), a subset containing an exceptional coordinate in \(B_0'\) has zero coefficient. On subsets avoiding \(B_0'\), its coefficient is precisely the Möbius sign when both native cutoffs pass and zero otherwise. Indeed every designated large coordinate exceeds \(1/5\); if its selected sum is at most \(\beta\), there are at most two such coordinates and `g0` has the required sign. Every subset with \(s_A\le\beta\) passes both cutoffs and no subset with \(s_A\ge1/2\) contributes. It follows that the discrepancy after deleting the exceptional coordinates is bounded by \(\sum_{\varnothing\ne A\subsetneq[4]}1_{\beta<s_A<1/2}\).

Delete the exceptional coordinates one at a time in the reference sum. The signed change from one deletion has absolute value at most two. Its magnitude is the absolute alternating sum of a downward-closed threshold family on at most three other coordinates. An empty family contributes zero. If the triple occurs, the sum is zero. Otherwise it is \(1-j+k\), where \(0\le j\le3\) is the number of allowed singletons and \(0\le k\le\binom j2\) is the number of allowed pairs. In all cases it lies in \([-2,1]\). This proves the pointwise native bound

\[
|H(n)|\le 2\sum_{i=1}^4 1_{\nu\le t_i\le1/5}+
  \sum_{\varnothing\ne A\subsetneq[4]}1_{\beta<s_A<1/2}.                     \tag{2}
\]

On the omitted sector \(W_4\) all other masks are indicators, and its support has \(t_i\ge\delta\). For the symmetric simplex bound one can therefore drop the off-good mask and divide by \(4!\) on the labeled simplex. For a block of \(h\ge1\) coordinates with total \(v\), the convolution density of \(dt/t\) truncated below \(\delta\) is at most

\[
K_h(v)\le\frac{h}{v}\big(\log(1/\delta)\big)^{h-1},\quad \delta\le v\le1.
\]

For \(h=1\) this follows directly. For \(h>1\), multiply the reciprocal product by \(v=\sum t_i\) and integrate the resulting \(h\) terms, using \(\int_\delta^1 dt/t\) for each free variable. The first term in (2) has multiplier \(2\cdot4\cdot1\cdot3/4!=1\). The second has multiplier \(\sum_{j=1}^3\binom4j j(4-j)/4!=2\). Therefore

\[
\Pi(|W_4|)\le \log^2(1/\delta)\left[\int_\nu^{1/5}\frac{dt}{t(1-t)}+2\int_\beta^{1/2}\frac{dt}{t(1-t)}\right]
\le 27^2\left[\frac{2\epsilon}{\nu(1-\nu)}+\frac{4\epsilon}{\beta(1-\beta)}\right]=:E_4.
\tag{3}
\]

Apply (1) to \(W_4^+,W_4^-\), preserving each comparator. For the upper bound on \(R_4\) the coefficient is \((32/9-1)\Pi(W_4^+)+\Pi(W_4^-)\). The reverse direction interchanges the signs. Thus \(\limsup |R_4|/S_b\le(23/9)E_4<0.000053095501\). The earlier quoted absolute cap was \(0.000107163\). This full rank-four numerical comparison has no unpaid rank-four companion.

## The full high-rank tail

On a squarefree output of rank \(r\), \(|H|\le 2^r\) by the divisor count. The three named prime banks in \(K\) are disjoint, including their common half-open endpoint. For sufficiently large \(x\), each marked prime exceeds \(n^{.01}\), since all lower bank exponents measured against \(x/2\) are at least .0105. Fewer than 100 such primes can divide \(n\) altogether. If their bank counts are \(r_u,r_v,r_w\), their product is at most \((100/3)^3<64^3\). For each divisor the general cofactor is prescribed once its three labels are fixed, so \(\mathrm{labels}(x/2,d)\le r_ur_vr_w\). The smooth multiplier has absolute value at most one for every \(d\mid n\). Thus \(|K|\le 2^r\). Consequently \(|W_r|\le2^{r+1}\) on the degree-\(r\), \(x^\delta\)-rough squarefree support. By the convolution bound used in (3) its unweighted ordered reference mass is at most \(27^{r-1}/(r-1)!\). Apply (1) to this unweighted nonnegative rough profile (its threshold can move by \(O(1/L)\)), retain the sum of the absolute actual and comparator costs, and sum first over the *fixed finite* range \(256\le r\le\lfloor1/\delta\rfloor\). Extending the resulting numerical envelope to infinity gives

\[
\limsup \frac{|R_{\mathrm{tail}}|}{S_b}
\le\left(\frac{32}{9}+1\right)4\sum_{m\ge255}\frac{54^m}{m!}
\le\frac{41}{9}\frac{4\cdot54^{255}}{255!\,(1-54/256)}<4\cdot10^{-62}.
\tag{T}
\]

The published fixed-product theorem is used separately at each fixed rank before the numerical series is extended, so no uniformity theorem in rank is required. This supplies `Ledger.Estimates.tail` at paper level. The old debit \(10^{-58}\) is retained in the rounded headline to ease comparison.

## Good and rank-two debit and the exact splice

The original off-good rank-two source equals the nonnegative indicator of the band \(\nu\le t\le a\) for the smaller prime logarithm, up to immaterial face conventions. To verify the classification for \(n=pq\), note that only the smaller prime can appear in a nonempty divisor below \(n^\gamma\). Its coefficient is \(-1\) if \(t<\nu\) or \(1/5<t\le\beta\) and is zero otherwise. Thus \(H\) is supported on \([\nu,1/5]\) and \((\beta,1/2)\). On the second band and on \((a,1/5]\), `rankTest` holds by assigning 1 to the smaller coordinate and either 1 or 2 to the larger so that its excess is zero. If \(\nu\le t\le a\) the smaller coordinate can be assigned no positive rank and its excess alone exceeds \(\epsilon\), so the good test fails. The mark vanishes. Put \(I_2=\int_\nu^a dt/(t(1-t))\) and \(I_2^*=\epsilon/(\nu(1-\nu))\). The good-positive source \(P\) has active rank at most five with each prime exponent at least \(\nu\); it is the exact finite piecewise angular kernel given by the pinned `Collar` and `GoodSupport` code. With \(J_p=\Pi(P)\), (1) gives

\[
\liminf\frac{B(P)-A(P)-R_2}{S_b}\ge-\frac{23}{9}(J_p+I_2).
\tag{4}
\]

The original bound \(J_p\le J_{\rm rat}\) can also be reconstructed using `Collar`'s pointwise rank classifications and the ordered integral. At rank two the two positive intervals contribute at most \(\epsilon/[a(1-a)]+2\epsilon/[\beta(1-\beta)]\). At rank three the positive case has height one and the two smaller coordinates in \((a,1/5]\); the largest coordinate is at least \(3/5\). The associated triangular region gives an upper \(\epsilon^2/[2a^2(3/5)]\). Rank four contributes zero. At rank five every coordinate exceeds \(a\) and the height is at most three. Translating by \(a\) in all five coordinates leaves slack \(5\epsilon\). The ordered integral is bounded by \(3(5\epsilon)^4/[5!4!a^5]\), since the full labeled simplex has four-dimensional coordinate volume \((5\epsilon)^4/4!\) and the symmetric bound splits equally among all orderings. Every larger rank is inactive. The sum of these four terms is exactly the repository's `goodRational`. Thus (1) supplies `Ledger.Estimates.goodMass` at paper level, and the rank-two formula supplies `Ledger.Estimates.pairs`.

The unsimplified identity `Ledger.exact_ledger` therefore gives the following unconditional strengthened estimate at paper level, in which every additional signed term is shown on its physical side:

\[
\liminf\frac{\mathcal C+T+R_{\rm tail}-\operatorname{deviation}(\mathrm{calibrated})-\mathrm{powerError}+\mathrm{normalError}}{S_b}
\ge 1-\frac{23}{9}(J_p+I_2+E_4).                                      \tag{5}
\]

Here \(\mathcal C=\mathrm{Closing.covariance}\). The upper or absolute bounds used on the left to recover the simplified lower terminal ledger are separate dependencies. `analytic_packet.md` proves \(\mathrm{normalError}=o(S_b)\) and comparator normalization, and the native code then supplies the prime-power payment. The `transferCap` for the complete calibrated mean and the transition \(\mathcal C=\mathcal U+o(S_b)\) require independent verification for a simplified conclusion. If one retains those inputs, the lower coefficient is at least \(0.999946852110\), rounded down, and with the inherited five-box cap the sufficient outside threshold becomes \(0.317068756575\), rounded down. The original unrounded lower constant was \(0.99989277549999972656\ldots\); the change is \(0.00005407661093649536\ldots\) in that conditional lower computation. Formula (5) itself uses no hypothesis about the outside source or twin primes. It gives no bound on the unestimated \(\mathcal U_{\mathscr B^c}\) and establishes no unconditional twin-prime reserve.
