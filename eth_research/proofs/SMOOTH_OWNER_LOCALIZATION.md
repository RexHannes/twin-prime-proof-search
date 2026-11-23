# Smoothing the two inner cutoffs in the REAL 1B outside source

The statements below concern the project at commit `43facedcf40b2f998aa47f7198d6b9b5feb5b792`. The result is an absolute tail estimate for a smooth decomposition of the complete physical sum. Its main application is to restrict the joint input and output factor profiles to compact, bounded-rank domains at any prescribed error tolerance. The signed estimate on those domains remains open. No fixed positive terminal saving follows.

## 1. Source and statement

Write $L=\log x$, $k=n-2$, $I_x=\{n:x/2<n\le x\}$, $V=x^{0.24}$, $w=\exp(L^a)$ for fixed $0<a<1$, and $R_v(k)=1_{P^-(k)>v}$. Write $M_{u,d}(k)$ for the original owner coefficient with unchanged prime cutoff $V$, inner divisor cutoff $x^u$, and product cutoff $x^d$. Thus
$$
M_{u,d}(k)=\sum_{\ell\mid k,\,\ell>V\ {\rm prime}}(\log\ell)
 \sum_{b\mid k/\ell}\mu(b)1_{b>x^u}1_{b\ell>x^d}.
$$
Let $f_x(n)=\Phi_x(n)-\psi_x(n)$ be the native outside profile. Its original squarefree, good, retained, marked cofactor, and outside-box selectors are all included. Set $\zeta=1/(4\cdot10^{11})$. On this window $f_x(n)\ne0$ implies $P^-(n)>x^\zeta$, and $|f_x|\le M=2(2^{255})^4$. The definition of $F$ enforces roughness. For $G$, an active kernel on a squarefree good output is rough by `GoodSupport.active_rough`. The size bound follows from `GoodSupport.uniform_phi` and `Direct.outside_eq_mask`.

Choose two fixed nonnegative smooth probability densities supported in the interiors of $J_u=[.23,.24]$ and $J_d=[.48,.49]$ and average $M_{u,d}$ independently against them. Denote the result by $\overline M(k)$. All averages take place at one physical $x$. For $0<\delta<.23$ and integers $K\ge1$, define the retained sum
$$
 C_{\delta,K}(x)=\!
 \sum_{n\in I_x}\! R_w(k)\mu^2(k) f_x(n)
 \sum_{\substack{\ell\mid k,\ \ell>V\ {\rm prime}\\r=k/\ell>1,\ P^-(r)>x^\delta,\ \omega(r)<K}}\!
 (\log\ell)\,
 \mathbf E_{u,d}\sum_{b\mid r}\mu(b)1_{b>x^u}1_{b\ell>x^d}.
$$
For fixed $\delta$ and large $x$, $R_w(k)=1$ on every retained row. The actual ordered sum includes every eligible prime owner of its input. The test $\omega(r)<K$ counts the quotient of that owner.

**Theorem A.** For any test $g_x$ bounded by $M$ and supported on $P^-(n)>x^\zeta$ in $I_x$, the sum of absolute values of all averaged rows discarded from $C_{\delta,K}$, with $g_x$ in place of $f_x$, is
$$
 \ll_{M,\zeta,\mathrm{densities}} (\delta + 2^{-K})\,x/L.
$$
The constant is independent of $a,\delta,K,x$. Rows with $r=1$ are identically zero. The entire averaged sum of absolute row values is $O(x/L)$ with the same dependencies. More generally, a multiplier $e^{-cK}$ can replace $2^{-K}$ with a constant depending also on $c>0$.

**Theorem B (transfer from the sharp native endpoint).** Under the fixed-profile prime-product progression estimate (PC) of Gold 4.66, Part II §3.2, for $f_x$ and $|f_x|$, uniformly on the fixed ranges above,
$$
 \mathcal U_{u,d}(f)=A(f)-\mathfrak S_2\sum_{n\in I_x} f_x(n)+o(x/L).
$$
Here $A(f)=\sum_{n\in I_x}R_{y}(n)1_{n-2\in\mathbb P}\log(n-2)f_x(n)$, $y=\exp(L^{1/20})$ and $\mathfrak S_2=2\prod_{p>2}(1-(p-1)^{-2})$. Section 5 gives a proof using (PC) and the classical Möbius prime number theorem. The hypotheses of (PC) and the author's explicit transfer for the finite native profile are stated there. At that level of analytic verification,
$$
 \mathcal U_{\mathscr B^c}(x)=C_{\delta,K}(x)
       +O((\delta+2^{-K})x/L)+o(x/L).
$$
Only the total sharp sum participates in this equation. Individual sharp rows can have discontinuous changes under smoothing. They must never be charged against the smooth tail estimate row by row. This also preserves the genuine-prime boundary, including its exact cancellation with the $b=1$ prefix on $r=1$.

## 2. Smooth row and the finite difference

Let $F_u,F_d$ be the two cumulative distributions. For $0\le s\le1$ and $.24\le\lambda\le1$ put
$$
 h_\lambda(s)=1-F_u(s)F_d(s+\lambda).
$$
Multiply this smooth function on the real line by a fixed smooth compactly supported cutoff identically one on $[0,1]$. All its derivatives then have uniform $L^1$ bounds in $\lambda$. Fourier inversion gives
$$
 |\widehat h_\lambda(t)|\le C_j(1+|t|)^{-j}
$$
for every fixed integer $j$, allowing a consistent $2\pi$ convention. If $r>1$ is squarefree, the averaged inner tail equals
$$
 -\sum_{b\mid r}\mu(b)h_\lambda(\log b/L)
 =-\frac{1}{2\pi}\int_{\mathbb R}\widehat h_\lambda(t)
     \prod_{p\mid r}(1-e^{it\log p/L})\,dt,
 \qquad\lambda=\log\ell/L.
$$
The sign comes from $\sum_{b\mid r}\mu(b)=0$. For $r=1$ the correct full formula is $1- h_\lambda(0)=0$. In particular, inserting only the negative prefix at $r=1$ is an error of one full prime row.

For uniform bounding put $b_t(p)=\min(2,|t|\log p/L)$. Each row is bounded by the integral of $C_j(1+|t|)^{-j}\prod_{p\mid r}b_t(p)$, independent of which prime labels are possible for this $r$.

## 3. An upper bound retaining the large prime label

Fix a squarefree odd $r\le x/V$. Every contributing $\ell$ is prime, exceeds $V$, and satisfies $P^-(r\ell+2)>x^\zeta$ and $\ell\le N=x/r$, where $N\ge x^{.24}$. For odd $p\le z=x^{\min(\zeta,.001)}$, sieve the residue roots of $Y(rY+2)$. Their count $\nu_r(p)$ equals 2 if $p\nmid r$, and 1 otherwise. Applying Montgomery's large sieve inequality with $Q=\lfloor N^{1/3}\rfloor$ bounds the count by $(N+Q^2)/G(Q)$ up to a harmless integer rounding term, where
$$
 G(Q)=\sum_{q\le Q,\ q\mid\prod_{2<p\le z}p}
            \prod_{p\mid q}\frac{\nu_r(p)}{p-\nu_r(p)}.
$$
In the full product mass each $p$ occurs independently with probability $\nu_r(p)/p$. Thus the mass fraction with $q>Q$ is at most $\sum_{2<p\le z}\nu_r(p)\log p/(p\log Q)<1/2$ for sufficiently large $x$, by Mertens' estimate, $\log Q\ge .079L$, and $\log z\le .001L$. Mertens and the convergent quadratic correction now give
$$
 G(Q)\gg_{\zeta} L^2/\sigma(r),
 \qquad \sigma(r)=\prod_{p\mid r,\ p>2}\frac{p-1}{p-2}.
$$
Consequently the sum of $\log\ell$ over these prime labels is $\ll_\zeta x\sigma(r)/(rL)$. A fixed even $r$ has zero output for all sufficiently large $x$, since $r\ell+2$ is even. This argument bounds all labels, even if the same physical integer occurs for several labels. Dropping the extra coprimality restriction $\ell\nmid r$ at this upper-bound step is valid.

## 4. Positive harmonic Euler products

For fixed $y\ge1$ the positive product
$$
 \prod_{p\le x}\left(1+\frac{y\sigma(p)b_t(p)}p\right)
       \ll_y (2+|t|)^{2y}
$$
is uniform in $x,t$, with $\sigma(2)=1$. In fact $\sigma(p)=1+O(1/p)$, so the correction contributes $O_y(1)$ to the logarithm. For $1\le |t|\le L/\log2$, split at $x^{1/|t|}$. The small primes contribute $O(1)$ by $\sum_{p\le z}\log p/p\ll\log z$; the rest contribute at most $2\log |t|+O(1)$ by Mertens. The two exterior ranges follow from the same elementary bounds.

To cover $P^-(r)\le x^\delta$, mark one such prime and use
$$
 \sum_{p\le x^\delta}\frac{\sigma(p)b_t(p)}p\ll |t|\delta .
$$
To cover $\omega(r)\ge K$, multiply by $2^{\omega(r)-K}$ and use $y=2$. Extending the remaining positive sum over squarefree $r\le x/V$ to the Euler product over all primes through $x$ gives the required bound. Taking $j=9$, for example, already makes both Fourier integrals absolutely convergent. The use of absolute values here occurs after the complete inner Möbius sum for each physical owner. This is the part of the proof which fails for the original sharp discontinuous cutoff.

One may also remove or introduce the original subpower $R_w(k)$ in the averaged source at absolute cost $O((\log w/L)x/L)$. The proof of section 3 includes the singular factor for *all* odd $r$, so it continues to apply when $r$ is not $w$-rough. The prime $\ell>V$ cannot be the small factor for large $x$.

## 5. Exact sharp-to-smooth source contract

This comparison uses an analytic input distinct from Theorem A. Write (PC) for the following maximal primitive average on the actual output: for each $B>0$, each fixed $\eta>0$ and uniform dyadic prefixes $x/2\le T\le x$, the sum over odd $q\le x^{1/2-\eta}$ of the absolute discrepancy of $f_x$ in residue $2\pmod q$, compared to $\varphi(q)^{-1}\sum_{(n,q)=1} f_x(n)$ over the same interval, is $O_B(xL^{-B})$. The same estimate applies to $|f_x|$. Outputs are polynomially rough with at most 255 distinct prime factors.

Liu–Park–Song Theorem 3.2 supplies the underlying estimate for fixed products of distinct primes in interval boxes, primitive average included. The bound there is uniform in the factor endpoints. Gold 4.66, Part II §§3.2 and 3.8, gives the adapter to $f_x$: partition the fixed finite ranks by a sufficiently fine inverse-logarithmic grid, resolve selector faces that are identically equal on the sum hyperplane, and cover the finitely many transverse faces by collars. The ordinary collar bound $O_f(hx/L+xe^{-c_f\sqrt L})$ follows by PNT partial summation on polynomial factor ranges. Cauchy–Schwarz with $\sum_{k\le x}\tau(k)^2\ll x L^3$ pays the progression incidences. The primitive collar costs $O(L)$ times its population. Mesh precision and the BV log saving are then chosen in that order. A dyadic prefix between $x/2$ and $x$ can be taken as the base parameter with exponent one, rescaling the factor endpoints and using the fixed power margin on the modulus. The general-integer cofactor in $K$ remains a product of a subset of the actual factors. The original polynomial roughness renders the subpower mark cutoff automatic at sufficiently large $x$. The adapter is written analytic work and has not been kernel-replayed here.

For clarity, uniformity in the *new cutoff average* can be verified directly. For $U=x^u,D=x^d$ throughout the two compact ranges use the exact Vaughan identity on $k>V$:
$$
 \Lambda(k)= I_{U,V}(k)+
       \sum_{m>U,j>V,\ mj\mid k}\mu(m)\Lambda(j),\quad
 I_{U,V}(k)=\sum_{m\mid k,m\le U}\mu(m)\log(k/m)
 -\sum_{mj\mid k,m\le U,j\le V}\mu(m)\Lambda(j).
$$
All Type-I moduli $m,mj$ are at most $x^{.48}$, and the additionally subtracted short-product moduli are at most $D\le x^{.49}$. Bonferroni-fold the $w$-presieve at $R=\lceil C_B\log L\rceil$. Every combined modulus remains below $x^{.495}$ for all sufficiently large $x$. Its smaller-prime part recovers the presieve divisor uniquely. The sum of absolute representations of the remaining modulus is at most $O(L)$ after the logarithmic weight, since $\sum_{j\mid h}\Lambda(j)=\log h$. The Bonferroni remainder is controlled by the same (PC) for $|f_x|$; its principal factorial tail $\lambda_w^{R+1}/(R+1)!$, $\lambda_w=\sum_{2<p\le w}1/(p-1)=a\log L+O(1)$, pays any fixed logarithmic loss on taking $C_B$ large. The term containing $\log(k/m)$ uses partial summation and the prefix bound. All modulus and representation bounds are independent of the endpoints $u,d$.

For completeness, the uniform Euler estimate used after this fold is
$$
 A_{h,w}(t)=\sum_{m\le t,(m,2h)=1}\frac{\mu(m)R_w(m)}{\varphi(m)}
     =O_{A,c}(L^{-A}),\qquad
 B_{h,w}(t)=\sum_{m\le t,(m,2h)=1}\frac{\mu(m)R_w(m)\log m}{\varphi(m)}
     =-\mathfrak S_2(h)/g_w+O_{A,c}(L^{-A})
$$
for $x^c\le t\le x$ and $h$ with boundedly many prime divisors, all exceeding $w$. Here $g_w=\prod_{2<p\le w}(1-1/(p-1))$. To see this, divide the unrestricted odd-prime Dirichlet series by $1/\zeta(1+s)$. Its Euler correction is absolutely summable with weight $d^{1/8}$ including the bounded number of prime exclusions. The classical Möbius PNT then gives an arbitrarily large logarithmic saving for the unweighted partial sum and the derivative main term $-\mathfrak S_2(h)$ for the logarithmic sum. The extra $w$-presieve inverse Euler factors have positive coefficient mass $g_w^{-1}\ll\log w$; their Rankin moment of order $1/\log w$ is $O(\log w)$. Indeed $\sum_{p\le w}(p^{1/\log w}-1)/p=O(1)$ by Mertens. The tail beyond $\sqrt t$ is therefore a fixed logarithmic power times $\exp(-c'L^{1-a})$; any fixed extra log factors are absorbed by using half this Rankin exponent. This proves the two estimates uniformly. The first Type-I principal is
$$
 g_w\sum_n f_x(n)[\log(n-2) A_{n,w}(U)- B_{n,w}(U)]
 =\mathfrak S_2\sum_n f_x(n)+o(x/L)
$$
since the output factors are polynomially large and bounded in number.

For a prime power $j=p^i$ in the second Type-I term, the exact Euler expression is
$$
 \frac{1}{\varphi(p^i)}
 \{A_{np,w}(U)-p^{-1}A_{np,w}(U/p)\},\quad p\nmid 2n.
$$
The first term has polynomial argument. In the second, $p\le\sqrt U$ leaves $U/p\ge x^{.115}$, and $p>\sqrt U$ is killed by the extra $p^{-1}$ after the logarithmic sum. For the subtracted short-product block the corresponding difference for $V<\ell\le D/U$ is
$$
 A_{n\ell,w}(D/\ell)- A_{n\ell,w}(U)
 -\ell^{-1}\{A_{n\ell,w}(D/\ell^2)-A_{n\ell,w}(U/\ell)\}.
$$
The first two arguments are at least $U\ge x^{.23}$; the last two have the factor $1/\ell\le x^{-.24}$. Empty ranges give zero. The cumulated weights $\sum\log\ell/(\ell-1)$ cost $O(L)$. These explicit margins prove uniform savings for both principals. The prime-power replacement and the squareful deletion on $R_w$ also have cutoff-independent absolute errors. For example the long coefficient is at most $L\tau(k)$, the number of rough nonsquarefree $k\le x$ is $O(x/w)$ and Cauchy–Schwarz gives $O_M(xL^{5/2}/\sqrt w)$. For proper power labels $p^i>V$, $i\ge2$, the harmonic tail is $O(V^{-1/2}L^{O(1)})$ and the cofactor divisor average costs only logarithms. Genuine prime inputs in the original Mangoldt source automatically exceed $w$. None of these steps requires a favorable signed bound. The uniform asymptotic may now be integrated against the two fixed densities and subtracted from the original $(.24,.49)$ formula.

## 6. Open signed proof after the transfer

At fixed $\delta,K$, all prime factors of $k$ and $n$ in $C_{\delta,K}$ exceed powers of $x$. With sufficient slack in a proposed favorable constant one can first pay the error in Theorem A, then send $x$ to infinity. A proof would still need a signed estimate for the simultaneous factorization $n=\ell r+2$, including both signs of $f_x$. In particular, when $r=p>V$ is prime and $\ell p>D$ throughout the smooth supports, the full semiprime coefficient for $k$ is exactly $-\log k$: both owners contribute. For $f_x(n)<0$ these give positive terms to the outside bound. The localization does not pay this mass. Distinct labels on other retained inputs are present as well.

For an exact example set $x=1729$, $a=1/4$, $k=1727=11\cdot157$ and $n=1729=7\cdot13\cdot19$. Every output factor has logarithmic coordinate strictly between $1/4$ and $9/20$. Hence unit ranks witness the good set, its divisor kernel is $H=1-3=-2$, and the five-box profile vanishes. The proof uses $7^4>1729$, $19^{20}<1729^9$, so the strict $\epsilon$ collars are immaterial. Both input factors pass the $x^{.24}$ owner cutoff and $w<11$ because $\log 1729<8$ and $\log 11>2$. For every sharp or averaged cutoff here the summand equals $+2\log 1727$. A finite witness rules out a proposed pointwise sign inequality and gives no information on the density of that joint population.

The reproducible test `verify_owner_smoothing.py` exercises the strict original inequalities, the probability-box mixture, prime-boundary cancellation, the two-owner semiprime sign, the divisor-product Fourier identity, and decomposition by small-factor and rank masks on finite inputs. These finite tests do not certify an asymptotic theorem.

### Sources

- Native coefficient, integral, source and support: `RequestProject/REAL1B_20261122/FMClosing.lean`, `FMDirect.lean`, `FMGoodSupport.lean`, `FMUniform.lean`, at the commit identified above.
- Historical fixed-profile proof: `REAL1B_Gold4_66_FM_Complete_Proofs_20261123.md`, Part II, §§3.1–3.8. SHA-256 `4f1762f55a75d98f87c15e201c809a16c460c9c4c110d537bdb6161889384a2a`.
- Yang Liu, Peter S. Park and Zhuo Qun Song, *Bounded gaps between products of distinct primes*, Theorem 3.2 and its proof. https://doi.org/10.1007/s40993-017-0089-3
- Montgomery's large sieve inequality for sifted sets, Theorem 1 in Ernest S. Croot III and Christian Elsholtz, *On variants of the larger sieve*, https://www.math.tugraz.at/~elsholtz/WWW/papers/papers16actamathhungarica.pdf.
- The divisor Fourier product proof and its shifted prime-label application above are derived here. Granville–Koukoulopoulos–Maynard study the closely related role of smoothing in Möbius divisor-weight moments: *Sieve weights and their smoothings*, https://ora.ox.ac.uk/objects/uuid%3Ae98d42bb-2cb1-47b9-9809-14fb82499ab5.
