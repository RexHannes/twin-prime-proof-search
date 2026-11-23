# Removing the true semiprime inputs from the complete signed source

Let $I=(x/2,x]$, $L=\log x$, $k=n-2$, $w=\exp(L^a)$ with fixed $0<a<1$, and $S^\circ=\mathfrak S_2 x/(2L)\sim S_b$. Write $R_h(k)=1_{P^-(k)>h}$. The original complete sum $W(f)$ has the physical weight $R_w(k)\mu^2(k)B_{.24,.49}(k)$ and the native output $f=f_x(n)=\Phi_x(n)-\psi_x(n)$. The same argument applies to either sign of $f$ and to an individual fixed polyhedral output family, including the balanced triple. Take any finite sup bound $M$ for the chosen profile. Its active outputs have rank at most 255 and all primes exceed $x^\zeta$, where $\zeta=1/(4\cdot10^{11})$. In particular $\sum_I|f|\ll_f x/L$ by ordinary upper sieve. All limits below keep the signed outside normalization.

Fix $0<t<1/12$. Put $Y=x^t$, $H=x^{1/2-2t}$, $s=\prod_{p\mid k,\ p\le Y}p$, $m=\#\{p\mid k:Y<p\le H\}$, and $M_s(Y)=\sum_{e\mid s,e\le Y}\mu(e)$. Define
$$
 b_t(k)=1_{\mathbb P}(k)\log k+
          [(m-1)\log k+\log s]M_s(Y).
\tag{1}
$$
For the squarefree physical inputs this gives the complete fixed-$t$ identity
$$
 W(f)=\sum_{k+2\in I} R_w(k)\mu^2(k) f(k+2)b_t(k)+o_{a,t,f}(S_b).
\tag{2}
$$
Write $V_{\ge3,t}(f)$ for the same sum over $\omega(k)\ge3$. With $a(t)=\log((1/2+2t)/(1/2-2t))$, any fixed $\theta<1/2$ with $\theta>\zeta$, and the upper linear sieve function $F$,
$$
 \limsup_{x\to\infty}\frac{|W(f)-V_{\ge3,t}(f)|}{S_b}
 \le \frac{M e^{-\gamma}}{\zeta}F(\theta/\zeta)a(t).
\tag{3}
$$
In particular the successive limit of the left side as $t\downarrow0$ is zero. The original sharp semiprime physical sum need not tend to zero. Formula (2) transfers its bill to explicitly specified higher-rank coefficients.

## Divisor identity and the low-modulus comparison

First take the large-product coefficient with equal outer and inner thresholds $Y$ and product threshold $Y^2$. All divisors $e>Y$ paired with prime labels $p>Y$ automatically have $pe>Y^2$. On squarefree composite $k$ the complementary full divisor sum on $k/p$ is zero, leaving exactly $-M_s(Y)$ per large label. On prime $k$ the original row is zero. The resulting universal physical coefficient is
$$
 B^0_t(k)=1_{\mathbb P}(k)\log k-(\log k-\log s)M_s(Y).
\tag{4}
$$
At native threshold $Y_0=x^{.24}$ the difference between original and the coefficient (4) comes only from the labels $Y_0<p\le x^{.25}$ and divisors $Y_0<e\le x^{.49}/p$ of $k/p$. Their sign in the original-minus-equal-threshold difference is negative. On grouping by $pe\le x^{.49}$ there are at most two possible labels. The associated main divisor prefix is the difference of the truncated Möbius harmonics at $x^{.49}/p$ and $Y_0$, both polynomially large. Each is arbitrarily log-small. This proves $W(f)=\sum R_w\mu^2 f B^0_{.24}+o(S_b)$. Here and below every unindexed physical sum runs over $k+2\in I$.

For details, use the primitive progression estimate of *Uniform transfer from sharp cutoffs to an averaged outside sum*, equation (2), for $f$ and $|f|$, modulus $h\le x^{1/2-\delta}$ and fixed shift $2$. It follows from Liu, Park and Song Theorem 3.2 on bounded products of primes and the finite profile boundary mesh given in that paper. The same proof applies to a fixed balanced triple mask. Expand the subpower presieve by the two adjacent Bonferroni orders of size $O_A(\log L)$, so its divisor is $x^{o(1)}$. Use the unsigned profile for the absolute bracket. Physical moduli coprime to the presieve contain no primes $\le w$, so their split from the presieve part is unique. The factorial tail is smaller than any prescribed inverse power of $L$ after increasing the fixed order multiplier. The weighted sum of progression remainders permits arbitrary log losses. Each displayed row below has grouping multiplicity $O(L)$ or smaller. The common factor $\log k$ is inserted by prefix partial summation. Removing and restoring squarefree $k$ in these low-modulus sums costs $O_A(x L^{-A})$ by Cauchy–Schwarz from $O(x/w)$ rough nonsquarefree inputs, $\sum_{k\le x}\tau(k)^2\ll x L^3$, and the weights bounded by $O_t(L\tau(k))$. Maintain coprime factors in the regrouped moduli.

Write $g_w=\prod_{2<p\le w}(1-1/(p-1))$, $A_w(T)=\sum_{d\le T} \mu(d)R_w(d)/\varphi(d)$. Native prime input has $k>x/3>w$, so its explicit term is the actual unpresieved prime input. The companion paper *Reweighting every near-threshold input owner* proves both $A_w(x^v)=O_{a,c,A}(L^{-A})$ uniformly for $c\le v\le1$ and the approximate identity
$$
 g_wL A_w(x^v)\,dv\longrightarrow \mathfrak S_2\delta_0
\tag{5}
$$
on $v\ge0$, with bounded total variation and vanishing variation away from zero. It derives (5) from the classical Möbius PNT and the positive inverse Euler factors for primes at most $w$. In any prefix, removal of an individual prime $r>w$ from the divisors costs $O(L/(r-1))$ by the absolute harmonic prefix. Excluded primes of an active output cost $O_f(Lx^{-\zeta})$ in all. These estimates apply also at endpoints where the prefix is short.

Now let $0<t<1/4$, including $t=.24$. The complete mean of $f\log k\, M_s(Y)$ with its physical mask is $o(S_b)$, because its low-modulus terms $e\le Y$ have primitive $g_w A_w(Y)$ up to those output exclusions. Next expand $\log s=\sum_{w<r\le Y,r\mid k}\log r$ on this mask. For each label $r$, separate terms of $M_s(Y)$ containing $r$. On squarefree $k$, the resulting divisor sum is
$$
 \sum_{d\mid k/r}\mu(d)
 [1_{d\le Y}-1_{d\le Y/r}].
$$
All moduli $rd\le Y^2$ fit below one half with a fixed gap. Their total coefficient after grouping is bounded by $O(L)$ since $\sum_{r\mid h}\log r\le\log h$. The primitive for $\log s\,M_s(Y)$ per output, up to $o(1)$ uniformly, is therefore
$$
 g_w\sum_{w<r\le Y}\frac{\log r}{r-1}\,[A_w(Y)-A_w(Y/r)].
$$
The deletion of $(d,r)>1$, and of output primes from either argument or the label sum, incurs $o(1)$ since $r>w$ and the output is polynomially rough. The term at $Y$ vanishes. For $r\le x^{t/2}$ the second prefix is arbitrarily log-small. For $r>x^{t/2}$ expand $A_w(Y/r)$ over its divisors $d\le x^{t/2}$ and use the PNT to replace the prime logarithmic harmonic by $du/u$, uniformly in the endpoint $Y/d$. Its absolute $d$-sum is $O(L)$. Formula (5) then gives
$$
 g_w\sum_{w<r\le Y}\frac{\log r}{r-1} A_w(Y/r)
 =g_w L\int_0^{t/2} A_w(x^v)\,dv+o(1)\to\mathfrak S_2 .
$$
It follows from (4) that $\sum R_w\mu^2 f B^0_t=\sum_{k+2\in I}1_{\mathbb P}(k)\log k\, f(k+2)-\mathfrak S_2\sum_I f+o(S_b)$ for every fixed such $t$. This proves the retuning of (4) against the complete native source, including its original $(.24,.49)$.

To pass from (4) to (1), add $m\log k\,M_s(Y)$. For $Y<p\le H$ and $e\le Y$, $pe\le x^{1/2-t}$ and $p>e$. Its prime label is unique in each modulus: it is the only prime factor bigger than $Y$. Its primitive before the common factor $\log k$ is, up to super-logarithmically small output exclusions,
$$
 g_w A_w(Y)\sum_{Y<p\le H}\frac1{p-1}.
$$
For fixed $t$ the prime harmonic is bounded. This whole row has mean $o(S_b)$, proving (2).

## The residual semiprimes and the balanced negative output

On true prime $k$, (1) has $s=1,m=0$ and gives zero. On true semiprime $k=pq$, $p<q$, the large factor $q\ge\sqrt{x/3}>H$ for sufficiently large $x$. If $p\le Y$, then $s=p$ and $M_s(Y)=0$. If $Y<p\le H$, then $s=1$, $m=1$, and (1) vanishes again. Only $p>H$ survives, with coefficient $-\log k$. This covers every squarefree semiprime input including the exact inequality boundaries.

For $\beta=1/2-2t$, elementary prime partial summation on the semiprime dyadic interval gives total count $(a(t)+o_t(1))x/(2L)$, where $a(t)=\int_\beta^{1/2}du/[u(1-u)]$. Ordering $p<q$ handles the diagonal; replacing the moving endpoint $\sqrt k$ by its limiting exponent loses $o_t(x/L)$. The product progression estimate of Liu, Park and Song applies to this two-prime population at every fixed level $\theta<1/2$, with prefix and small subdivision of the boundaries as above. Sieve the actual shift $n=k+2$ at $x^\zeta$ using the upper dimension-one linear sieve. All sieving prime factors are $\le x^\zeta<H$, so every allowed input is coprime to every sieve divisor and the primitive is exactly the total mass divided by $\varphi(d)$. Mertens gives $g_{x^\zeta}\sim \mathfrak S_2 e^{-\gamma}/(\zeta L)$, and $\log k\le L$. Multiplying by $M$ proves (3). The constants in its final coefficient are independent of $t$. The threshold in $x$ and the vanishing remainder may depend on $t$.

For the balanced triple let $g=2$ on the squarefree three-prime outputs with all native coordinates in $(.2001,.4999)$, and zero elsewhere. Its native coefficient is $f_C=-g$. Here $M=2$ and every active output prime exceeds $x^{.2}$ eventually. Use $\theta\uparrow1/2$ and $F(u)=2e^\gamma/u$ for $1\le u\le3$ in (3) to obtain the upper cost $8a(t)$. On higher-rank inputs with $1<s\le Y$ the prefix vanishes. On $s=1$, a rank of at least three forces $m\ge1$ since $H^3>x$. Therefore $b_t(k)=(m-1)\log k\ge0$ and its contribution $-g b_t$ is favorable. On this slice the result is the genuine upper bound
$$
 \limsup_{x\to\infty}\frac{W(-g)+\sum_{\omega(k)\ge3,\,s>Y}
       R_w(k)\mu^2(k)g(k+2)b_t(k)}{S_b}\le8a(t).
\tag{6}
$$
The signed fragmented small-factor sum in (6) is unpaid. Its two physical signs can actually occur. The joint fixed-power version is obtained by the polynomial-presieve estimate below. For full signed $f$ the $s=1$ high-rank term is retained in (3).

## Fixed-rank version and order of the limits

Given a tolerance, choose $t$ first, then fix $0<\epsilon\ll\min(t,\zeta)$, and finally let $x$ tend to infinity. Replace $R_w$ by $R_z$, $z=x^\epsilon$, on the right side of (2). To check this replacement directly, apply the dimension-one fundamental lemma to the low-modulus comparisons above with auxiliary level $x^{t/2}$. Every marker has $pe\le x^{1/2-t}$ and every retuned base product $rd\le x^{2t}$. Use unsigned majorants for both physical signs. The $\epsilon$-rough harmonic over $e$ is $O(1/\epsilon)$ and $g_z L\ll1/\epsilon$. The marker prime harmonic is $O_t(1)$ and base $r$ weights sum to $O(L)$. With $E_u\ll u^{-u/2}$ the normalized majorant error is $O_{f,t}(\epsilon^{-2}E_{t/(2\epsilon)})$. The original subpower source is already compared to its unrestricted prime principal above.

The signed primitive prefix at $x^v$ converges uniformly to the Dickman function $\rho(v/\epsilon)$, through the finite harmonic rough-divisor expansion in *A polynomial input presieve for the unaltered signed FM outside coefficient*. Thus the marker and the $\log k$ portion of the retuned base cost $O_{f,t}(\epsilon^{-1}\rho(t/\epsilon))$ in normalized limsup. In the base logarithmic part, $\sum_{z<r\le Y}\log r/(r-1)\sim (t-\epsilon)L$. Its endpoint term at $Y$ has the same bound. Its integral $g_z L\int_0^{t-\epsilon} \rho(v/\epsilon)dv$ tends at fixed $\epsilon$ to $\mathfrak S_2 e^{-\gamma}\int_0^{t/\epsilon-1}\rho(u)du$. The exact endpoint $t/\epsilon-1$ accounts for the restriction $r>z$. In consequence the extra discrepancy on the retuned signed source is at most
$$
 O_{f,t}\!\left(\epsilon^{-1}\rho(t/\epsilon)
       +\int_{t/\epsilon-1}^\infty\rho(u)du
       +\epsilon^{-2}E_{t/(2\epsilon)}\right)S_b
$$
in normalized limsup, using $\int_0^\infty \rho=e^\gamma$. It vanishes for fixed $t$ as $\epsilon\downarrow0$. A first-moment expansion at $Y$ from the same paper equivalently absorbs the difference between the tails at $t/\epsilon-1$ and $t/\epsilon$ in the first error term by Dickman's delay identity.

The surviving true semiprimes $p,q>H$ automatically satisfy both presieves. Thus (3) gives a joint two-sided approximation to $W(f)$, within any prescribed error, by the explicit coefficient (1) on $R_{x^\epsilon}(k)\mu^2(k)=1$ and $3\le\omega(k)\le\lfloor1/\epsilon\rfloor$. The double limit cannot be taken as a uniform estimate for cutoffs depending on $x$. A signed estimate on this explicit fixed-rank population is still required for any terminal improvement.

## Sources

- Theorem 3.2 on finite prime products. [Liu, Park and Song](https://people.math.harvard.edu/~pspark/boundedgaps.pdf)
- Upper linear sieve, Lemma 2.5. [Matomäki and Zuniga-Alterman](https://www.utupub.fi/bitstream/handle/10024/185534/Matom%C3%A4ki_and_zuniga_weighted_sieves_2025.pdf?sequence=1)
- Fundamental lemma, Theorem 19.1. [Koukoulopoulos](https://dms.umontreal.ca/~koukoulo/documents/publications/primes.pdf)
- Dickman integral, Theorem 3.5.1. [Lagarias](https://doi.org/10.1090/S0273-0979-2013-01423-X)
