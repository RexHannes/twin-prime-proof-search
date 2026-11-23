# A genuine adverse cohort past every fixed exact small-factor elimination

For every integer $J\ge1$ there is $t_J>0$ such that for every fixed $0<t<t_J$ and every sufficiently small fixed $\epsilon>0$, the exact compensated physical sum of *Concentrating the complete signed upper* contains a population $\mathcal A_{J,t}$ with
$$
 \liminf_{x\to\infty}\frac1{S_b}\sum_{k\in\mathcal A_{J,t}}
 R_{x^\epsilon}(k)\mu^2(k)
  [f_+(k+2)b_{0,J}(k)-f_-(k+2)b_{1,J}(k)]
 \;>\;\frac{1}{100t}.
\tag{1}
$$
Every row in this cohort is nonnegative and every input has exactly $J+1$ prime factors below $Y=x^t$. The coefficient $1/100$ works for every fixed $J$. The parameters giving its onset, and the scale in $x$, depend on $J$. The output is the real native outside profile, including both physical signs, with $\Pi(f_-)>1.64$ as proved on the balanced-triple chamber in *Full source certificate comparison*. In particular the assertion has a fixed cost in $S_b/t$ units from the genuine joint source.

## Selecting the small labels

Write $r=J+1\ge2$, $S=\{p\mid k:p\le Y\}$, and $m=\#\{Y<p\le H:p\mid k\}$, with $H=x^{1/2-(J+2)t}$. The exact recursion gives $b_{v,J}(k)=-c_v(S)$ on $|S|=r$ for composite $k$. Indeed including the single omitted subset $T=S$ in (2) would cancel the entire coefficient by (1) in that paper. Write
$$
 c_v(S)=(vm-1)\log k\,a(S)+d(S).
$$
Here $a$ is the sharp integer-valued inverse in *The sharp recursive correction has nondecaying signed harmonic coefficients*. The remaining log-weighted term has $|d(S)|\le C_r r t L$, by induction on the finite subset recurrence using $|M(T)|\le2^{|T|}$ and $\sum_{p\in T}\log p\le rtL$.

For coordinates $u_i=\log p_i/\log Y$, the harmonic integral of $a$ on $[1/V,1]^r$, divided by $r!$, tends as $V\to\infty$ to
$$
 h_r=[w^r]\exp\!\left(\sum_{j\ge2}\frac{\zeta(j)}j w^j\right)
 \ge [w^r]\frac{e^{-w}}{1-w}=\frac{!r}{r!}\ge\frac13 .
$$
Both series in the exponent have nonnegative coefficients and $\zeta(j)\ge1$. The final alternating sum $\sum_{i=0}^r(-1)^i/i!$ is at least its two successive minima at $r=3$ and subsequent odd terms, by grouping the remaining adjacent terms. Choose a finite $V=V_J>1$ such that
$$
 A=\frac1{r!}\int_{[1/V,1]^r}a(S)_+\prod_i du_i/u_i\ge\frac14 .
\tag{2}
$$
These constants and the fixed region precede the choices of $t,\epsilon$. Since $a$ depends on finitely many subset sum comparisons it is bounded and constant off finitely many faces at this fixed $r$. The reciprocal-prime sum with this weight converges to $A$ by Mertens on polynomial intervals and subdivision of its faces.

Take $t_J$ small enough that $U^8<H$ for $U=Y$, $1/4+(r+24)t<.49$, and $|d(S)|\le\tfrac12\log k$ throughout for sufficiently large $x$. Also impose $t<1/[6(J+2)]$ as in the original recurrence. In the genuine cohort require all of the following.

- There are exactly $r$ small primes and they all lie in $(Y^{1/V},Y]$ with $a(S)>0$.
- At least one prime factor lies in $(Y^2,Y^4]$ and at least one in $(Y^4,Y^8]$.
- The input $k$ is squarefree and $k+2$ lies in the native dyadic interval.

Then every prime of $k$ exceeds $x^{t/V}$, so any $\epsilon<t/V$ gives the requested polynomial input presieve. We have $a(S)\ge1$ and $m\ge2$, whence
$$
 b_{0,J}=a(S)\log k-d(S)\ge0,\qquad
 -b_{1,J}=(m-1)a(S)\log k+d(S)\ge\tfrac12 a(S)\log k .
\tag{3}
$$
In particular negative outputs are adverse with their true sign, and positive outputs cannot offset them on this population.

## Paying the joint shifted incidence

The positive-moment method in *A quantitative adverse population in the fixed-power compensated source* applies with weight $a(S)_+$. Here are the modulus and normalization checks. In the measure $f_-(k+2)a(S)_+$ impose exactly the displayed $r$ small primes, and let $N_i$ count the primes in the two material medium bands. For $Z=N_1N_2$ its first moment has main lower $(1-\theta_t+o(1)) V_Y\sum_I f_- A\lambda^2$, and its second moment upper is $(1+\theta_t+o(1))V_Y\sum_I f_- A(\lambda+\lambda^2)^2$. Here $\lambda=\log2$, $V_Y=\prod_{2<p\le Y}(1-1/(p-1))$ and $\theta_t\to0$ as $t\downarrow0$.

To prove these estimates, expand $N_i^2=N_i+2\binom{N_i}{2}$, and choose an unordered set of $r$ small labels. Each simultaneously occupied input has just one exact small set. With $d$ the product of the $r$ labels and at most four distinct medium tags, require $d\mid k,\ P^-(k/d)>Y$. Insert the two dimension-one fundamental-lemma weights at level $x^{1/4}$ for the latter cofactor. The folded modulus $dc\le x^{1/4+(r+24)t}$ permits the native product progression estimate at fixed shift. For a given modulus the fixed number $r+4$ of labels costs at most a fixed power of $L$, and $a(S)_+$ is bounded for this $J$. Primitive exclusion of an output prime costs $O_{J,t,V}(x^{-\zeta}L^C)$ per output. A collision between a named small prime and a sieve-divisor prime costs $O_{J,t,V}(x^{-t/V}L^C)$ per output by removing the repeated prime from the absolute reciprocal sum. Removing the other nonsquarefree physical inputs incurs $O_{J,t,V}(x^{1-t/V}L^C)$. At this fixed $J,t,V$ all are negligible at the required scale. The principal sieve factor has relative error $θ_t\ll (1/(4t))^{-1/(8t)}$ at sufficiently small $t$. The signed progression remainder is handled with arbitrary log precision and the absolute label loss only there. The harmonic order of the distinct medium tags gives $\lambda,\lambda^2$, respectively, with its diagonal squared-reciprocal error vanishing. This proves the two moment estimates for the stated weighted measure.

Positive Cauchy–Schwarz on these moments yields, on $Z>0$, a measure mass at least
$$
 (1-o(1))V_Y\sum_I f_- A
 \frac{(1-\theta_t)^2}{1+\theta_t}
 \left(\frac{\lambda}{1+\lambda}\right)^2 .
$$
Now $V_Y\sim\mathfrak S_2 e^{-\gamma}/(tL)$, $\sum_I f_-\sim\Pi(f_-)x/(2L)$ and $\log k/L\to1$ uniformly. Multiply by (3), use (2), and choose $t_J$ small enough that $\theta_t\le1/10$. The normalized lower in (1) is at least
$$
 \frac1{8t}e^{-\gamma}\Pi(f_-)
        \frac{81}{110}\left(\frac{\log2}{1+\log2}\right)^2
 \;>\;\frac1{100t},
$$
using $e^{-\gamma}>.55$, $\Pi(f_-)>1.64$ and $\log2>.69$. These are the same constant bounds audited in the companion positive-moment argument.

## Scope of the adverse charge

For each fixed $J,t$ the complete polynomially presieved compensated source approximates the original complete source within one unit of $S_b$ by taking $\epsilon$ sufficiently small. The actual adverse contribution (1) must then be accompanied by favorable signed compensation elsewhere if the complete upper stays bounded. Some of that compensation can lie in the discarded zero-small terms, so (1) alone gives no lower bound for the *net* $T_{>J,z}$. Its uniform coefficient does invalidate an estimate that bounds the total positive part of this exact remainder by a quantity tending to zero solely by choosing large $J$ uniformly across the allowed choices of $t$. It places no restriction on a genuinely signed estimate exploiting the required companion.
