# The endpoint derivative in a smoothed Vaughan cutoff

Let $L=\log x$, $w=\exp(L^a)$ with fixed $0<a<1$, and $V=x^v$. A literal exponential divisor prefix is pointwise nonnegative on squarefree quotients:
$$
 \sum_{m\mid r}\mu(m)m^{-1/(cL)}
       =\prod_{p\mid r}(1-p^{-1/(cL)}).
$$
The following computation identifies the analytic change produced by giving the cutoff distribution mass down to exponent zero. Truncating the upper tail of the exponential also changes its pointwise factorization.

## The Euler moment

Let $h$ be a fixed smooth real function on $[0,\infty)$ supported in $[0,A]$, smoothly extendible past zero. For an odd integer $N$ with a bounded number of excluded primes, all greater than $w$, set
$$
 E_N(h)=
 g_w\sum_{\substack{m\ge1\\(m,2N)=1}}
 \frac{\mu(m)R_w(m)}{\varphi(m)}h(\log m/L),\qquad
 g_w=\prod_{2<p\le w}(1-(p-1)^{-1}).
$$
Then uniformly in such $N$,
$$
 E_N(h)=-\mathfrak S_2(N) h'(0)/L+O_h(L^{a-2}).
$$
The constant may also depend on $a$ and the fixed excluded-rank cap. The corresponding logarithmic moment is $-\mathfrak S_2(N) h(0)+O_h(L^{a-1})$. Here $\mathfrak S_2(N)=\mathfrak S_2\prod_{p\mid N,\ p>2}(p-1)/(p-2)$.

To verify this, write the associated Dirichlet series $F_{N,w}(s)=\sum_m \mu(m)R_w(m)1_{(m,2N)=1}/(\varphi(m)m^s)$ on $\Re s>0$ as
$$
 F_{N,w}(s)=\zeta(1+s)^{-1}G_N(s)
 \prod_{2<p\le w}(1-p^{-s}/(p-1))^{-1}.
$$
The exclusion correction $G_N$ and its first derivative are bounded uniformly in a fixed small neighborhood of $s=0$, by absolute convergence with a power of slack and the bounded number of excluded-prime factors. Also $G_N(0)=\mathfrak S_2(N)$. On $\Re s\ge0$, $|s|\log w=o(1)$, the logarithm of the finite Euler product divided by its value at zero differs from zero by $O(|s|\log w)$: differentiate the logarithm along the segment and use $\sum_{p\le w}\log p/(p-2)=O(\log w)$. Together with $\zeta(1+s)^{-1}=s+O(|s|^2)$ this gives
$$
 g_wF_{N,w}(s)=\mathfrak S_2(N)s+O(|s|^2\log w).
$$

Extend $H(u)=e^u h(u)$ to a compact smooth function on the real line. Fourier inversion yields
$$
 E_N(h)=(2\pi)^{-1}\int_{\mathbb R}\widehat H(\xi)
       g_wF_{N,w}((1-i\xi)/L)\,d\xi .
$$
The series is absolutely convergent on this vertical line. In fact its absolute sum is $O(L^{O(1)})$, since $\sum_p p^{-1-1/L}=\log L+O(1)$ and the remaining local errors are absolutely summable. On $|\xi|\le L^{(1-a)/3}$, use the near-zero expansion above; its integrated error is $O_h(L^{a-2})$. Rapid Fourier decay pays the complementary polynomial bound and any desired negative power of $L$. Integration of $1-i\xi$ gives $H(0)-H'(0)=-h'(0)$. Replacing $h(u)$ by $u h(u)$ and multiplying by $L$ establishes the logarithmic moment.

## The true prime-input calibration

Define $B_{h,v}$ by leaving $\ell>V$ a prime and replacing the condition $m>U$ by weight $1-h(\log m/L)$. The product cutoff may be $D=V$ and is then automatic on the relevant positive divisors; $h(0)=1$ ensures the unit has zero tail. Assume $v+A<1/2$ with fixed slack and the native fixed-profile progression contract for $f,|f|$. The signed whole sum satisfies
$$
 \mathcal U_{h,v}(f)
   =A(f)-[h(0)-(1-v)h'(0)]\,\mathfrak S_2\sum_n f_x(n)+o(x/L).
$$

The finite Vaughan identity is linear in the split $\mu=\mu h+\mu(1-h)$. Against $R_w(k)f_x(n)$ its first Type-I main is $[\log k\,E_n(h)-L E_n(t\,h(t))]$. Since $\log k=L+O(1)$ on the physical dyad, this equals $\mathfrak S_2(n)[h(0)-h'(0)]+o(1)$ per output. The second Type-I term is subtracted. For each prime power $\ell^j\le V$ with $\ell>w$ and $\ell\nmid 2n$, its primitive form is
$$
 \frac{\log\ell}{\varphi(\ell^j)}
 \left[E_{n\ell}(h)-\ell^{-1} E_{n\ell}(h_\ell)\right],
 \quad h_\ell(t)=h(t+\log\ell/L).
$$
The second expression with $1/\ell$ is a negligible harmonic tail. In the first, $\mathfrak S_2(n\ell)=\mathfrak S_2(n)(1+O(1/w))$, and the total $\sum \log\ell/\varphi(\ell^j)=vL+o(L)$ uniformly since the omitted prime range $\ell\le w$ has weight $O(\log w)=o(L)$ and excluded output primes are few. Thus this second main is $-v h'(0)\mathfrak S_2(n)+o(1)$. Subtract it from the first to obtain the coefficient displayed. Pointwise $o(1)$ can be summed against $|f_x|$ here because the absolute physical profile is bounded and supported on $x^\zeta$-rough outputs with fixed $\zeta>0$, whence $\sum |f_x|\ll_f x/L$ by an upper sieve. The fixed-rank output singular factor is $\mathfrak S_2+o(1)$. Uniform presieve folding has modulus at most $x^{A+v+o(1)}$, and the same proper-prime-power and internal-squareful estimates apply. This completes the source comparison.

For a smooth upper-end truncation equal to $e^{-u/c}$ near zero the original sharp source is consequently
$$
 \mathcal U_{\mathrm{sharp}}(f)
 =\mathcal U_{h,v}(f)+\frac{1-v}{c}\mathfrak S_2\sum_n f_x(n)+o(x/L).
$$
The term need not be positive for a signed $f$, so it must be paid with its actual sign. For $f_+$ it is an adverse debit. For an exact untruncated exponential the Euler moment can be evaluated directly at $s=1/(cL)$; dispatching the high Vaughan moduli in the corresponding source is an additional problem. None of this gives a positive reserve. A useful stress test is any derivative-flat prefix, for which $h'(0)=0$ restores the old calibration.

## A finite lower bound on the cost of universal positive prefixes

Set $B=1-v$. Suppose that every tuple of positive quotient exponents $t_i$ of total less than $B$ satisfies
$$
 M(t_1,\ldots,t_r)=\sum_{S\subseteq[r]}(-1)^{|S|}
     h\!\left(\sum_{i\in S}t_i\right)\ge0.
$$
The claim is about an individual-coefficient sign required throughout the continuous quotient chamber. Distinct prime labels may approach equal exponents, so continuity permits testing repeated exponents. The conclusion does not impose any additional restriction on the physical joint output weights.

Write $y=A/4$, $a_1=h(y)$, $a_2=h(2y)$, and $a_3=h(3y)$. The condition $v+A<1/2$ implies $2A<B$. Each of the multisets $y^8$, $(y,y,2y,2y,2y)$ and $(2y)^4$ therefore fits the quotient budget. Expanding $M$ on these three multisets and using $h(t)=0$ for $t\ge A$ gives, respectively,
$$
  1-8a_1+28a_2-56a_3\ge0,\qquad
  1-2a_1-2a_2+6a_3\ge0,\qquad 1-4a_2\ge0 .
$$
Their nonnegative combination with multipliers $3/20$, $7/5$ and $7/20$ gives $19/10-4a_1\ge0$. With $w_1(t)=1-h(t)$, the two-label inequality states $w_1(s+t)\le w_1(s)+w_1(t)$. Thus $w_1(y)\le m w_1(y/m)$ for every integer $m\ge1$, and differentiability at zero gives $w_1(y)\le-yh'(0)$. Consequently
$$
   -h'(0)\ge \frac{21}{10A},\qquad
   -(1-v)h'(0)>\frac{21}{5}.
$$
The second expression is the excess comparator coefficient of the preceding section. The proof uses universal signs only. It leaves open signed cancellation across actual physical rows and estimates proved specifically on the support of $f_x$.
