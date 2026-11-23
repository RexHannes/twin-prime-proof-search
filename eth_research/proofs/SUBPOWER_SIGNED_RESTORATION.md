# A subpower version and the signed mass one recovers when omitted sectors are restored

Fix $0<a<b<1$, $0<\eta<.1$, and let
$$
 w=e^{L^a},\quad V=e^{L^b},\quad U=e^{\tau L^b},\quad T=e^{2L^b},
 \quad H=x^{1/2-\eta},\quad D=V.
$$
Keep the fixed smooth law of $\tau$ on $(1,2)$ and the definitions of $B,B',F,f_\pm$ from the small-input compensation packet. In particular $\mathcal W$ denotes the sum of $f_+B-f_-B'$ against $R_w\mu^2$; prime-input coefficients are evaluated in the original owner formula and are zero.

## 1. Bounds at these cutoffs

The folded Type-I and low-label moduli after inserting at most $R=O(\log L)$ presieve primes are at most $HTw^R=x^{1/2-\eta+o(1)}$. Thus the same *fixed* progression level $1/2-\eta/2$ suffices. All coefficient growth is polynomial in $L$: $W\ll L^{1-b}$ and a folded modulus has $O(L^{1-b})$ possible prime labels above $V$. The uniform presieved Möbius prime-number-theorem estimate holds already at $t\ge\exp(L^b/2)$ by the same Euler correction proof, with Rankin tail at most a fixed power of $L$ times $\exp(-c_1L^{b-a})$. The unpresieved PNT log savings at $t^{1/2}$ are arbitrary powers of $L$ since $\log t\gg L^b$. There is no product-subtraction block. Therefore
$$
 \mathcal U_{\mathscr B^c}=\mathcal W+o_{a,b,\eta,f}(x/L)
 =A(f)-\mathfrak S_2\sum_n f_x(n)+o_{a,b,\eta,f}(x/L).
$$
This is a fresh parameter derivation. The asymptotic in the first packet with *fixed* polynomial parameters would not by itself give the same conclusion.

The pointwise signs from the small-input compensation packet now show that every adverse summand, apart from the $O_{f,\zeta}((\eta+1/L)x/L)$ near-half semiprime class, has at least two distinct prime factors in $(e^{L^a},e^{2L^b}]$. The product of all its factors in that range must exceed $V$. For these cutoffs two small factors cannot form the whole input, since $T^2=o(x)$. The small-factor/Radon-rank approximation with constants depending on fixed $c$ is not invoked.

## 2. Exact restoration on zero small factors

Put
$$
 g_T=\prod_{2<p\le T}(1-1/(p-1)),\qquad
 P_T=\sum_{T<p\le H}\frac1{p-1},\qquad
 J(k)=\#\{T<p\le H:p\mid k\}.
$$
Write $\mathcal W_i$ for the above corrected source on inputs with exactly $i$ primes in $(w,T]$, and $\mathcal W_{\ge i}$ for the corresponding tail. On squarefree $R_T(k)=1$ all the prefixes on composite rows equal 1. Including the prime boundary, for every such $k$ in the physical window,
$$
 B(k)=-(1-1_{k\ {\rm prime}})\log k,\qquad
 B'(k)=[J(k)-1+1_{k\ {\rm prime}}]\log k.
$$
A prime in the window has $J(k)=0$. Therefore
$$
 \mathcal W_0=A(f)-
 \sum_{n\in I_x} R_T(k)\mu^2(k)(\log k)
        [f_x(n)+J(k)f_{-,x}(n)].
$$
This identity keeps the true prime-input mass, including its sign on the negative output wall.

The two required remaining prime-free populations are elementary consequences of (PC):
$$
 \sum_n R_T(k)\mu^2(k)g(n)=g_T\sum_n g(n)+O_A(xL^{-A}),
$$
$$
 \sum_n R_T(k)\mu^2(k)J(k)g(n)
  =g_T P_T\sum_n g(n)+O_A(xL^{-A})
$$
for $g=f,f_-$ and their positive envelopes (the implied constants depend on $a,b,\eta,f,A$). To see this, use Bonferroni for odd primes through $T$ at truncation $C_A\log L$. Every output prime exceeds $T$ for large $x$. In the first principal all small coprime factors are thus present. In the second, mark one $p\in(T,H]$, so $q=p e$ has a unique split into its one large-prime factor and a $T$-smooth factor. Its level is $\le HT^{O(\log L)}<x^{1/2-\eta/2}$. Exclusions $p\mid n$ cost at most $O_f(x^{-\zeta})$ per output by its bounded rank. The elementary symmetric principal tail from small primes is bounded by a factorial tail with mean $O(\log L)$; the extra prime sum costs $O(\log L)$. Taking the Bonferroni truncation constant and the discrepancy accuracy large enough pays any fixed log power. For squareful $R_T$-rough inputs the population is $O(x/T)$; the test $J(k)$ is at most $O(L)$, so removing them is harmless. The same facts with the absolute profiles show that replacing $\log k$ by $L$ here costs $O_f(xg_T(1+P_T)/L)=o(x/L)$, because $\sum_n |f_x(n)|\ll_f x/L$.

Subtracting from the complete sum yields
$$
 \boxed{\begin{aligned}
 \mathcal W_0&=A(f)-L g_T\bigg[\sum_n f_x(n)+P_T\sum_n f_{-,x}(n)\bigg]+o(S_b),\\
 \mathcal W_{\ge1}
 &=L g_T\bigg[\sum_n f_x(n)+P_T\sum_n f_{-,x}(n)\bigg]
                   -\mathfrak S_2\sum_n f_x(n)+o(S_b).
 \end{aligned}}
$$
The calibrated complete signed mass on *all* inputs with at least one small prime is therefore explicit. Recovering its favorable zero-small counterpart restores the still unknown $A(f)$. This is the arithmetic content of the representation.

## 3. Obstruction to using the small-factor residual alone

The exactly-one sector satisfies $\mathcal W_1\le0$ by the pointwise calculation. Thus $\mathcal W_{\ge2}\ge\mathcal W_{\ge1}$. By Mertens,
$$
 g_T\sim e^{-\gamma}\mathfrak S_2/\log T,\qquad
 P_T=(1-b)\log L+O(1).
$$
If $\Pi(f_-)=\lim (2L/x)\sum_n f_{-,x}(n)>0$, the main term in the preceding box has normalized size
$$
 \frac{\mathcal W_{\ge1}}{S_b}
 \sim \tfrac12 e^{-\gamma}(1-b)\Pi(f_-)\,L^{1-b}\log L .
$$
Only the leading asymptotic is asserted here. The exact $g_T,P_T$ formula above gives the stronger absolute $o(S_b)$ error. Positivity of the fixed-profile mean follows without the full historical computation: restrict the three distinct output primes to fixed disjoint logarithmic bands near $(.30,.33,.37)$ whose sum equals one, staying away from all nontrivial cuts. Each factor has coordinate in $(1/4,9/20)$; $H=1-3=-2$, the output is good, and its outside profile equals $-2$. PNT partial summation gives positive mass on such a small open ordered region. No claim about primality of the shift is needed.

Consequently the one-sided shortcut which discards the entire complement of the at-least-two-small-prime source has a divergent positive right-hand side, even though the full physical source is on scale $S_b$. A joint estimate retaining the negative zero-small mass is essential. This is a scoped obstruction to the subpower truncation under the verified signs. It assigns no fixed advantage to the original endpoint. For the *positive* part alone, the omitted zero-small composites also have normalized mass asymptotic to $\tfrac12 e^{-\gamma}\Pi(f_+)L^{1-b}$, provided $\Pi(f_+)>0$, with the prime exception contributing $O_f(S_b)$ by a two-linear-form upper sieve on the prime and its shifted rough output.

The exponents $a,b$ may in particular be chosen inside $(.1,.2)$. Two small input labels in one broad band and a weight on $n=k+2$ do not match an external theorem requiring many prescribed distinct subpower bands or a different prime-output test.
