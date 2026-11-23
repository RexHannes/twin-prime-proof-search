# Unmarked rough companions and the rank-one gap

The estimates below apply to the actual primes \(x<p\le 2x\). They quantify the part of the perforated polynomial sieve on which every Lü–Wang–Wu auxiliary product vanishes. They also give a lower bound there for companions having at least three distinct prime factors.

Write \(L=\log x\), \(M(F)=\sum_{x<p\le 2x}(\log p)F(p+2)\), \(R_0(n)=1_{P^-(n)>x^\beta}\), and
\[
 V_0=\prod_{2<q\le x^\beta}\left(1-\frac1{q-1}\right)
 \sim \frac{2e^{-\gamma}C_2}{\beta L}.
\]
The products here and below range over primes. Take \(D=x^{.001}\), \(s=.001/\beta\) large and fixed. Let \(R\) be the sieve with the \(H\) fixed exceptional subpower bands in ETH-PERF-01 and \(V\) its local product. Write \(\theta_s=C s^{-s/2}\) with an absolute sieve constant, enlarging \(C\) a fixed number of times if necessary.

## Mass invisible to the marks

The fundamental lemma in Koukoulopoulos, *The Distribution of Prime Numbers*, Theorem 19.1(a)–(c), gives upper and lower divisor polynomials supported on squarefree odd \(d\le D\), with coefficients of absolute value at most one. The local density is \(1/(q-1)\). The inverse dimension-one product condition on all prime intervals holds uniformly for either choice of omitted bands. Ordinary prime Bombieri–Vinogradov on the reduced progression \(-2\bmod d\) gives
\[
 (1-\theta_s+o(1))xV_0\le M(R_0)\le(1+\theta_s+o(1))xV_0.
\]
The same applies to \(R,V\). Each omitted band contributes a factor \(2+o(1)\) to \(V/V_0\) by Mertens' theorem. Consequently,
\[
 \frac{M(R_0)}{M(R)}
     =2^{-H}\big(1+O(\theta_s)+o(1)\big).
\]
All estimates take \(x\) to infinity after fixing \(H,\beta\). With \(s\) fixed the bracket in this display cannot be replaced by an established \(1+o(1)\).

On every input selected by \(R_0\), all exceptional band counts vanish for large \(x\), and hence every marked product \(W_j\) vanishes pointwise. Every linear combination \(G\) of functions \(W_jS_j\), with arbitrary finite divisor-polynomial tests \(S_j\), obeys
\[
 \frac{M(R|G-1|^2)}{M(R)}\ \ge\ \frac{M(R_0)}{M(R)}.
\]
The observation holds for any function of the marked products that vanishes when its arguments are all zero. Thus normalization by the much larger perforated sieve mass can make the missing fraction small, while the absolute error on the unmarked set still has size \(xV_0\).

## Actual high-rank supply on the unmarked set

For the three exponent intervals \((2,4],(5,10],(11,22]\) let \(\mathcal B_j\) consist of the primes whose \(\log q/(\beta L)\) belongs to the respective interval. Set \(t_j(n)=\#\{q\in\mathcal B_j:q\mid n\}\), \(Y=t_1t_2t_3\), and \(m=\log 2\). For \(h=1,2\) write
\[
 F_1=m^3,\qquad F_2=(m+m^2)^3.
\]
Then
\[
 (1-\theta_s)F_h+o(1)
 \le \frac{M(R_0Y^h)}{xV_0}
 \le(1+\theta_s)F_h+o(1).
\]

To prove these inequalities, multiply the two fundamental-lemma divisor polynomials for \(R_0\) by the nonnegative \(Y^h\) and expand. Each \(t_j^2=t_j+2\binom{t_j}{2}\). The squarefree prime product specifying the selected primes in the three bands determines all three unordered subsets. The remaining sieve divisor has primes at most \(x^\beta\), so the folded modulus has one representation with coefficient bounded by eight. All moduli are \(\le x^{.001+72\beta}\), where \(72=2(4+10+22)\). This lies within ordinary prime Bombieri–Vinogradov for our choice \(\beta<.001\). Its absolute error is \(O_A(xL^{-A})\). In the local model the disjoint primes divide independently with probabilities \(v_q=1/(q-1)\). For each band \(\sum v_q=m+o(1)\) and \(\sum v_q^2=o(1)\). The first two raw local moments of \(t_j\) converge to \(m\) and \(m+m^2\). Products across the disjoint bands factor, which proves the displayed estimates.

A squareful \(p+2\) in \(R_0\) has \(q^2\mid p+2\) with \(q>x^\beta\); an integer count bounds its prime log mass by \(O(L(x^{1-\beta}+\sqrt{x}))\). As \(Y^2\) is bounded in terms of fixed \(\beta\) on \(n\le 3x\), deleting this part costs \(o(xV_0)\) in both moments. Cauchy's inequality on the positive squarefree measure now gives
\[
 \liminf_{x\to\infty}
 \frac{M(R_0\mu^2\,1_{Y>0})}{xV_0}
 \ \ge\
 \frac{(1-\theta_s)^2}{1+\theta_s}
 \left(\frac{m}{1+m}\right)^3 .
\]
For sufficiently small \(\beta\) we have \(\theta_s\le 1/10\). Since \(\log 2>2/3\), the right side exceeds
\[
 \frac{(9/10)^2}{11/10}(2/5)^3=\frac{324}{6875}>\frac1{25}.
\]
Every counted companion has at least three distinct polynomial-sized prime factors and has no prime below \(x^\beta\). All these companions lie in the zero set of every \(W_j\).

## Consequences for the attempted lift

The elementary dimension-two upper-bound sieve on \(p(p+2)\) bounds the actual twin log mass by \(C_0 x/L\) with an absolute \(C_0\). In the last inequality \(1/25\) is independent of \(\beta\), while \(xV_0\sim 2e^{-\gamma}C_2 x/(\beta L)\). Decreasing fixed \(\beta\) makes the lower bound for the genuine undifferentiated high-rank population exceed any fixed multiple of this upper bound for twins. The argument gives no allocation between odd and even rank within this population.

For a precise information bound, keep the actual prime log weights, masks, ranks, and every unsigned observation fixed. Consider the two *comparison signs* that agree with arithmetic \(\mu\) elsewhere and take the respective constant values \(+1,-1\) on \(R_0\mu^2\,1_{Y>0}\). Every observed signed quantity of the form \(M(\mu\,W_jS_j)\) has exactly the same value for the two choices. Their unmarked signed composite totals differ by more than \((2/25+o(1))xV_0\). This construction diagnoses the information carried by these particular marked statistics. Only the original Möbius sign is asserted to be arithmetic.

On the actual integers the missing rank-sensitive inequality has a direct expression. With \(T\) the genuine twin log mass on \((x,2x]\) and \(\Omega\) counting prime factors with multiplicity,
\[
 T=M(R_0\,1_{\mu=-1})-M(R_0\,1_{\mu=-1,\ \Omega\ge3}).
\]
The second term includes all squarefree odd-rank composites, while nonsquarefree companions make zero contribution to both terms on the right. All twins survive \(R_0\) for large \(x\). A positive lower bound for this difference on an unbounded sequence would supply the terminal theorem. Neither the marked cancellation estimate nor the positive high-rank estimate gives that lower bound.

### Forcing the missing prime labels by multiplication

One possible way to make a marker nonzero on the blind sector is to multiply \(p+2\) by selected marking primes before evaluating its Möbius and occupancy weights. On the actual no-hole sector this has an exact formula, including for a weighted average over multipliers. For each \(x\), take any finite family \(\mathcal A_x\) of squarefree integers whose prime factors are \(\le x^\beta\) and complex scalars \(c_a\). Write \(\boldsymbol\omega_E\) for the vector of the \(H\) exceptional band occupancies. Let \(F\) be any function of this vector, and let \(Z(n)\) be any bounded arithmetic test on the original companion. Then
\[
 \sum_{a\in\mathcal A_x}c_a\!
 \sum_{x<p\le2x}(\log p)R_0(p+2)Z(p+2)\,
      \mu\big(a(p+2)\big)F\big(\boldsymbol\omega_E(a(p+2))\big)
 =
 \left[\sum_{a\in\mathcal A_x}c_a\mu(a)F(\boldsymbol\omega_E(a))\right]
 M(R_0Z\mu).
\]
Indeed \(R_0(n)\) implies \((a,n)=1\), and all the selected bands lie below \(x^\beta\) for large \(x\). Hence multiplication contributes exactly the external prime labels, leaving the original companion with none. The argument holds also with an \(a\)-dependent \(F_a\). It is an exact identity at each sufficiently large scale, with no growth restriction on the number of multipliers or their coefficients. Zero bracket gives the identity \(0=0\). A nonzero bracket gives precisely the original unmarked signed statistic upon division. Thus forced multiplicative labels create no independent equation on the missing object, even if one forces one label in every group and makes all auxiliary products nonzero.

The reason the published marked correlation cannot estimate this new left side is also visible before averaging. Its shift-two prime source is \(p+2\) with input \(p\). Replacing the argument by \(a(p+2)=ap+2a\) replaces the corresponding input at shift \(2a\) by \(ap\), composite for \(a>1\). In the label-extraction step the forced divisibility \(a\mid a(p+2)\) puts no congruence condition on \(p+2\). The independent labels in LWW (4.5)–(4.8), used in the mean-square estimate, are not supplied by these repetitions.

The comparison-sign changes above also preserve any unmarked bounded signed test known only up to \(o(x/L^\alpha)\) for fixed \(\alpha<1\). Their effect is \(O_\beta(x/L)=o(x/L^\alpha)\). This remains true uniformly over all divisor polynomials \(S(n)=\sum_{d\mid n}l_d\) with \(\lvert l_d\rvert\le1\) in absolute value. On the perturbed squarefree \(n\le3x\) every prime factor is above \(x^\beta\), hence \(\tau(n)\le 2^{2/\beta}\) for large \(x\). The total variation argument is at fixed \(\beta\). It covers the coarse precision of the global HLC estimate but does not claim invariance for unknown unmarked estimates of terminal precision.

**Primary sources.** The upper and lower sieve weights and their dimension bound come from Koukoulopoulos, Theorem 19.1. The auxiliary weights and their pointwise marked factors come from Lü–Wang–Wu (2.6)–(2.14). [Sieve text](https://dms.umontreal.ca/~koukoulo/documents/publications/primes.pdf) and [Lü–Wang–Wu, v2](https://arxiv.org/html/2610.20242v2).
