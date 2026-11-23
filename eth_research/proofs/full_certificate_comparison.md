# Which complete bound changes

At the source commit 43facedcf40b2f998aa47f7198d6b9b5feb5b792, write $f=\Phi-\psi$ and $f_\pm=\max(\pm f,0)$. Write $\Pi$ for the native ordered-prime angular measure; the measure of the whole prime rank is one. The full transfer at $u=.24,d=.49$ in `uniform_native_transfer.md` yields
$$
\frac{\mathcal U_{\mathscr B^c}}{S_b}
 = \frac{A(f_+)-A(f_-)}{S_b}-\Pi(f_+)+\Pi(f_-)+o(1).
$$
The subsequence error cannot be used separately on selected input-owner rows. The squarefree, rough, physical mask and all signed companions here are those in the transfer. I independently checked its AP source theorem, collar cost, common-prefix BV integration, unique rough/smooth factorization, two Euler sums, prime-power extraction and $1/\ell$ cost in the noncoprime Vaughan subtraction. The argument covers all three profiles uniformly at paper level.

Gold 4.64 Part IV R2.2 gives the old independent nonnegative certificate coefficient $(3.4002754-1)\Pi(f_+)+\Pi(f_-)$. The extension in `native_rough_sieve.md` proves that on the same physical source the complete coefficient can be replaced by
$$ C_{\rm new}=\frac73\Pi(f_+)+\Pi(f_-). $$
It charges the negative comparator on the entire native outside support. The inequality that was spent is $-A(f_-)\le0$.

## Two disjoint witnesses for the strict change

Gold 4.62's chamber is $a=t_1\in(.09,.11), b=t_2\in(.12,.15), c=t_3\in(.16,.19), s=t_1+t_3+t_4\in(.502,.508)$. Hence $t_4=s-a-c\in(.202,.258)$ and $t_5=1-s-b\in(.342,.378)$, in canonical order throughout. The first four primes give six pairs below the half-divisor threshold. The pairs $a+t_5$ and $b+t_5$ are also below; they are at most $.488$ and $.498$. The other two pairs $c+t_5$ and $t_4+t_5$ are at least $.502$ and $.55$. All singletons pass, and exactly two complementary triples pass. The native $H=1-5+8-2=2$ away from all epsilon collars. Each of the three labels in $K$ would require a prime below $.028$ in normalized scale; none exists. The smallest coordinate excludes the good set. The original boxes require $t_1+t_3+t_4>.51$, hence $f=2$. The transformation from $(a,b,c,s)$ has Jacobian one. The product denominator never exceeds $.11\cdot.15\cdot.19\cdot.258\cdot.378$, giving $\Pi(f_+)\ge 400/566181$ on this chamber.

The new chamber centered at $(.103,.107,.150,.281,.359)$ in `native_rough_sieve.md` is disjoint from the former by its second coordinate. It contributes a further $10^{-7}$. Therefore
$$ C_{\rm old}-C_{\rm new}
 \ ge\ (3.4002754-10/3)(400/566181+10^{-7})
 =\frac{211425922099669}{4469850000000000000}
 >.00004730045 .
$$
This is a fixed gain on a correctly normalized **complete named outside upper**. Its implication for the best budget needs a further comparison.

## A stronger obstruction to this independent upper

On ordered squarefree triples of primes with $\sum t_i=1$, all $0<t_i<1/2$, discard points where some $t_i$ is within $h=10^{-5}$ of $0$, $1/2$ or $1/5$. For the remaining physical triples $H=1-3=-2$. Indeed every singleton allowed by the native small/large classification gives $-1$, all below $\beta$, and all pairs are above the outer cutoff since the opposite singleton lies below $1/2-h$. The original $K$ vanishes on triples: a marked divisor needs three distinct primes as labels and a disjoint nonunit fourth factor. The input presieve in $K$ therefore makes no difference. The three factors exceed the polynomial output cutoff for large $x$. On good triples $-G=-2$; on off-good triples $F=-2$ by retained rank three. No triple is in a five-prime box. Thus $f_-=2$ on the entire remaining chamber, independently of the good-set partition.

Before carving out these collars its ordered weighted angular mass is
$$
\frac{2}{3!}\int_0^{1/2}\int_{1/2-t}^{1/2}
 \frac{du\,dt}{t u(1-t-u)}
= \frac23\int_0^{1/2}\frac{-\log(1-2t)}{t(1-t)}\,dt
=\frac{\pi^2}{6}.
$$
For the last equality let $v=2t$. The two terms from $dv/v+dv/(2-v)$ integrate to $\pi^2/6$ and $\pi^2/12$, respectively, by the ordinary and alternating Basel sums. By symmetry the union of all discarded collars costs at most twice the one-dimensional integral of $[-\log(1-2t)]/[t(1-t)]$ over the three removed intervals on one coordinate. On $[0,h]$ the integrand is at most 6. On $1/5\pm h$ it is at most 7. On $[1/2-h,1/2]$ use $1/[t(1-t)]<5$ and the integral $h[1-\log(2h)]<12h$. These three errors total less than $(12+28+120)h$. Using just $\pi>3.14$ proves
$$ \Pi(f_-)>3.14^2/6-160h=197/120>1.64. $$
This lower bounds the right side of the nonnegative certificate. It does not lower bound the true outside contribution.

The two-sided historical ledger gives the alternative whole-source bound $\mathcal U+T\le(1.000107183501+o(1))S_b$, subject to the explicit analytic inputs in the pinned `Ledger.upper_of_estimates`. Native box calibration and $T,\mathrm{primeBox}\ge0$ then imply
$$ \limsup \mathcal U_{\mathscr B^c}/S_b\le 1.000107183501+J. $$
With the old integral enclosure this is at most $1.28460707694425252602$. With the new enclosure it is at most $1.27571012985835393770$. Both numbers are below 1.64. Thus a smaller nonnegative certificate on its own does not set a record for the combined complete budget if the two-sided ledger has been established. The improvement to the integral bounds **does** improve this latter complete upper, by $0.00889694708589858832$ with the same ledger. A stronger lower ledger and five-box cap further relax the sufficient outside threshold. Each conclusion inherits the analytic premises used; none is a positive twin-prime reserve.

## Independent route for the tail field

On squarefree rank $r\ge256$ the calibrated kernel satisfies $|H-K|\le(1+r^3/64^3)2^r$ since there are $2^r$ divisors, at most $r^3$ ordered marked prime triples per divisor, and $|1-(\log d/\log n)^2|\le1$. Its output has every prime $>x^{1/(4\cdot10^{11})}$, so $r$ has a fixed ceiling $4\cdot10^{11}$. Write $b=1/(4\cdot10^{11})$. The rank-$r$ angular measure on this support is at most $[\log(1/b)]^{r-1}/(r-1)!$. Multiply the reciprocal product by $\sum t_i=1$ and place each of its $r$ terms under the projection dropping that coordinate. Bound the other $r-1$ one-dimensional integrals by $\int_b^1dt/t$ and divide by $r!$ on the unordered symmetric upper envelope. Since $\log(1/b)<27$, the first term in the resulting majorant is $(1+256^3/64^3)2^{256}27^{255}/255!<2.235\cdot10^{-61}$. Subsequent ratios are at most $(257/256)^3(54/256)<.214$. The full mass is $<2.85\cdot10^{-61}$. The $10/3$ genuine-prime upper and comparator asymptotic apply rank by fixed rank on this finite set, positive and negative parts separately. Hence $\limsup |R_{\rm tail}|/S_b\le(7/3)\Pi(|W_{\rm tail}|)<6.7\cdot10^{-61}<10^{-58}$. This estimate supplies a paper check of the relevant ledger field.

The exact chamber and arithmetic checks are reproduced by `profile_comparison.py`. The angular integral and analytic transfers use the proofs above rather than extrapolation from finite instances.
