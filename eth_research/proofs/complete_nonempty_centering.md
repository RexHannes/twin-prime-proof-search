# The entire nonempty small-factor sector has a computable net charge

Let $W(f)$ denote the original sharp complete signed FM outside sum. Use $Y=x^t$, $z=x^\epsilon$, $I=(x/2,x]$, $k=n-2$, $L=\log x$, $\theta(k)=1_{\mathbb P}(k)\log k$ and $S^\circ=\mathfrak S_2x/(2L)\sim S_b$. Fix $J\ge1$. Apply the two different exact recursions of *Concentrating the complete signed upper* to $f=f_+-f_-$. Write $P_\pm=\Pi(f_\pm)$, $S=\{p\mid k:p\le Y\}$, and $T_{>J,z}$ for the entire signed physical sum of the two corrected channels on $|S|>J$. The active genuine output has $P_->1.64$ from its balanced triple chamber.

First choose a fixed $h=1/2-\eta$, $0<\eta<1/6$, put $H=x^h$, and choose $t$ so small that $t(J+1)<\eta/4$. The complete low-modulus gauges still hold because $HY^{J+1}<x^{1/2-3\eta/4}$. Then
$$
 \lim_{t\downarrow0}\limsup_{\epsilon\downarrow0}\limsup_{x\to\infty}
 \left|\frac{T_{>J,z}}{S_b}
   -\left(P_--P_++\frac{e^{-\gamma}}t
       [P_++(\log(h/t)-1)P_-]\right)\right|=0.
\tag{1}
$$
In particular the entire net high-small-factor sector diverges with leading coefficient $e^{-\gamma}P_-\log(1/t)/t$. The compensating favorable mass can be placed on the exact zero-small sector. The genuine prime-input correlation remains there.

## Removing the prime flag before splitting

In the notation of the recursion put $D^*_{v,J}=b_{v,J}-\theta(k)$. This is the polynomial divisor expression including every correcting subset. Its complete primitive against $f_\pm$ is $-\mathfrak S_2\sum_I f_\pm+o(S_b)$ under the subpower $R_w$. With $R_z$ the normalized discrepancy tends to zero after $\epsilon\downarrow0$ at fixed $J,h,t$, by the fundamental lemma and Dickman prefixes in the recursion paper. Every input with $S\ne\varnothing$ is composite for sufficiently large $x$. The expressions $D^*_{v,J}$ there equal the actual $b_{v,J}$ and vanish identically for $1\le|S|\le J$. On $S=\varnothing$ they equal $-\log k$ for $v=0$ and $(m-1)\log k$ for $v=1$, where $m$ counts the factors in $(Y,H]$. It follows that, in normalized units up to a discrepancy vanishing in the $x$ then $\epsilon$ limits,
$$
 T_{>J,z}=-\mathfrak S_2\sum_I f+
   \sum_{k+2\in I} R_Y(k)\log k\,[f_+(k+2)+(m-1)f_-(k+2)].
\tag{2}
$$
Here $R_Y$ implies $R_z$, and the originally retained squarefree condition may be removed in (2) since even a single square factor costs $O(x^{1-t}L^C)$ at fixed $t$. This exact cancellation is independent of the detailed inverse coefficients and uses all their complementary terms. Reapplying the prime flag only after (2) would change the equation.

## Paying the ordinary and one-marker sums

Take $g=f_+$ or $f_-$, with $\sum_I g\sim\Pi(g)x/(2L)$ when its mass is positive, and the corresponding additive $o(x/L)$ statement in general. In the no-marker sum use the two dimension-one fundamental-lemma weights at level $x^{\eta/2}$ to impose $R_Y(k)$. In the one-marker sum fix $Y<p\le H$, require $p\mid k$, and sieve the cofactor by the same weights. The mark and every sieve divisor are coprime, the total modulus is $\le x^{1/2-\eta/2}$, and its sole prime larger than $Y$ is the optional mark. The finite-profile progression theorem at the native fixed shift gives arbitrary log savings and accommodates $\log k$ by endpoint partial summation. The active outputs have all prime factors $>x^\zeta$; take $t<\zeta$ so none is in the small-prime sieve. Excluding an output prime equal to the marker costs $O(x^{-\zeta}L^C)$ per output. The sieve means are consequently the common factor $V_Y=\prod_{2<p\le Y}(1-1/(p-1))$ with relative upper/lower error $O(E(\eta/(2t)))$, and additionally $\sum_{Y<p\le H}1/(p-1)=\log(h/t)+o_t(1)$ when marked. Here $E(s)\ll s^{-s/2}$ at large $s$. The squarefreeness and dyadic $\log k=L+O(1)$ cost $o_t(S_b)$ by the same positive population estimate. Since $LV_Y\sim\mathfrak S_2 e^{-\gamma}/t$, the total normalized bracket error is bounded in limsup by
$$
 O_f\!\left(\frac{1+\log(h/t)}t E(\eta/(2t))\right) .
$$
It tends to zero at fixed $\eta$ as $t\downarrow0$, proving (1).

The ordinary integer model with the same conditions has local density $1/p$ including 2 and $L\prod_{p\le Y}(1-1/p)\sim e^{-\gamma}/t$. Its complete polynomial divisor principal is $-1$ per integer. The ordinary tagged sum has the same marker harmonic and the same fundamental-lemma bracket. Thus inserting $f_\pm-\mathfrak S_2 P_\pm/L$ pays the *entire* $|S|>J$ sector at the terminal scale in the ordered limits of (1). The model is included on all inputs, as in *A payment at the terminal scale on the actual four-band adverse population*. A sum of absolute centered terms is not estimated.

## The original shrinking headroom

For $h_t=1/2-(J+2)t$, at fixed $J$ the same complete algebra (2) holds. In particular $m(t,h_t)\ge m(t,h)$ for any fixed $h<1/2$ and sufficiently small $t$. The full term is nonnegative for each additional marker, so (1) also gives a diverging lower for the original $T_{>J,z}$. A sharper remainder follows by splitting the high markers into strips.

For markers below $x^{.25}$ use auxiliary level $x^{.24}$, so the full absolute normalized error is $O_f(E(.24/t)(1+\log(1/t))/t)$. For $p\ge x^{.25}$ form the strips
$$
 j t\le 1/2-\log p/L<(j+1)t,\qquad j\ge J+2.
$$
A partially truncated strip at exponent $.25$ is allowed. For each strip use auxiliary level $x^{(j-1)t}$, giving the same fixed gap $t$ below level one half for that $t$. Its prime harmonic is at most $4t+o_t(1)$ since its coordinates are at least $.25$, and its one-marker contribution has an absolute normalized bracket error $O_f(E(j-1))$. For each fixed $t$ there are finitely many strips, so all $o_{J,t}(1)$ errors vanish before changing $t$. For sufficiently large $J$ the right side of (1) with $h=h_t$ has absolute terminal-scale limsup error at most $C_f\sum_{j\ge J+2}E(j-1)$, which goes to zero with $J$. For the finitely many small $j$ below the asymptotic fundamental-lemma range one may use any fixed finite linear-sieve upper and zero as lower; such a strip has $O(1)$ normalized mass. Thus for every fixed $J\ge1$ the leading asymptotic $e^{-\gamma}P_-\log(1/t)/t$ also holds with original $h_t$.

This upgrades the physical positive-subcohort lower in *A genuine adverse cohort past every fixed exact small-factor elimination* to a calculation of the **net** high-small-factor contribution. The original $W(f)$ also contains the zero-small terms of the two channels, whose sum is exactly the prime correlation $\sum\theta(k)f(k+2)$ minus the large two sieve sums in (2), up to the squareful error. Cancelling these leaves the same full prime-sensitive term as in the starting source. No inequality paying that last term has been supplied by the finite-sector reductions.
