# Uniform transfer from sharp cutoffs to an averaged outside sum

This paper calculation uses REAL 1B source commit 43facedcf40b2f998aa47f7198d6b9b5feb5b792. The fixed-cutoff Type I and short-product arguments have antecedents in Gold 4.58. Here the moving cutoffs are independent, the outer prime threshold stays fixed, and the error is uniform before averaging.

Write \(I=(x/2,x]\), \(L=\log x\), \(w=\exp(L^a)\), \(0<a<1\) fixed, and \(k=n-2\). Let \(f_x\) be any of \(\Phi,\psi,\Phi-\psi\), exactly as defined in FMDirect. Put \(R_w(k)=1_{P^-(k)>w}\), \(R_w(1)=1\), \(V=x^{.24}\), \(U=x^u\) and \(D=x^d\), with \((u,d)\in [.23,.245]\times[.485,.495]\). Define
\[
 B_{u,d}(k)=\sum_{\ell\mid k,\ \ell\ {\rm prime},\ \ell>V}\log\ell
       \sum_{m\mid k/\ell,\ m>U,\ m\ell>D}\mu(m).
\]
The original coefficient uses \((.24,.49)\).

**Theorem.** Uniformly in this rectangle, for every fixed \(A>0\),
\[
 \sum_{k+2\in I}R_w(k)\mu^2(k) f_x(k+2)B_{u,d}(k)
 = \sum_{k+2\in I}\vartheta(k) f_x(k+2)
       -\mathfrak S_2\sum_{n\in I} f_x(n) + O_{A,a,f}(xL^{-A}).
 \tag{1}
\]
Here \(\vartheta(k)=1_{k\ {\rm prime}}\log k\), and \(\mathfrak S_2=2\prod_{p>2}(1-(p-1)^{-2})\). Integrating over the rectangle against any probability measure changes the original complete sum by \(O_{A,a,f}(xL^{-A})\). All three choices of \(f\) keep their physical signs.

## Fixed-shift progression estimate

For odd \(q\) write \(\Delta_g(q;t)\) for the sum of \(g_x(n)\) on \(x/2<n\le t,\ n\equiv2\bmod q\), less \(1/\varphi(q)\) times the sum on the same prefix with \((n,q)=1\). For fixed \(\xi>0,A>0\),
\[
 \sup_{x/2\le t\le x}\sum_{q\le x^{1/2-\xi},\ q\ {\rm odd}}|\Delta_g(q;t)|\ll_{A,\xi,g} x L^{-A},\qquad g=f,|f|,f_+,f_- .
 \tag{2}
\]
The \(x\) in the profile is held fixed throughout the prefix operation. The active outputs are squarefree of rank at most 255 and every prime factor exceeds \(x^b,\ b=1/400000000000\). This follows from the off-good selectors and from the good-support lemmas on the other branch. On the ordered prime coordinates \(v_i=\log p_i/L\) the profiles are bounded and piecewise uniformly Lipschitz throughout the dyadic shell. Their discontinuities lie on finitely many affine planes at each fixed rank. Enumerate the divisors and marked prime triples, retaining the complete subset product for the general fourth factor in a mark. Clear \(\sum_i v_i\) in profile-ratio inequalities and resolve the finite good-rank assignments and their maxima. The sieve and mark constraints add coordinate planes whose intercepts may depend on \(x\). On each piece the smooth factor in \(K\) is \(1-(\sum_{i\in S}v_i/\sum_i v_i)^2\). All genuine normals are fixed. Identically constant comparisons can be resolved exactly. Taking the positive part, negative part or absolute value preserves the Lipschitz control on a piece.

Partition prime coordinates into boxes of width \(h=L^{-M}\). Cells meeting genuine boundaries lie in collars of width \(O(h)\). Fix all primes except one whose coefficient in the plane is nonzero. Its allowed interval has multiplicative width \(\exp(O(hL))\). In the collar restrict all primes to \(\ge x^{b/2}\). With \(m\) the product of the other coordinates, the number of candidate integers in the free position is \(O(hLx/m+1)\), and \(m\le x^{1-b/2}\). Divisor counting over the other coordinates gives a total
\[
 N_{\rm collar}\ll_r hxL^{r+1}+x^{1-b/2} L^r .
\]
This includes planes parallel to the product boundary, and support faces \(v_i=b\). In the progression sum the total absolute error is controlled by the error against \(\tau(n-2)\). On the collar apply Cauchy–Schwarz with \(\sum_{k\le x}\tau(k)^2\ll xL^3\); in the interior the coefficient error is \(O(h)\). The corresponding primitive-main error is at most \(O(L)\) times its unweighted absolute sum. Choose \(M\) large enough for the desired accuracy.

On each remaining rectangle count squarefree products of distinct primes in prescribed intervals, with repetitions of the same interval allowed. The canonical order assigns the rectangle to each integer uniquely. Liu–Park–Song, Theorem 3.2, counts the set of such integers, with primitive principal sum. Use their parameter \(u_{\rm paper}=1\) and base equal to the upper prefix \(t\) or to \(x/2\); rewrite the prime intervals in that base. Their implied constant is uniform in the interval endpoints, and the fixed gap \(\xi/2\) works at either base. Ordinary prime BV covers rank one. Half-integer endpoints in counting variables give the same intended integer intervals (including open faces). A convention at the final product endpoint changes one integer, with aggregate cost \(O(\tau(n-2)+\log x)\). The \(O_r(L^{Mr})\) rectangles cost a fixed power of \(L\), covered by requesting higher precision. This proves (2) and permits a common weight \(\log(n-2)\) by partial summation. We use a supremum of sums over moduli, with the *same* endpoint for every modulus.

## Both Vaughan subtractions and the short product

For \(k>V\), the exact convolution is
\[
 \Lambda(k)=I_{U,V}(k)+\sum_{mh=k,\ m>U}\mu(m)\sum_{\ell\mid h,\ \ell>V}\Lambda(\ell),\qquad
 I_{U,V}=(\mu_{\le U}*\log)-(\mu_{\le U}*\Lambda_{\le V}*1).
\]
Extract the short terms with \(\ell\) prime, \(m>U,\ell>V,m\ell\le D\) on all inputs before squarefree restriction. The discrepancy from the retained short plus long terms on squareful inputs is bounded by \(2\tau(k)\log k\), since all prime-power divisor logarithms add to \(\log k\). On rough inputs the number having a square factor exceeds zero only for a repeated prime \(>w\); the count is \(O(x/w)\). Cauchy–Schwarz and uniform boundedness of \(f\) pay \(O_A(xL^{-A})\). Replacing the original \(\Lambda\) by \(\vartheta\) costs \(O(\sqrt xL^2)\). Genuine primes in this window exceed \(w\).

In Type I, the modulus \(e\) is \(m\le U\) or \(mj\le UV\). In the latter case the grouped coefficient is bounded by \(\sum_{j\mid e}\Lambda(j)=\log e\). In the former, split \(\log((n-2)/m)=\log(n-2)-\log m\). In the short term \(e=m\ell\le D\), with absolute grouped coefficient at most \(\log e\). Split \(R_w(k)=R_w(e)R_w(k/e)\). The input is odd wherever \(f\ne0\). For the second factor expand the odd primes up to \(w\) by Bonferroni through degree \(R=\lceil C\log L\rceil\). The absolute error at \(k/e\) is bounded by the number of squarefree divisors \(q\) with \(R+1\) such prime factors. The representation \(eq\) is unique since \(e\) is rough and \(q\) smooth. This covers the positive remainder as well. Uniformly \(eq\le x^{.495}w^{R+1}\le x^{.4975}\) eventually. Apply (2) to \(f\) and the absolute remainder to \(|f|\). Every active \(n\) is coprime to \(q\) since \(w<x^b\) eventually. The primitive main still imposes \((n,e)=1\).

Let \(g_w=\prod_{2<p\le w}(1-1/(p-1))\). The truncation error in its finite Euler product is bounded by \(H^{R+1}/(R+1)!\), where \(H=\sum_{2<p\le w}1/(p-1)=O(\log L)\). Choosing \(C\) large absorbs arbitrary log powers, including the grouped coefficients and \(\sum_{e\le D}1/\varphi(e)\ll L\). The main coefficient is consequently \(g_w/\varphi(e)\) with the primitive exclusions.

For \(h=n\) or \(n\ell\) with \(\ell>w\), set
\[
 A_h(T)=\sum_{\substack{m\le T\\(m,2h)=1}}\frac{\mu(m)R_w(m)}{\varphi(m)},\qquad
 B_h(T)=\sum_{\substack{m\le T\\(m,2h)=1}}\frac{\mu(m)R_w(m)\log m}{\varphi(m)} .
\]
Uniformly for \(T\in[x^c,x^{C'}]\), with \(0<c<C'\) fixed,
\[
 A_h(T)=O_B(L^{-B}),\qquad B_h(T)=-\mathfrak S_2/g_w+O_B(L^{-B}). \tag{3}
\]
First omit the sieve and \(h\). The odd Euler product of \(\mu(m)/\varphi(m)\) factors as \(G(s)/\zeta(1+s)\) with
\[
 G(s)=(1-2^{-1-s})^{-1}\prod_{p>2}\frac{1-p^{-s}/(p-1)}{1-p^{-1-s}} .
\]
Its coefficients for \(G\) have an absolutely summable fixed positive power moment by geometric expansion of each ratio. \(G(0)=\mathfrak S_2\). The classical zero-free-region PNT for Möbius, partial summation and the simple pole of \(\zeta\) give \(\sum_{m\le t}\mu(m)/m=O_B((\log t)^{-B})\) and \(\sum_{m\le t}\mu(m)\log(m)/m=-1+O_B((\log t)^{-B})\). Convolution with the coefficients of \(G\), split at \(\sqrt t\), gives the corresponding two odd sums. To exclude primes up to \(w\), convolve with the nonnegative coefficients \(v(j)\) of \(\prod_{2<p\le w}(1-p^{-s}/(p-1))^{-1}\). Their sum is \(1/g_w\ll\log w\), and \(\sum v(j)j^{1/\log w}\ll\log w\) since \(\sum_{p\le w}(p^{1/\log w}-1)/p=O(1)\). Thus \(j>\sqrt T\) contributes at most \(O(\log w\exp(-\log T/(2\log w)))\) times a fixed log power. Apply the odd estimates on the rest, including the extra \(\log j\) in the second. Finally deleting multiples of each \(p\mid h\) costs \(O(L^2/(p-1))\) by squarefreeness and the harmonic totient bound. There are at most 256 such primes, all \(>w\). This proves (3).

If \(\ell>w,\ \ell\nmid 2n\) is prime, splitting at \(\ell\mid m\) gives the exact identity
\[
 \sum_{\substack{m\le T\\(m,2n)=1}}\frac{\mu(m)R_w(m)}{\varphi(m\ell^j)}
 =\frac{1}{\varphi(\ell^j)}
   \left[A_{n\ell}(T)-\ell^{-1}A_{n\ell}(T/\ell)\right],\qquad j\ge1. \tag{4}
\]
The first Type I principal is \(g_w\sum_n f_x(n)(A_n(U)\log(n-2)-B_n(U))=\mathfrak S_2\sum_n f_x(n)+O_A(xL^{-A})\).
In the second, sum (4) over \(\ell^j\le V\) with weight \(\log\ell\). The first argument is \(U\). Use (3) on the second for \(\ell\le\sqrt U\); otherwise use \(O(L)\) and \(\sum_{\ell>\sqrt U,j\ge1}\log\ell/(\ell\varphi(\ell^j))\ll L/\sqrt U\). Hence the second principal is \(O_A(xL^{-A})\). For the short block use (4) with \(j=1\), taking the difference at \(T=D/\ell\) and \(U\) for \(V<\ell\le D/U\). Both main arguments are at least \(U\). The \(1/\ell\) correction costs \(O(L^2/V)\) per output. Empty ranges contribute zero. These estimates prove (1) uniformly and give the four original native Type I and short-product inputs at paper level.

## Consequence for the owner sum

Under independent smooth probability densities in \(u,d\), the inner divisor factor becomes \(h_\ell(\log m/L)\), the product of two smooth cumulative functions evaluated at \(\log m/L\) and \(\log m/L+\log\ell/L\). A common smooth compact cutoff equal to one on the physical range gives Fourier transforms decaying faster than every power uniformly in \(\ell\). For squarefree \(r=k/\ell\) the divisor Fourier factor is \(\prod_{p\mid r}(1-\exp(it\log p/L))\). When \(r=1\) the actual row vanishes since \(h_\ell(0)=0\). The resulting identity transfers the whole native sum and does not assert sharp-to-smooth transfer on individual rank strata. Its main term still contains the genuine shifted-prime weight. Complete terminal credit for this transfer alone is zero.

**Sources.** Theorem 3.2 of Liu, Park and Song supplies the product progression estimate with primitive main. Standard BV and PNT are used in their unconditional forms. [Liu–Park–Song](https://link.springer.com/article/10.1007/s40993-017-0089-3) · [Koukoulopoulos](https://dms.umontreal.ca/~koukoulo/documents/publications/primes.pdf)
