# The sharp recursive correction has nondecaying signed harmonic coefficients

For the finite-subset corrections (1) of *Concentrating the complete signed upper*, let $a(T)$ be the coefficient of $(vm-1)\log k$ in $c_v(T)$. This defines the coefficient formally before assigning values to the physical logarithms. Let $N(\varnothing)=1$ and $N(T)=a(T)$ for $T\ne\varnothing$. On finite labelled sets with convolution $(P*Q)(T)=\sum_{A\subseteq T}P(A)Q(T\setminus A)$, equation (1) gives $N*M=\delta_\varnothing$. Write $u_i=\log p_i/\log Y$. The sharp coefficient is
$$
 M(T)=\sum_{A\subseteq T}(-1)^{|A|}1_{\sum_{i\in A}u_i\le1}.
$$
We evaluate its harmonic inverse in continuous prime coordinates. This tests the small-label majorant used when discarding all correlations with the actual output and the complementary divisor prefix.

For fixed $U=t/\epsilon>1$, integrate each variable with $du/u$ on $[1/U,1]$. Set
$$
 M_U(z)=\sum_{j\ge0}\frac{z^j}{j!}\int M([j])\prod_{i=1}^j\frac{du_i}{u_i},\qquad
 N_U(z)=\sum_{j\ge0}\frac{z^j}{j!}\int N([j])\prod_{i=1}^j\frac{du_i}{u_i}.
$$
The sets are labelled and distinct in the physical sum. At each fixed $j,U$ the replacement of reciprocal prime weights by these integrals follows from Mertens on the polynomial window, subdivision of its finite linear faces, and the vanishing mass of equal coordinates. The subset convolution becomes multiplication of exponential generating series. Thus $M_U(z)N_U(z)=1$ formally. Expanding $M$ by subsets gives
$$
 M_U(z)=e^{z\log U}\sum_{r=0}^{\lfloor U\rfloor}
  \frac{(-z)^r}{r!}\int_{u_i\ge1/U,\;\sum_i u_i\le1}\prod_{i=1}^r\frac{du_i}{u_i}.
$$
At $z=1$ the finite sum is the Dickman function $\rho(U)$, by its integral expansion in the polynomial-presieve proof. Consequently
$$
 \sum_{j\ge0}\frac1{j!}\int |N([j])|\prod_{i=1}^j\frac{du_i}{u_i}
 \;\ge\;\frac1{U\rho(U)}.
\tag{1}
$$
If the left side is finite, $N_U$ converges absolutely at one and its product with the entire $M_U$ may be evaluated there. If it diverges the inequality already holds. This large norm involves all orders at fixed $U$ and makes no assertion that a specified finite partial sum reaches it.

For each fixed $j$ the stronger signed limit is
$$
 h_j=\lim_{U\to\infty}\frac1{j!}\int N([j])\prod_i\frac{du_i}{u_i}
       =[z^j]\,e^{-\gamma z}\Gamma(1-z),\qquad
 \lim_{j\to\infty}h_j=e^{-\gamma}.
\tag{2}
$$
The normalization by $j!$ already discounts the unordered label multiplicity. Thus an extra inverse factorial cannot justify summing heuristic small-factor rarity.

## Absolute convergence at each fixed rank

For $x_0>0$, let $M_{x_0}$ use the sharp threshold $x_0$ in place of 1, with coordinates now ranging over $(0,1]$. On a compact set of $x_0$s bounded away from zero the full harmonic integral of $|M_{x_0}([j])|$ is finite, uniformly for any fixed $j$. For $j=1$ its integrand is $1_{u>x_0}$. For $j\ge2$, select the smallest coordinate $u$. If the coefficient is nonzero, some subset of the remaining variables has sum in $(x_0-u,x_0]$. For $u<x_0/2$ one member of this subset is at least $x_0/(2j)$. Once all other variables are fixed it occupies an interval of length at most $u$, with harmonic measure $O_{j,x_0}(u)$. Summing the finitely many choices bounds the contribution of $u<\delta$ by $O_{j,x_0}(\int_0^\delta (1+\log(1/u))^{j-2}du)$. This also gives continuity in $x_0$ by truncated dominated convergence. Integrals of $N$ at fixed rank are absolutely finite by the finite convolution recurrence and products of these bounds.

## Transform of the sharp endpoint

Let $M(x_0;z)$ be the exponential series of the resulting degree coefficients for $M_{x_0}$ over $(0,1]$, manipulated coefficient by coefficient. For $0<x_0\le1$ the labels exceeding $x_0$ cannot enter an admissible subset. Dividing all remaining coordinates by $x_0$ gives the formal identity $M(x_0;z)=x_0^{-z}M(1;z)$. Thus at each fixed order the growth toward $x_0=0$ is bounded by a polynomial in $\log(1/x_0)$. For $x_0\ge j$ the degree-$j$ coefficient is zero whenever $j\ge1$.

The Laplace transform in $x_0$ is
$$
 \int_0^\infty e^{-s x_0}M(x_0;z)dx_0
  =s^{-1}\exp\!\left(z\int_0^1\frac{1-e^{-su}}u\,du\right)
  =s^{-1}\exp\big(z(\log s+\gamma+E_1(s))\big).
$$
To justify the first equality, first restrict $u_i\ge d>0$. Integration of each subset indicator is its exponential divided by $s$, giving $\prod(1-e^{-su_i})/s$. As $d\downarrow0$ the fixed-order coefficients converge under the Laplace integral. For $x_0\le1$ the same split at $x_0$ bounds their absolute integrals uniformly in $d$ by a polynomial in $\log(1/x_0)$ times the finite absolute integrals at endpoint 1. If $d>x_0$ they are bounded by the corresponding power of $\log(1/x_0)$. For $x_0\ge1$ use the fixed-compact bound and the vanishing for $x_0\ge j$. The second equality follows by differentiation in $s$ and the usual constant in the exponential integral $E_1(s)=\int_s^\infty e^{-u}du/u$.

Replacing the portion $x_0\ge1$ of $M(x_0;z)$ by $x_0^{-z}M(1;z)$ changes each coefficient of its transform by an exponentially small quantity as $s\to\infty$. The latter transform equals $s^{z-1}\Gamma(1-z)M(1;z)$. Multiplying by $s^{1-z}$ and taking $s\to\infty$ coefficientwise yields $M(1;z)=e^{\gamma z}/\Gamma(1-z)$. Inverting the formal coefficients now proves the first half of (2). For $|z|<1$, its reciprocal is
$$
 e^{-\gamma z}\Gamma(1-z)=\exp\!\left(\sum_{r\ge2}\frac{\zeta(r)}r z^r\right).
$$
The coefficient sequence is nonnegative. Subtracting $e^{-\gamma}/(1-z)$ removes the simple pole at $z=1$ and leaves a function analytic in $|z|<2$. Its coefficients tend to zero, which proves the second half of (2).

As a finite check, suppose every selected prime is larger than $\sqrt Y$. Then all pair products exceed $Y$ and $M([j])=1-j$. Its exponential series is $(1-z)e^z$. Thus on every such set $N([j])=j![z^j]e^{-z}/(1-z)$ is exactly the derangement number $!j$. For $j\ge2$, the remaining part of $c_v(T)$ equals $(j-1)!\sum_{p\in T}\log p$ by symmetry and differentiation of $(1-z)e^z$ at each degree. A raw pointwise coefficient of factorial size is therefore present on actual open prime-coordinate boxes.

These harmonic facts preserve the full original signed physical remainder as an open problem. In particular dropping the residual's complementary $M(S\setminus T)$ or its correlation with $f_\pm(k+2)$ can remove essential signed cancellation. Equations (1) and (2) do not preclude another bound exploiting that information; they apply only to this specific labelled correction with its unconditioned harmonic model.
