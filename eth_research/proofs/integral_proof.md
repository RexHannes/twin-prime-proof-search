# A sharper enclosure of the actual Gold five-prime integral

The input is `Direct.J` at `43facedcf40b2f998aa47f7198d6b9b5feb5b792`. I derive the following bounds for the same 1,566 boxes and both original displaced faces.

$$
0.27547734178065116588 \le J \le 0.27560294635735393770.
$$

They use exact arithmetic. The checker is written in Python. The sharper assertion has no Lean certificate in this packet.

Let $t_5=1-\sum_{i=1}^4 t_i$, $g(t)=1/\prod_{i=1}^5t_i$, and $H$ be the original height. Partition each original box into $4^4$ equal cubes. Their side length is $h=1/400$ and all five coordinates are positive on every closure. Endpoints of the open boxes and individual hyperplanes have measure zero. The thresholds separated by $10^{-9}$ are kept distinct. On one cube use coordinates $t_i=h(a_i+u_i)$, with $a_i$ the integer lower endpoints and $0\le u_i\le1$. Its height equals two plus four indicators, each testing the sum of three distinct $u_i$ against a rational threshold. The coefficient deciding between the one- and two-epsilon faces is constant on every original box.

For $v\in\{0,1\}^4$ let $B_v$ denote the usual multilinear corner basis, a product of $u_i$ when $v_i=1$ and $1-u_i$ when $v_i=0$. Write
$$w_v=\int_{[0,1]^4}H B_v,\quad m=\sum_v w_v,\qquad a'_i=\sum_{v:v_i=1}w_v.$$
These give the exact mass and first moments of $H$. The function $\log g$ is convex, being a sum of negative logarithms of positive affine coordinates. Thus $g$ is convex. Jensen at the $H$-weighted centroid gives one side. Repeated one-coordinate convex interpolation at the corners gives the other:
$$
 h^4 m g(h(a+a'/m))
 \le \int_{\text{cube}}H g
 \le h^4\sum_v w_v g(h(a+v)).
$$

Here is an exact integration rule for every $w_v$. For $0\le k\le 3$, the integral of $u_1\cdots u_k$ on $[0,1]^3\cap\{\sum u_i<y\}$ is
$$
\sum_{a=0}^3(-1)^a\sum_{j=\max(0,a-(3-k))}^{\min(k,a)}
 {k\choose j}{3-k\choose a-j}
 \sum_{r=0}^j {j\choose r}\frac{(y-a)_+^{3+k-j+r}}{(3+k-j+r)!}.
$$
Exclude the events $u_i>1$ from the positive simplex. For each selected coordinate translate by one, expand the $j$ factors that become $1+u_i$, and integrate the resulting monomial on the positive simplex. The upper-face mass is the full moment $2^{-k}$ minus the displayed result. For a three-coordinate corner basis with $b$ positive bits, expand the $3-b$ factors $1-u_i$ using the binomial theorem. Integrating out the fourth coordinate gives an additional factor $1/2$. The base height two contributes $2/16$ to each $w_v$.

At every cube the checker rounds the Jensen lower down to a multiple of $10^{-20}$ and independently rounds each of the 16 upper summands up at that denominator. It sums 400,896 cubes. An independent exact check of every threshold position used in both the two- and four-way subdivisions uses a Laplace transform. The transform of a lower cumulative corner mass of three factors is
$$
 s^{-7}(s-1+e^{-s})^{3-b}(1-(1+s)e^{-s})^b .
$$
Writing the numerator as a sum of $c_{a,j}e^{-as}s^j$ gives the inverse transform explicitly, $\sum c_{a,j}(y-a)_+^{6-j}/(6-j)!$. This second formula matched all 220 tested threshold and corner-bit-count combinations. The two-way subdivision independently yields $[0.27535211011865944471,0.27585415891793411439]$.

## Effect on the direct endpoint

Keeping the inherited analytic comparison with $c_*=3.4002754$, the refined geometric result alone gives a conditional box cap $0.66152297230907626575444258$ and conditional sufficient outside threshold $0.33836980318992373424555742$. Compared with the rounded handoff threshold this enlarges the acceptable coefficient by $0.02135512322592373424555742$. The exact finite proof certifies $J$. A favorable upper for the full outside source, and the needed signed ledger and transfers, are separate. No unconditional twin-prime mass follows from this computation.

For normalization select $T/S_b=t$, the prime-weighted box $\mathrm{primeBox}/S_b=b$ and $\mathcal U_{\mathrm{out}}/S_b=u$. Under both historical ledger directions and native box calibration,
$$
0.999892775499+J-o(1)\ \le\ t+b+u\ \le\ 1.000107183501+J+o(1).
$$
The upper direction needs the additional lower side of the rank-two omitted-sector bound in `Ledger.upper_of_estimates`. In particular the old strict outside target already implies $t+b\ge 0.682878095535+J+\kappa-o(1)$ using the lower ledger; if $b=J+o(1)$ it forces a macroscopic twin density $t\ge 0.682878095535+\kappa-o(1)$. This illustrates the strength of that architecture. Assuming the upper ledger and box calibration, $t,b\ge0$ also imply $u\le1.000107183501+J+o(1)\le1.27571012985835393770+o(1)$. This latter is a complete-source but conditional upper, far above the closing threshold.

## Independent assessment of the comparator and ordinary counts

I checked the three statements in `analytic_packet.md` against the source definitions on the exact commit and Koukoulopoulos, *The Distribution of Prime Numbers*, Theorem 18.9. The theorem has both max over endpoints and max over reduced residues inside the modulus sum. The Bonferroni degrees remain $O_A(\log\log x)$ and moduli are $x^{o(1)}$, including when a unique largest factor is selected with exponent at least $1/255+o(1)$. The native $K$ definition includes the unrestricted quotient. For fixed squarefree prefix and fixed rank, all its selectors are finite unions of affine intervals in the log of the variable largest prime and its smooth weight has bounded total variation. The physical $H,G$ and good-set cutoff allow only bounded-rank polynomially rough active outputs. The sum of the separate prime-BV error scales over possible prefixes is bounded by $x(1+\log x)$. Finally, represent the last of the five ordered primes at a fixed tuple of four by the actual dyadic window for that prime. The moving faces tend to fixed hyperplanes of measure zero, all five exponent coordinates stay positive, and ordered labeling introduces no factorial. I accept the three statements at the level of written proofs using classical theorems. This makes no claim of a new Lean verification or numerical twin reserve. [Koukoulopoulos, Theorem 18.9](https://dms.umontreal.ca/~koukoulo/documents/publications/primes.pdf)
