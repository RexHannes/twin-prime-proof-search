# Two simultaneous bounds for the full signed source

All quantities refer to native commit 43facedcf40b2f998aa47f7198d6b9b5feb5b792 and window \(x/2<n\le x\). All displayed liminf/limsup coefficients use the same positive \(S_b\sim\mathfrak S_2x/(2\log x)\). Use the definitions, rank-four pointwise inequality and signed partition in collar_ledger, equations (1), (2) and (5), the four source transfers and calibrated mean in analytic_contracts, and the small-prime-slot estimate in the referee's native_rough_sieve. The integrals for each nonnegative fixed profile use ordered squarefree prime factors counted once. All ingredients below have written proofs. The native Lean consumer retains its explicit analytic premises.

## A smaller absolute four-factor cost

For any retained rectangular angular cell of fixed rank \(r\ge3\), all prime factors exceed a common fixed positive power of \(x\) and the least satisfies \(p_1\le x^{1/3}\). Pascadi's Proposition 5.2 accepts \(x^{2\tau}\le N\le x^{1/3+\tau}\) for every sufficiently small fixed \(\tau>0\). The whole two-sieve and factorization proof for the five boxes in native_rough_sieve applies to this least prime also. Take \(\tau\) smaller than one fourth of the common lower exponent. The prime short coefficient satisfies Siegel–Walfisz uniformly over the fixed cells, the other \(r-1\) primes give a coefficient bounded by \((r-1)!\), and the count of dyadic cells is a fixed power of \(\log x\). Cells meeting the support and their upper products preserve the exponent slack. Take \(x\to\infty\) first, then the small-sieve and \(\tau\) limits. This gives \(A(P)/S_b\le (10/3)\Pi(P)+o(1)\) for any bounded nonnegative fixed-rank chamber profile \(P\) here. The same conclusion holds at rank two when the smaller prime is in either narrow band about \(x^{1/5}\). For the near-half rank-two band we retain the separate \(32/9\) inequality. Rank-dependent constants cause no limit exchange since the rough tail has a fixed finite rank ceiling. [Pascadi, Propositions 4.4 and 5.2](https://arxiv.org/html/2505.00653v2)

For the rank-four angular error envelope keep the dependence of each convolution on its *own* prime-sum mass. The proof in collar_ledger gives

\[
K_h(v)\le\frac{h}{v}\log^{h-1}(v/\delta)
\]

for \(v\ge\delta\), since the remaining \(h-1\) variables range in \([\delta,v]\). For the exceptional single-coordinate term of pointwise bound (2), \(t\in[\nu,1/5]\) and the other three sum to \(1-t\le1-\nu\). Its logarithmic factor is bounded by \(C_1^2\) with \(C_1=26.492\). For the half-sum term, \(\beta<t<1/2\) and both groups' summed masses are at most \(1-\beta\), giving the smaller \(C_2^2\) with \(C_2=26.022\). The exact rational sums \(\sum_{j=0}^{130}C_i^j/j!\) exceed \((1-\nu)/\delta\) and \((1-\beta)/\delta\), respectively. Hence

\[
E_4'=\frac{2\epsilon C_1^2}{\nu(1-\nu)}
+\frac{4\epsilon C_2^2}{\beta(1-\beta)}
=0.00001960713760979619438614\ldots
\]

upper-bounds \(\Pi(|W_4|)\), including both signs. For any signed \(W\) with \(A(W^\pm)/S_b\le c\Pi(W^\pm)+o(1)\) and \(B(W^\pm)/S_b=\Pi(W^\pm)+o(1)\), the two-sided centered bound is \(|A(W)-B(W)|/S_b\le(c-1)\Pi(|W|)+o(1)\) whenever \(c\ge2\). Applying it to \(W_4\) gives \(D_4=(7/3)E_4'<0.000045749987756191120235\). At ranks \(r\ge256\) use the same signed bound and the earlier envelope \(2^{r+1}27^{r-1}/(r-1)!\). The absolute tail cost is

\[
D_t=\frac73\,\frac{4\cdot54^{255}}{255!(1-54/256)}
<2.034\cdot10^{-62}.
\]

## Every entry in the signed partition

Put \(a_0=1/5-\epsilon\), \(A_0=2\epsilon/[\beta(1-\beta)]\) and

\[
B_0=\frac{\epsilon}{a_0(1-a_0)}
+\frac{\epsilon^2}{2a_0^2(3/5)}
+\frac{3(5\epsilon)^4}{5!\,4!\,a_0^5},\qquad
I_0=\epsilon/[\nu(1-\nu)] .
\]

Here \(A_0\) bounds the positive good-sector mass from near-half rank two. \(B_0\) bounds the positive good-sector masses from the other rank-two band, rank three, and rank five, respectively. The rank-five term uses all prime orders and the full native upper height three. Good rank four and all higher positive ranks vanish. The omitted (off-good) rank-two source is nonnegative and has ordinary mass at most \(I_0\). Put \(D_m=9\delta^{-2}/(50\,99!)<3.086\cdot10^{-134}\). This is the combined signed calibration debit for the original \(H-K_X\), with the general \(q\) bank, no truncation in rank, and the squarefree filter.

The exact native identity after the \(o(S_b)\) prime-power, ordinary mean and Vaughan payments is

\[
\frac{\mathcal U+T}{S_b}
=1+\frac{B(P)-A(P)-R_2-R_4-R_{\rm tail}
+\operatorname{deviation}(\mathrm{calibrated})}{S_b}+o(1).
\]

The good contribution lies between \(-[(23/9)A_0+(7/3)B_0]\) and \(A_0+B_0\), up to \(o(1)\). The sign multiplying the omitted pair is minus, so its interval is \([-(7/3)I_0, I_0]\). The three other contributions are bounded in absolute value by \(D_4,D_t,D_m\), respectively. It follows that the **complete simultaneous window** is \(L_0-o(1)\le(\mathcal U+T)/S_b\le U_0+o(1)\), where

\[
\begin{aligned}
L_0&=1-\tfrac{23}9 A_0-\tfrac73(B_0+I_0)-D_4-D_t-D_m
 =0.99995420040113248509504115422\ldots,\\
U_0&=1+A_0+B_0+I_0+D_4+D_t+D_m
 =1.00004577048775628226606863364\ldots .
\end{aligned}
\]

The lower and upper use different sides of the same positive-source comparison. The rational check_complete_ledger program carries every term, including the minute rank-five, high-tail and calibrated debits.

## The boxed and outside source on the same window

Let \(b=\mathrm{primeBox}(x)/S_b\), \(t=T(x)/S_b\), \(v=\mathcal U_{\mathscr B^c}(x)/S_b\). The ordinary integral \(J\) for the 1,566 native boxes has the rigorous enclosure \(j_-=.27547734178065116588\le J\le j_+=.27560294635735393770\) in the referee's J4 certificate. The six rough profile upper bounds and positivity give \(0\le b\le (10/3)J+o(1)\). Native Vaughan calibration gives \(\mathcal U_{\mathscr B}/S_b=b-J+o(1)\), hence its complete range is \([-J,(7/3)J]\) up to \(o(1)\). The complete outside source therefore satisfies

\[
\begin{aligned}
L_0-\tfrac73j_+-o(1)&\le v+t\le U_0+j_++o(1),\\
L_0+j_- -o(1)&\le v+t+b\le U_0+j_++o(1).
\end{aligned}
\]

Numerically the first interval is \([0.35688065890063996379504\ldots,\,1.27564871684511021996607\ldots]\). Its upper end bounds \(v\) unconditionally by \(t\ge0\). The second interval starts at \(1.27543154218178365097504\ldots\). The sufficient closing condition is a strict improvement on \(\limsup v<L_0-(7/3)j_+\), still unproved. The actual proven upper and the sufficient closing threshold differ by more than \(0.9187\). The exact matched interval with \(b,t\) retained does not prescribe how much each nonnegative genuine-prime population contributes.

The Gold 4.66 full proof, §6 (6.1), uses \(J\le.28449989344325252602\) on the same full boxes. Its archived polynomial profile calculation at smaller cost elsewhere is for a further short-pair restriction. The pinned upper ledger \(1.000107183501\), when all its analytic inputs are supplied, gave the earlier same-source upper \(1.28460707694425252602\) by the identical nonnegativity deduction. The arithmetic above directly proves a smaller complete upper from the audited papers. Any claim that a numeric bound supersedes the entire historical research programme additionally requires checking independent archives and any alternative complete certificates.
