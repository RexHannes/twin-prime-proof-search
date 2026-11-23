# A quantitative adverse population in the fixed-power compensated source

Use the root simultaneous_core representation at \(U=V=x^t\), \(H=x^{1/2-2t}\), \(k=n-2\), and its following rank-three correction. The output \(f=\Phi-\psi\) is the original bounded signed outside profile. Write \(s=\prod_{p\mid k,\ p\le U}p\) on squarefree \(k\), and let \(m\) count the primes of \(k\) in \((U,H]\). Use
\[
M_s=\sum_{d\mid s,\ d\le U}\mu(d).
\]
On composite squarefree inputs the raw coefficient is \(B=-\log(k/s)M_s\) and the corrected negative-channel coefficient is \(B^\dagger=[(m-1)\log k+\log s]M_s\). For the positive channel subtract
\[
P(k)=\sum_{\substack{p<q\le U,\ pq>U\\p,q\ {\rm prime},\ pq\mid k}}
\log(k/(pq))\sum_{\substack{d\mid k/(pq)\\ d\le U}}\mu(d).
\]
The signed coefficient of interest is \(f_+(B-P)-f_-B^\dagger\), with squarefreeness on \(k\) and input mask \(P^-(k)>x^e\). The sum over the *entire* physical source of the added double-label probe is negligible with the subpower input mask and has arbitrarily small limiting normalized size after choosing sufficiently small \(e>0\) at fixed \(t\).

Indeed its combined Type I modulus is \(pqd\le x^{3t}\). The two powers of small label choice are at most logarithmic per factor when merging. At fixed \(p,q\) the exact primitive correction has numerator \(\sum_{j\mid pq}\mu(j) A_{npq,w}(U/j)/j\) and denominator \(\varphi(pq)\); the \(j=1\) term is arbitrarily small by the uniform Möbius harmonic lemma, and the \(j>1\) errors have at least one divisor \(>w\). For \(z=x^e\) the uniform limiting \(j=1\) numerator is \(\rho(t/e)+o_e(1)\); shared primes now exceed \(z\). Factoring out the sieve logarithm \(\log k\), the harmonic cost of the named rough primes is \(O((1+\log(t/e))^2)\). The ordinary lower/upper fundamental sieve bracket, as in sharp_polynomial_presieve, gives an additional vanishing \(O_t((1+\log(t/e))^2 e^{-2}E_{t/(2e)})\) after \(x\to\infty\) and \(e\downarrow0\). Here \(e^{-2}\) denotes \(1/e^2\), where \(e\) is the fixed roughness exponent. The convention for the Dickman function yields a total vanishing cost in this order. The source alteration is therefore legal on the complete signed sum.

## The rank-three sectors

If there are no small primes, \(M_s=1\). At rank three at least one prime lies below \(H\), since \(H^3>x\) for all fixed \(t<1/12\). Thus \(B^\dagger=(m-1)\log k\ge0,\ B-P=-\log k<0\). A single small prime gives \(M_s=0=P\). With two smalls \(p<q\), the remaining \(r=k/(pq)\) exceeds \(H\). If \(pq\le U\) then \(M_s=0=P\). Otherwise \(M_s=-1\), \(P=\log r=B\), and \(B^\dagger=\log r>0\). Three small primes are impossible on this window. Hence all rank-three summands of both channels together are nonpositive. Rank-two and prime inputs have no pair tag. The remaining near-half semiprime error is as in simultaneous_core.

## A lower bound for an adverse cohort of rank at least five

For every sufficiently small fixed \(t>0\) and every \(0<e<t/4\), consider the actual squarefree \(k\) in the physical window with exactly two primes \(\le U\), denoted \(p,q\), and the following additional conditions:

\[
U^{1/4}<p\le U^{1/2},\quad U^{3/4}<q\le U,\qquad
\omega_{(U^2,U^4]}(k)\ge1,\quad \omega_{(U^4,U^8]}(k)\ge1.
\tag{1}
\]

All inputs satisfy \(P^-(k)>x^e\), \(s=pq>U\), \(M_s=-1\), \(P=\log(k/(pq))=B\), and \(m\ge2\), since \(U^8<H\). Thus the complete signed summand gives
\[
f_+(B-P)-f_-B^\dagger
=f_-(n)[(m-1)\log k+\log(pq)]\ \ge\ f_-(n)\log k
\tag{2}
\]
pointwise on this population. It has at least five prime factors: even the product of any four required primes taking their displayed maxima is \(\le U^{13.5}<x/2-2\) once \(t\) is sufficiently small.

Let \(\lambda=\log2,\ \lambda_q=\log(4/3)\). If \(\mathcal Q(t,e)\) denotes the sum of the full left side of (2) on (1), then
\[
\liminf_{x\to\infty}\frac{\mathcal Q(t,e)}{S_b}
\ \ge\ \frac{e^{-\gamma_E}}{t}\Pi(f_-)
  \frac{(1-\theta_t)^2}{1+\theta_t}\,
  \lambda\,\lambda_q \left(\frac{\lambda}{1+\lambda}\right)^2
\ >\ \frac{0.021}{t}.
\tag{3}
\]
Here \(\theta_t\to0\) as \(t\downarrow0\) and all parameters are fixed before \(x\to\infty\). The factor \(\Pi(f_-)>1.64\) is the genuine balanced-triple lower bound in full_certificate_comparison. Formula (3) is an adverse contribution in the compensated upper ledger.

To prove it, take the positive measure of ordinary outputs with weight \(f_-(n)\), restricted to these exactly two small primes \(p,q\) but before imposing the last two conditions in (1). Write \(N_1,N_2\) for the two medium band counts and \(Y=N_1N_2\). Let \(V_U=\prod_{2<r\le U}(1-1/(r-1))\). The first and second moments of \(Y\), before applying the prime-input logarithm, satisfy
\[
\begin{aligned}
\sum f_-\,1_{p,q\ \mathrm{as\ above}}Y
&\ge(1-\theta_t+o_t(1))V_U\sum f_-\,\lambda\lambda_q\,\lambda^2,\\
\sum f_-\,1_{p,q\ \mathrm{as\ above}}Y^2
&\le(1+\theta_t+o_t(1))V_U\sum f_-\,\lambda\lambda_q\,(\lambda+\lambda^2)^2 .
\end{aligned}
\tag{4}
\]

For each moment expand the named prime labels, using \(N_i^2=N_i+2\binom{N_i}{2}\). The product \(d\) includes \(p,q\) and up to two primes from each medium band. Require \(d\mid k\) and \(P^-(k/d)>U\), exactly the desired absence of other small primes. This also excludes a second power of a named small prime. Deleting all other squareful inputs costs \(O_t(x^{1-t/4}L^C)\): on the exact population every factor exceeds \(x^{t/4}\), and all label multiplicities at fixed \(t\) are bounded. Insert fixed fundamental-lemma lower/upper divisor weights of level \(x^{1/4}\) on the cofactor, with odd sieve primes \(\le U\), local densities \(1/(r-1)\), \(s_0=1/(4t)\). Their Euler relative error is \(\theta_t=O(s_0^{-s_0/2})\). These same weights may be used for every choice of the marked \(d\).

The modulus \(dc\) in the progression for each cofactor sieve divisor \(c\) is at most \(x^{1/4+25.5t}\), hence below \(x^{.49}\) by a fixed margin for sufficiently small \(t\). It is odd and the residue of the original output is 2. Each folded modulus has at most a fixed power of \(L\) representations (at most six named primes). Thus the native primitive product-distribution theorem applies to the summed signed sieve errors at arbitrary logarithmic precision. Removing the primitive exclusion \((n,dc)>1\) costs \(O(x^{-\delta}L^C)\) per output after summing harmonic weights, since each prime of an active \(n\) exceeds \(x^\delta\) and the input ranks/label counts are bounded. Replacing \(\varphi(dc)\) by \(\varphi(d)\varphi(c)\) costs \(O_t(x^{-t/4}L^C)\) per output: only \(p,q\) can occur in both \(d\) and \(c\), and the absolute reciprocal cost of a shared fixed prime is \(O(L^C/x^{t/4})\). The upper/lower main terms now factor. The band sums \(\sum_{r}1/(r-1)\) tend to \(\lambda,\lambda_q,\lambda,\lambda\) respectively, uniformly integrable on these fixed exponent intervals. Distinctness in the medium-band diagonal costs \(o_t(1)\) as \(\sum 1/(r-1)^2=o_t(1)\). This proves (4).

Positive-measure Cauchy gives the weight of the event \(Y>0\) at least the square of the first moment divided by the second. Multiply by \(\log k=L+O(1)\), and use \(V_U\sim\mathfrak S_2 e^{-\gamma_E}/(tL)\) and \(\sum f_-\sim\Pi(f_-)x/(2L)\). This proves the first inequality in (3). For all sufficiently small \(t\) the fixed sieve constant permits \(\theta_t\le 1/10\). The elementary numerical bounds \(e^{-\gamma_E}>.55,\ \log2>.69,\ \log(4/3)>.287\) yield a coefficient at least
\[
\tfrac{55}{100}\tfrac{164}{100}\tfrac{81}{110}
\tfrac{69}{100}\tfrac{287}{1000}\left(\tfrac{69}{169}\right)^2
=\frac{313110797643}{14280500000000}>.021 .
\]
For example \(\log 2>.693\) and \(\log(4/3)>.287\) follow from three and two positive terms of their atanh series. Also \(\gamma_E\le H_{32}-5\log2<.594<\log(20/11)\), using \(H_{32}<4.059\) and the same two-term lower series for \(\log(20/11)\).

For fixed \(t\), choose \(e\) sufficiently small that the complete signed transfers have normalized error at most one. The complete corrected source then remains \(O_f(S_b)\) with an upper constant independent of sufficiently small \(t\), because the original outside source has a uniform finite upper. Thus the complementary physical population must contain a favorable net of order \(S_b/t\) as \(t\downarrow0\). The rank-three elimination preserves this substantial cancellation requirement. Its nonpositive discarded sectors cannot supply a positive terminal reserve when their compensating charges are omitted.

## A forced adverse cohort beyond every fixed finite elimination

The following applies to the separate optional nonpositive-sector construction in rank_three_and_owners. Fix \(J\ge2\). Write \(K=J+1\), and use its exact coefficient \(f_+B-f_-B^\dagger-|f|\log k\sum_{i=2}^{J}C_iQ_i(k)\), where each \(C_i\ge0\) and
\[
 Q_i(k)=\sum_{\substack{A\subseteq S\\|A|=i}}M(S\setminus A),
 \qquad S=\{p\mid k:p\le U\},\quad
 M(B)=\sum_{\substack{d\mid\prod_{p\in B}p\\d\le U}}\mu(d).
\]
This construction starts afresh from the two-channel base, as in the root proof. It is distinct from the pair-only modification in (2).

Choose the actual squarefree physical population where \(S\) consists of exactly \(K\) primes, all in \((\sqrt U,U]\), and where the same two medium bands \((U^2,U^4],(U^4,U^8]\) are both occupied. For fixed \(J\) take \(t\) small enough that \(U^8<H\), \((K+24)t<.23\), and the prescribed input sieve has \(e<t/2\). On this population all pair products among \(S\) exceed \(U\), hence \(M(B)=1-|B|\). For every \(i\le J\),
\[
Q_i(k)=\binom Ki(1-K+i)\le0 .
\]
The optional compensating terms therefore increase the combined signed coefficient on this physical cohort. In addition \(B=J\log(k/s)>0\) and \(B^\dagger=-J[(m-1)\log k+\log s]\le-J\log k\). Consequently every combined summand is at least \(J f_-(n)\log k\).

The same two positive moments used for (4) apply with \(K\) *unordered* forced small primes. The exact small-set requirement is enforced by the cofactor \(R_U(k/d)\). The sum of the forced small harmonic weights tends to \(\lambda^K/K!\), by Mertens, bounded total harmonic mass and vanishing diagonal mass. Each physical integer in the small set has exactly one such choice. The maximum folded modulus in the second moment is now \(x^{1/4+(K+24)t}\), still below the fixed profile level. There are at most \(K+4\) distinct prime tags and their folding costs a fixed power of \(L\). The repeated-small-prime density collision and squareful errors are power-small at fixed \(J,t\) since every small label exceeds \(x^{t/2}\). Thus the sum \(Q^{(J)}(t,e)\) of the complete signed optional coefficient on this cohort satisfies, for all sufficiently small fixed \(t\),
\[
\liminf_x\frac{Q^{(J)}(t,e)}{S_b}\ge \frac{c_J}{t},\qquad
c_J=J e^{-\gamma_E}\Pi(f_-)\frac{81}{110}
\frac{(\log2)^{J+1}}{(J+1)!}
\left(\frac{\log2}{1+\log2}\right)^2>0 .
\tag{5}
\]
All these inputs have more than \(J\) small factors by construction. For small enough \(t\) their actual prime factor rank is at least \(J+4\): a product of only the \(K\) small labels and the two forced medium primes is at most \(U^{K+12}<x/2-2\). Equation (5) supplies a genuine adverse numerical coefficient for each individual finite construction. Its dependence on \(J\) is explicit, so it gives no nondecay lower as \(J\) grows at fixed \(t\). For each fixed \(J\), taking \(t\) small drives the unnormalized debit in native \(S_b\) units to arbitrarily large values, even after that finite construction has made all sectors with at most \(J\) small factors nonpositive. The full signed source remains bounded on that scale only with compensating favorable sectors retained.
