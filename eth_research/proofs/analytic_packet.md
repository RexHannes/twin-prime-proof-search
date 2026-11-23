# Comparator and ordinary five-prime counts on the signed endpoint

Commit `43facedcf40b2f998aa47f7198d6b9b5feb5b792`, branch `real1b-gold467-analytic`. The statements below are paper proofs of existing analytic inputs. The displayed Lean identifiers identify the physical consumer. They do not record a new kernel build or a terminal reserve. The run identifier is `ETH-ANALYTIC-1`.

## 1. Shifted prime comparator

Write \(I=(x/2,x]\), \(L=\log x\), \(y=\exp(L^{1/20})\), \(D_y=\prod_{p\le y}(1-1/p)\), and \(V_y=\prod_{2<p\le y}(1-1/(p-1))\). For every fixed \(A>0\),

\[
\sum_{p\in I}1_{P^-(p-2)>y}=V_y\{\operatorname{li}(x)-\operatorname{li}(x/2)\}+O_A(xL^{-A}).
\]

For large \(x\), both \(p\) and \(p-2\) are odd. For any odd squarefree \(d\) supported on primes up to \(y\), the relevant class is exactly the reduced class \(2\bmod d\). Take an even integer \(R=2\lceil C_A\log L\rceil\). The two Bonferroni sums through degrees \(R\) and \(R+1\) bound the original indicator on both sides. Their moduli are at most \(y^{R+1}=x^{o(1)}\). Each modulus occurs at most once in each sum. The max-endpoint Bombieri–Vinogradov theorem for \(\pi(t;d,2)\), applied at \(x\) and \(x/2\), costs \(O_B(xL^{-B})\) for any fixed \(B\), since eventually \(y^{R+1}<x^{1/3}\). The same Bonferroni inequalities for independent Bernoulli variables of success probabilities \(1/(p-1)\) place \(V_y\) between the corresponding two principal coefficients. Their difference is bounded by

\[
\frac{H_y^{R+1}}{(R+1)!},\qquad H_y=\sum_{2<p\le y}(p-1)^{-1}=\tfrac1{20}\log L+O(1).
\]

Choose \(C_A\) so the factorial bound is \(O(L^{-A-2})\). This proves the assertion. Mertens gives \(D_y\asymp L^{-1/20}\) and \(V_y/D_y=2\prod_{2<p\le y}(1-(p-1)^{-2})\to\mathfrak S_2\). The dyadic log integral differs from \(x/(2L)\) by \(O(x/L^2)\), so the required pre-division error is \(o(D_y x/L)\). This is `Normalization.ShiftedPrimeEstimate`. By `comparator_count` and `normalized_of_shifted_primes`, it gives \(S_b\sim(\mathfrak S_2/2)x/L\). These steps preserve the shift on the smaller factor and the odd local density. This claim is `ETH-CMP-01`.

## 2. Six unit counts on the original five-prime box

Write \(E_j=\{t\in\mathbb R^4:\mathrm{boxDomain}(t),\ \mathrm{test}(j,t)\}\) for `FMDirect.lean` and `FMProfileSlices.lean`, with the stated open cell endpoints and the strict and weak face choices. At every fixed \(j\in\{0,\ldots,5\}\),

\[
\#\{n\in I:\mathrm{unitWeight}_j(n)=1\}
=\frac{x}{2L}\int_{E_j}\frac{dt_1\,dt_2\,dt_3\,dt_4}{t_1t_2t_3t_4(1-\sum t_i)}+o(x/L).
\tag{1}
\]

The integrand equals `sliceDensity j` with its positive profile height canceled on the selected set. Thus (1) proves the complete unweighted six-count input of `infinite_of_signed_estimates` after multiplication by \(\mathfrak S_2\), and `Profile.mean_of_unit_counts` yields `Profile.MeanDensity`. This claim is `ETH-UNIT-02`.

For the proof, write \(n=p_1p_2p_3p_4q\) with ordered distinct prime factors, \(M=\prod p_i\), and \(s_i=\log p_i/L\). All original cutoffs use \(t_i=\log p_i/\log n\), so \(\|s-t\|_\infty=O(1/L)\) on the whole dyadic window. The admissibility inequalities give \(t_i\ge0.04\), and \(1-\sum t_i\ge0.21\) and \(1-\sum t_i\ge t_4\) on box closures. Distinctness and ordering of the four coordinates follow in open boxes from the distinct cell indices. Add the planes \(t_i=t_j\), \(t_4=1-\sum t_i\) to the finite union of box and test boundary hyperplanes. Restrict the discussion of collars to a fixed compact neighborhood of the box closures on which all five exponents exceed a fixed positive constant. On the complement of any fixed positive-width collar, for sufficiently large \(x\) the coordinates \(s\) determine every test and the ordering for every possible \(q\in (x/(2M),x/M]\). If \(s\) lies in the selected region away from the collar, distinctness of the last prime and its strict order follow from the positive separation from \(s_4=1-\sum s_i\). Each accepted integer then has exactly one labeling.

For fixed \((p_i)\) in the enlarged compact region, PNT gives, uniformly,

\[
\pi(x/M)-\pi(x/(2M))=\frac{x}{2ML(1-\sum s_i)}+o\!\left(\frac{x}{ML}\right).
\]

Uniformity follows since \(x/M=x^{1-\sum s_i}\) ranges from \(x^c\) to \(x\) for fixed \(c>0\). The measures \(\sum_{x^a<p\le x^b}\delta_{\log p/L}/p\) converge weakly to \(1_{[a,b]}(s)ds/s\) on every fixed \(0<a<b\), by Mertens or partial summation. Their fourth product therefore converges on the compact region, and its total mass is bounded. Repetitions and permutations can be retained in the auxiliary upper bound on a boundary collar. Its limiting density is bounded, and its mass vanishes as the collar width tends to zero. Applying the product measure limit to upper and lower inner and outer sets proves (1), including points lying exactly on weak or strict faces. The exact dyadic factor is \(1/2\). There is no \(1/5!\) since the labeled coordinates already have the native canonical order.

## 3. Comparator on the full native signed output

The same proof architecture yields the sharper source-exact claim

\[
\sum_{n\in I}\mathrm{compare}(x,n)\Phi_x(n)=\mathfrak S_2\sum_{n\in I}\Phi_x(n)+O_A(xL^{-A})
\tag{2}
\]

for each fixed \(A>0\), and the analogous formula with \(\psi\) or \(\Phi-\psi\). In particular this independently supplies `Ledger.Estimates.comparator` via the first result. The general comparison formula already occurs in the original dossier. The proof here uses ordinary prime BV on one uniquely selected largest output prime and does not require a distribution theorem for products of primes. This claim is `ETH-CMP-PROFILE-03`.

The native definitions and `GoodSupport.active_rank`, `GoodSupport.active_rough` imply that wherever \(\Phi_x\ne0\), the output is squarefree, its rank is at most 255 and every prime factor exceeds \(z=x^{1/400000000000}\). The good part has active rank at most five and all its active factors are at least \(n^\nu\). These facts hold also after boxing and after subtraction. Hence the output sieve at \(y\) is automatically one. Separate each active output uniquely as \(n=Mq\) with \(q\) its largest prime. Sum only squarefree prefixes \(M\) with prime factors above \(z\), and impose \(q>P^+(M)\) and the output rank limit explicitly. Each nonempty prefix has \(X_M=x/M\ge(x/2)^{1/255}\). We may impose that same lower cutoff on \(X_M\) from the start.

For fixed prefix, the weight \(w_M(q)=\Phi_x(Mq)\), extended from primes using the fixed prime list of \(M\) and variable last coordinate, is supported in \((X_M/2,X_M]\) and has uniformly bounded total variation and amplitude. To see this explicitly, write \(u=\log q\). At the fixed rank, every log coordinate or subset sum has the form \((b+e u)/(\log M+u)\) with \(e=0\) or \(1\) for a subset. All cutoff comparisons give affine inequalities on \(u\) after fixing the relevant finite choices. The witnesses in `rankTest` have total at most five, so finitely many cases suffice. For `tinyCost`, resolve each maximum into its two branches before summing. In \(K\), the divisors and their ordered distinguished prime triples correspond to subsets and labels on the fixed factor list. The general-integer cofactor stays a full subset product. The bank tests are affine, and each remaining smooth factor \(1-(\log d/\log n)^2\) is bounded and monotone between faces because \(\log d/\log n\) is a nonnegative linear-fractional function with derivative of constant sign. The mark cutoff, presieves, rank choices and the finite box tests supply only boundedly many further endpoints. Truncation and taking positive or negative part preserve bounded variation. All constants may depend on the fixed rank ceiling and cutoffs, uniformly in \(M,x\).

For odd \(d\mid\prod_{2<p\le y}p\), the prefix is coprime to \(d\) and the residue for \(q\) is \(2M^{-1}\bmod d\). Integration by parts transfers max-endpoint prime BV at \(X_M\) to the weight. With \(Q=y^{R+1}=x^{o(1)}\) as above, \(Q<X_M^{1/3}\) uniformly. Thus the sum over \(d\le Q\) *from this odd squarefree family* of absolute differences between the weighted progression sum and \(\varphi(d)^{-1}\int w_M(t)dt/\log t\) is \(O_B(X_M L^{-B})\). The progressions contain the exact reduced residues, even when \(M\) varies. Ordinary PNT with the same partial summation permits replacement of the integral by the unconditioned prime sum, at the cost \(O_B(X_M L^{-B}\prod_{2<p\le y}(1+1/(p-1)))\), absorbed by increasing \(B\). Apply the Bonferroni argument to positive and negative parts separately. The factorial tail per prefix is \(O_B(X_M L^{-B})\). This gives

\[
\sum_{q\ {\rm prime}}w_M(q)1_{P^-(Mq-2)>y}=V_y\sum_{q\ {\rm prime}}w_M(q)+O_B(X_M L^{-B}).
\]

The sum of \(X_M\) over all relevant integer prefixes is bounded by \(x(1+L)\). After division by \(D_y\), replace \(V_y/D_y\) by \(\mathfrak S_2\) with error \(O(1/y)\), using the tail of the absolutely convergent singular series. The weights are uniformly bounded and there are at most \(x\) physical outputs. Increasing \(B\) proves (2).

## Scope and next proof target

These arguments supply the comparator normalization, the ordinary five-prime mean and the comparator field of the six-field lower ledger at paper level. They leave the genuine shifted-prime weighted five-box/rough-source upper, the remaining lower-ledger fields, the centered Vaughan and short-product estimates in the Lean endpoint, and the strict signed outside source to be certified or proved as applicable. The central outside term still involves macroscopic products \(m\ell>x^{0.49}\). For (2), moduli divide a product of at most \(O(\log\log x)\) primes below \(y\), and are at most \(x^{o(1)}\). Applying the largest-factor BV proof directly to those macroscopic moduli would require an additional distribution or signed cancellation argument. The established gain on the unconditional terminal reserve is zero. No G5 implication is promoted by this packet.

### Sources and reproducibility

The source definitions are `FMSource.lean`, `FMDirect.lean`, `FMClosing.lean`, `FMProfileSlices.lean`, `FMNormalization.lean`, `FMGoodSupport.lean`, `FMUniform.lean` and `FMLowerLedger.lean` at the stated commit. The precise max-residue, max-endpoint BV normalization is Theorem 18.9 of Koukoulopoulos, *The Distribution of Prime Numbers*. PNT and Mertens are used only in their classical unconditional forms. [Author's textbook](https://dms.umontreal.ca/~koukoulo/documents/publications/primes.pdf)

`check_analytic.py` verifies finite Bonferroni bounds and the odd local factor including the factor at 2. It also exhausts all 1,566 admissible native bins and their order and exponent inequalities. The finite check is separate from the asymptotic proofs.
