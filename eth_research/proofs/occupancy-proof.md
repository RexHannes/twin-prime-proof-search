# REAL 1B. Squarefreeness, sign and one subpower prime band

**Status.** Analytic corollary of the cited inputs, including the November 19 v2 preprint of Lü, Wang and Wu for the signed part. The squarefreeness and unsigned occupancy statements use classical theorems only. No Lean formalization, positive terminal reserve or literature-priority claim. The computation in `verify_occupancy.py` checks only the finite reallocation identity.

## The joint law

Fix \(1/10<a<1/5\), put \(L=\log x\), and let \(J(p)\) count distinct divisors of \(p+2\) amongst the primes \(e^{L^a}<r\le e^{2L^a}\). Give each genuine prime \(x<p\le2x\) weight \(\log p/x\). Set
\[
 A_2=\prod_{q>2,\ q\text{ prime}}(1-1/[q(q-1)]),\qquad
 \lambda=\log 2,\qquad \pi_j=e^{-\lambda}\lambda^j/j!.
\]
The joint measures of \(J\) and \(\mu(p+2)\) converge in total variation on \(\mathbb N_0\times\{-1,0,1\}\) to the product of the Poisson law \((\pi_j)\) and the probability distribution with masses \(A_2/2,1-A_2,A_2/2\) at \(-1,0,1\), respectively. In particular, for **every fixed** \(j\), the weighted mass of either sign is \(x(A_2\pi_j/2+o(1))\) before dividing by \(x\). Total variation also allows bounded occupancy selectors depending arbitrarily on \(x\), with **absolute** \(o(x)\) error. This gives no relative error for a rare moving cell.

### Unsigned and squarefree parts

First impose \(q^2\nmid p+2\) only for odd primes \(q\le Y\), with \(Y\) fixed. This is a finite union of reduced classes mod \(M=\prod_{2<q\le Y}q^2\); its relative density among reduced classes is \(A_{2,Y}=\prod_{2<q\le Y}(1-1/\varphi(q^2))\). For large \(x\) the moving primes all exceed \(Y\). In any one allowed class \(b\pmod M\), the \(h\)-th binomial moment of \(J\) is obtained by summing over unordered sets of \(h\) distinct moving primes with product \(d\le\exp(2hL^a)\). The two congruences \(p=b\pmod M\) and \(p=-2\pmod d\) have one reduced solution modulo \(Md\). Each \(d\) occurs once, so the Bombieri–Vinogradov remainder with a maximum over residues is \(O_{M,h,B}(xL^{-B})\) for every fixed \(B\). The dyadic main term is
\[
 \frac{x}{\varphi(M)}
 \sum_{r_1<\cdots<r_h}\prod_{i=1}^h(r_i-1)^{-1}
 =\frac{x}{\varphi(M)}\big(\lambda^h/h!+o(1)\big).
\]
Here \(h=0\) uses the prime number theorem in a fixed progression. For \(h>0\) the sum of the individual weights tends to \(\lambda\) and their sum of squares tends to zero. The moments determine the Poisson distribution (its moment generating function exists around zero). The first moment gives tightness. Summing the finitely many allowed classes therefore gives \(A_{2,Y}\pi_j x+o_Y(x)\) for the truncated squarefree event in each cell.

Removing the truncation costs \(O(x/Y)+o(x)\), uniformly in any occupancy selector of modulus at most 1. For \(Y<q\le x^{1/4}\), Brun–Titchmarsh bounds the log-weight in \(p=-2\pmod{q^2}\) by \(O(x/\varphi(q^2))\). For \(x^{1/4}<q\le\sqrt{2x+2}\), counting all integers costs \(O((x^{3/4}+\sqrt{x})\log x)\). Even \(p+2\) does not occur once \(x>2\). Let \(x\to\infty\) and then \(Y\to\infty\). Thus the squarefree occupancy masses converge to \(A_2\pi_j\); the unsigned occupancy masses converge to \(\pi_j\) by the same argument with \(M=1\).

### Signed part and version audit

The Gold 4.68 proposal uses the v1 equation number (5.18). In **v2**, formula (5.18) is a mean-value integral and the required prime-weighted Möbius estimate is **(5.33)**. Its weights are (2.12)–(2.14). Proposition 2.3 (2.16) supplies the mean-square auxiliary-weight removal. All references here are to [arXiv:2610.20242v2](https://arxiv.org/html/2610.20242v2). This uses a preprint result, without claiming a new verification of its internal Type II theorem.

Here are the details of the one-band deduction. Fix \(0<\rho<1\) and choose the admissible number \(K\) in the proof of (5.33) for one fixed positive logarithmic precision. Keep the distinguished band and take \(b\) disjoint families of \(K-1\) other bands, all exponents fixed first. Let \(D(j)=j\rho^{j-1}/V\) for \(j>0\), \(D(0)=0\), and \(V=\sum_r1/r\to\lambda\). For each family let \(H_i\) be its product weight normalized by its positive mean. Applying (5.33) to each \(D H_i\) gives \(x^{-1}\sum_p\log p\,\mu(p+2)D(J)H_i=o(1)\). Proposition 2.3 applies with \(K-1\) to the helper sets. Their normalized arithmetic means computed with their own moduli equal the means computed after adjoining the distinguished prime moduli, by CRT. Because \(D\) is bounded, Cauchy–Schwarz bounds the cost of replacing \(b^{-1}\sum H_i\) by 1 by \(O_{K,\rho}(b^{-1/2})+o_b(1)\) on this scale. Send \(x\to\infty\), then \(b\to\infty\); if \(K=1\) no removal is necessary.

Write \(s_{x,j}=x^{-1}\sum_{J(p)=j}\log p\,\mu(p+2)\). The preceding result gives \(\sum_{j\ge1} j\rho^{j-1}s_{x,j}=o_\rho(1)\) for every fixed \(0<\rho<1\). From any sequence \(x\to\infty\), extract a coordinatewise convergent subsequence; the total variations are uniformly bounded and the unsigned first moments give uniform tail tightness. For its limit \(s_j\), the derivative of the absolutely convergent power series \(S(z)=\sum_j s_jz^j\) is zero on \((0,1)\) by exponential decay of \(j\rho^{j-1}\). Hence \(s_j=0\) for \(j\ge1\). Global HLC \(v2 Theorem 1\) and tail tightness also give \(s_0=0\). Every subsequential limit is identical, so \(s_{x,j}\to0\) coordinatewise and \(\sum_j|s_{x,j}|\to0\) by the same tightness. For either sign, the unsigned squarefree mass and the signed mass add/subtract and divide by two. The third sign is their squarefree complement. Coordinatewise convergence plus unsigned tightness proves the claimed total-variation convergence.

## Attempt to lift this to genuine twins

The prime-containing cell has \(\mu(p+2)=-1,J=0\). Its total unnormalized weight is \(A_2x/4+o(x)\). The upper-bound sieve for twin primes gives \(\sum_{p,p+2\ {\rm prime}}\log p=O(x/\log x)\); e.g. use the two roots \(0,-2\pmod q\) for odd \(q\) on integers in the dyadic interval, followed by multiplication by \(O(\log x)\). Thus **odd squarefree composites** in this same cell have \(A_2x/4+o(x)\) weight. This improves the Gold 4.68 lower-only calculation in this particular cell and gives its exact leading constant. In each cell \(j\ge1\) every output is composite for large \(x\), and each Möbius sign has mass \(A_2\pi_j x/2+o(x)\).

For any fixed integer \(R\ge2\), the donors in the zero cell may additionally be required to have \(\omega(p+2)>R\) with the same leading density. To prove it, count divisibility of \(p+2\) by the fixed, odd primes \(q\le Z\). Reduced residue classes give independent Bernoulli indicators of means \(1/(q-1)\) in the fixed-\(Z\) limit by CRT and the prime number theorem in progressions. Their mean tends to infinity and their variance is at most their mean. Chebyshev, with \(x\to\infty\) before \(Z\to\infty\), implies \(\sum_{\omega(p+2)\le R}\log p=o_R(x)\). On squarefree outputs \(\omega=\Omega\). This is a macroscopic statement and does not bound fixed ranks at precision \(o(x/\log x)\).

Let \(T\) be the present dyadic log-weight of all actual twin inputs and \(D\) the weight of these odd-composite donors of rank \(>R\). For large \(x\), \(D\asymp x\). Define weights on the **same set of genuine input primes** by putting zero on each twin, multiplying donor weights by \(1+T/D=1+O(1/\log x)\), and keeping \(\log p\) elsewhere. For every function \(F_x(J,\mu)\), the loss and gain are exactly \(-T F_x(0,-1)\) and \(+T F_x(0,-1)\). Every separate auxiliary observation supported on \(2\le\Omega(p+2)\le R\) is also preserved, exactly. The new weights are an explicit comparison for this information class. They change the native prime weight and make no assertion about all native FM, Type I/II, roughness, genuine-rank-one or growing-rank tests. They show why even exact sign/occupancy data at every cell cannot pay the prime-containing cell from this aggregate information.

**Unpaid estimate.** On any scale the equation is \(T=M_{-,0}-D_{-,0}\), with \(D_{-,0}\) all odd-composite donors without a rank cutoff. The exact common \(A_2x/4\) main terms cancel. An independently controlled lower bound for their difference on scale \(x/\log x\), with the required native masks and a fixed favorable margin, remains unproved. The full FM ledger acquires zero confirmed credit.

## Supporting sources

- Lü, Wang and Wu, *On the Hardy–Littlewood–Chowla conjecture*, v2, Proposition 2.3, equation (5.33), Theorem 1, Proposition 6.1. [Paper](https://arxiv.org/html/2610.20242v2)
- Montgomery and Vaughan, *Multiplicative Number Theory II. Primes and Sieves*, Chapters 20–21, for Bombieri–Vinogradov and dimension-one/two sieve tools. [Authors' text](https://personal.science.psu.edu/rcv4/Vol2/Vol2.pdf)
- Gold 4.68 one-band proof packet and registry (November 23). Local inputs were read in `work/registry/material/`. The extra precision comes from the CRT squarefree/occupancy calculation and the exact reweighting argument.
