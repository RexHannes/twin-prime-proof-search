# Gate 1B / Real R11 — independent endpoint audit and Gram repair

Date: 19 October 2026.
Status: REPAIR -> scoped paper-level PASS. No terminal R11, HSTAR, primitive rough Type-II or rough endpoint covariance theorem is proved.

## 1. Controlling evidence and four verdicts

This note audits the supplied `Gate1B_HLC_Endpoint_Firewall_20261019/01_REPORT.md`, not an earlier character or near-determinant checkpoint. The original is preserved separately, not overwritten.

| Claim | Verdict | Exact scope |
|---|---|---|
| HLC literal-slope exclusion | PASS | Direct identification with the fixed-K prime-list slopes only; common main scales related by fixed powers. |
| Diagonal-moment population cost | PASS with quantifier clarification | exp((nu/c+o(1))*sqrt(L)) when 2R/sqrt(L)->c; only exp(Theta(sqrt(L))) follows from comparability alone. |
| Endpoint scalar roughening | PASS under explicit support/budget hypotheses | A common auxiliary cutoff whose odd primes are all included in the pinned comparison primorial, and fixed-depth divisor/profile bounds. |
| Endpoint Gram roughening | REPAIR | The incoming proof used the complementary coefficient Gamma where the detector row S was required. Section 4 repairs the proof, preserving and strengthening its closing margin. |
| Prime-slot no-long-Mobius distinction | PASS, scoped | Source-local, same-argument operations built only from the long-long coefficient cannot recover the prime slot. This is not a no-go for nonlocal recombination. |

An occurrence image definition is not an executable occurrence-to-provider proof. The source-factory bounds below are explicit hypotheses inherited from the printed factory. This audit does not certify every earlier analytic bank or enumerate every live occurrence.

## 2. HLC audit against the primary preprint

Lue-Wang-Wu, arXiv:2610.20242v1, Proposition 4.2 and Sections 2.3/4, use fixed K prime lists with exponents between 1/10 and 1/5. Their auxiliary slopes are bounded by exp(2K L^(1/5)). Gate's retained primitive slopes satisfy

    a=m/gcd(m,j), b=j/gcd(m,j) >= c X^delta L^(-J_d).

For fixed delta>0, K and J_d, logarithms give

    delta log X - J_d log L - O(1) > 2K L^(1/5)

for all sufficiently large X. The literal families therefore do not intersect. The claim remains valid when the HLC main parameter is a fixed power of X. An uncharged exponential change of scale is not allowed.

This excludes direct theorem substitution only. Adding auxiliary weights or proving a polynomial-slope theorem remains a different mathematical task.

The inspected preprint takes R=ceil(sqrt(L)/2). It uses the factor (d_0 Y)^(1/(2R)) in (4.67)-(4.68), with log(d_0 Y)=O_K(L^0.21). Replacing the local population by X^nu gives exp((nu+o(1))*sqrt(L)) for that exact R. A merely comparable R gives an unspecified positive constant in the exponent.

Its Proposition 2.3 has error C_(K,rho)/b+o(1), with b,K fixed before x tends to infinity. That statement alone does not allow b=L^A or uniform arbitrary-log unweighting. We do not import the preprint's headline theorem as a Gate provider or independently certify its full proof.

## 3. Exact endpoint scope, scalar proof, and common cutoff

Work with the unnormalised endpoint row

    W_theta = sum_(m,c) A_theta(m) Gamma_theta(c) W_theta(m,c) Delta_X(mc),
    Delta_X(mc)=Lambda(mc+2)-B_X(mc).

The raw Gram omits Gamma:

    S_theta(c)=sum_m A_theta(m) W_theta(m,c) Delta_X(mc),
    G_theta=sum_c |S_theta(c)|^2.

Assumptions, uniform in the occurrences being asserted:

* m,c are positive odd integers; m is in [M,2M], X^delta<=M<=X^(1/6).
* The physical support has mc+2 in a fixed proportional interval [c_-X,c_+X].
* |A_theta(m)|<=d_k(m), |Gamma_theta(c)|<=d_l(c), with k+l bounded by a fixed factory depth.
* |W_theta(m,c)|<=L^b, with a fixed exponent; all allowed modulus-one twists preserve these envelopes.
* The same pinned comparison is B_X(mc)=2/V_o(z) times the indicator that mc+2 is coprime to its odd primorial, and its amplitude is at most L^b0.
* The occurrence measure and other licensed outside factors have their stated fixed-polylogarithmic total-variation costs.

The true cutoff condition is set inclusion: every odd prime <=Z must divide the comparison primorial. The bare inequality Z<=z is not sufficient to resolve a '<z' versus '<=z' convention. A safe common choice, for z>=4 and the usual primorial convention, is

    Z=min(exp(L^gamma), z/2), 0<gamma<1.

Only the auxiliary cutoff changes. The comparison is not redefined. If a specific HLC cutoff is desired, its inclusion must be checked separately. For a family with occurrence-dependent cutoffs use a proved common lower cutoff, not an assumed one.

Put N=mc+2 and R(N)=1_(P^-(N)>Z). On odd physical support,

    (1-R(N)) Delta_X(mc)=(1-R(N)) Lambda(N).

The right side is supported on N=p^e~X, p<=Z, e>=2 for large X. A fixed proportional interval contains O(1) powers of each p, so there are O(Z) possible N.

For each N, exact convolution of divisor bounds gives

    sum_(mc=N-2) |A_theta(m) Gamma_theta(c)| <= d_(k+l)(N-2).

For every fixed epsilon>0, this is O_epsilon(X^epsilon), uniformly in fixed depth. Thus the unnormalised endpoint scalar error is

    |W_theta-W_theta^rough| <= C_epsilon Z X^epsilon L^C.       (S)

Because Z=X^o(1), it is O_A(X L^(-A-C_src)) for any fixed requested precision. This is a uniform deduction from the stated factory envelopes, not a proof of the unknown rough row.

## 4. Repair of the actual Gram cross term

The incoming report's Section 5 used the energy of Gamma to estimate the Gram cross term. This is the wrong vector: Gamma belongs to the outer scalar pairing, not the raw row Gram.

Let

    S_R(c)=sum_m A_theta(m) W_theta(m,c) R(mc+2) Delta_X(mc),
    E(c)=sum_m A_theta(m) W_theta(m,c) (1-R(mc+2)) Lambda(mc+2).

Then S=S_R+E, and exactly

    G_theta-G_theta^rough = 2 Re sum_c S_R(c) conjugate(E(c)) + sum_c |E(c)|^2.  (G1)

Define e_1=sum_c |E(c)|. The same sparse-power count, now without Gamma, gives

    e_1 <= C_epsilon Z X^epsilon L^C,

since sum_(m|N-2) d_k(m)=d_(k+1)(N-2).

Independently of any endpoint cancellation,

    ||S_R||_infinity
      <= L^b (log(c_+X)+sup |B_X|) sum_(m~M) |A_theta(m)|
      <= M L^C.

The last inequality follows from the first divisor moment; alternatively the declared A energy and Cauchy give it. The comparison amplitude assumption follows from its usual finite Euler product whenever log z is bounded by a fixed power of L, or can be kept as an explicit audited input.

Consequently

    |G_theta-G_theta^rough| <= 2 ||S_R||_infinity e_1+e_1^2
      <= C_epsilon [M Z X^epsilon L^C + Z^2 X^(2epsilon) L^C].       (G2)

Equivalently the difference is M X^o(1). In particular, since M<=X^(1/6), it is O_A(X L^(-A)) for every fixed A. This preserves the incoming claimed negligibility, without assuming G_theta or the rough endpoint small and without substituting Gamma for S_R.

The exact complex conjugate in (G1) matters. The verifier checks it with unit-modulus Gaussian-rational row coefficients and formal log(prime) variables.

For the normalised Gram, divide this raw difference by L^2 exactly once. For any additional positive source weight bounded by (X/M)L^C, its integrated perturbation is X^(1+o(1)), hence o(X^2/L^2). Larger or unverified source weights are not automatically covered.

A simple algebraic diagnostic explains the original problem: for one coordinate take S_R=t, E=1 and Gamma=0. The Gram difference is 2t+1, while Gamma has zero energy. This is not an actual-occurrence counterexample; it refutes the proposed algebraic substitution.

## 5. Research continuation: source-weighted high moments do not become free from roughness

The following sharp statement tests a source-weighted alternative rather than only restating a dimension count.

Let H=T T* be positive semidefinite, R a positive integer, and d_i=<e_i,H^R e_i>. Positivity gives |(H^R)_(i,j)|<=sqrt(d_i d_j). Spectral Holder/Jensen therefore gives, for every f,

    ||T* f||_2 <= ||f||_2^(1-1/R) (sum_i |f_i| sqrt(d_i))^(1/R).    (M1)

If d_i<=epsilon^(2R), this becomes

    ||T* f||_2 <= epsilon ||f||_2 (||f||_1/||f||_2)^(1/R).          (M2)

It is not justified to replace the last factor by one merely because the signs of f are known.

To test this with actual Mobius signs, take f_n=mu(n)R_Z(n) on a positive-power interval (U,2U], and let N_f be its nonzero support count. Its entries there are +/-1, so (||f||_1/||f||_2)^2=N_f. If Z<U, all primes in that interval belong to the support; the prime number theorem gives N_f >> U/log U.

Let u=f/sqrt(N_f) and define the rank-one operator

    T=epsilon N_f^(1/(2R)) u u*.

Every diagonal entry of (TT*)^R on the support equals epsilon^(2R), while ||T*u||=epsilon N_f^(1/(2R)). Thus (M2) is sharp even with this fixed rough Mobius sign pattern.

For U>=X^kappa and 2R~sqrt(L), the permitted loss is at least exp((kappa+o(1))*sqrt(L)). The test does NOT assert this rank-one matrix is the actual determinant operator. It shows that diagonal moment data, actual signs and rough support alone do not prove the missing mixed correlation. An off-diagonal/source-weighted moment theorem is still needed.

## 6. Direct scalar attempt and its exact outstanding field

The inherited roughening report proves, on the SAME fully reassembled centred functional,

    L_X(R_Z I1), L_X(R_Z I2), L_X((1-R_Z)Lambda) = O_A(XM L^(-A)).

Hence Vaughan's exact identity also yields

    L_X(R_Z T_Y)=L_X(Lambda)+O_A(XM L^(-A)).                       (V)

This is useful for auditing fidelity, but not a new estimate for either side. The remaining object is still a prime-weighted affine divisibility discrepancy with the actual coherent row coefficients, moving profiles, and centering. No pairwise independence of the two affine forms is established.

In particular, rough support cannot make the right side of (V) disappear. Any direct HLC application still lacks the original polynomial slopes, their measure, and the complete coefficient/profile adapter. Full-circle identities (S), (V) do not establish restricted minor-arc bounds.

## 7. No-long-Mobius endpoints and restoration

For prime p>max(Y,Z), exact Vaughan faces are

    R_Z(p)=1, I1(p)=log p, I2(p)=T_Y(p)=0.

Thus a same-argument source-local construction acting only on R_Z T_Y cannot recover the prime slot. This does not rule out a proved nonlocal or pre-split signed identity. The Vaughan divisor r=1 must not be identified with a factory label d=1 without an explicit map.

The original source register lists two still-open endpoint classes: k=0,J=empty and k>=1, both containing d=1. Its formula for grouped leaves and its measure/energy budgets are retained as stated; no exhaustive current executable map or new Lean provider is claimed here.

The TWO unpaid analytic owners remain:

    A: |L_X(R_Z T_Y)| <<_A XM L^(-A),
       or a separately source-matched minor-arc theorem;
    B: |W_theta^rough| <<_A X L^(-A-C_src), uniformly on the actual image,
       or a genuinely sufficient integrated Gram/covariance theorem.

The latter Gram condition is sufficient for the endpoint scalar, not logically equivalent to it. Full R11 additionally needs every other sector, comparisons, twists, companions, source measures, occurrence quantifiers and the single licensed normalisation. Ford-Maynard Proposition 7.22 consumes Type-II information; it does not prove these inputs.

## 8. Evidence and publication status

The incoming checker reruns with identical ordinary and -O outputs. Its historical 4,276 count includes 186 floating-point slope diagnostics and support-only endpoint tests; it is not a certificate for Gram cross terms. We do not relabel those as exact analytic verification.

The new verifier uses only integer and Fraction arithmetic, formal log(prime) polynomials and Gaussian-rational coefficients. All asymptotic estimates depend on the written proofs and declared hypotheses, not the number of checks.

The native fixture has X=4096, M=4, c in (256,512], row coefficients of unit modulus at m=5,7, Z=7 and comparison cutoff z=13. Its nonrough detector error contains m=5,c=437,N=2187=3^7, and its Gram cross term is nonzero. This is a physical arithmetic-envelope fixture, NOT a live Ford occurrence certificate.

No Lean executable or independent human referee is used. The random-configuration adapter from the incoming report is not re-audited or newly certified in this focused four-claim audit.

## 9. Status

What done — HLC literal restriction checked at the printed parameter order; endpoint scalar roughening retained under explicit cutoff support; actual Gram cross term repaired; source-signed diagonal-moment capacity tested; prime-slot distinction retained.

What remains — Rough mixed signed cancellation, rough endpoint covariance, exact occurrence/provider coverage and Full R11/HSTAR. No new terminal signed PAY is claimed.

Next frontier — Off-diagonal/source-weighted determinant control beyond (M1), or a direct centred prime scalar estimate; independently cover the complete no-long-Mobius endpoint with its prime slot and comparison.
