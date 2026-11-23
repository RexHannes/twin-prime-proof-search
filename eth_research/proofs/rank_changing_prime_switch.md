# A three-to-five factor comparison on genuine shifted primes

All logarithms are natural. Use the native outside profile f=Φ−ψ at commit 528f762ac6a5f921ca0335ef52a7e94aa565c02d. Put I=(x/2,x], L=log x, θ(k)=1_prime(k)log k and S_b∼𝔖₂x/(2L). This experiment proves a signed comparison on genuine shifted primes with a broader outer variable. The original restriction on this variable is precisely the remaining expense.

## Two chambers with opposite physical signs

Write B(t) for the prime interval x^(t−η)<p≤x^(t+η), η=0.0001. The physical outer set consists of M=pq with p∈B(.303), q∈B(.322). Set J=[x^.6248,x^.6252]. For every real M∈J let N₁(M) count primes s in I/M and let N₃(M) count triples s=abc in I/M with a∈B(.052), b∈B(.132), c prime. For an integer M let H₁(M),H₃(M) count the same residuals weighted by θ(Ms−2). Each label is unique, including for the extension to arbitrary integer M: a,b,c are in disjoint exponent ranges, with the exponent of c within .0004+O(1/L) of .191. A single residual prime and a triple residual cannot coincide. On the physical set, the two outer primes also have disjoint bands from the residuals.

On these two physical sources the exact native weights are respectively −2 and +2 for large x. At the centres (.303,.322,.375) and (.052,.132,.191,.303,.322), the counts of subsets with sum below one half, by size starting at zero, are (1,3,0,0) and (1,5,8,2,0,0). Their distances to the nearest half-sum wall are .125 and .006. These gaps absorb the angular variation, the fixed native epsilon=10⁻⁹, and the O(1/L) change to logarithms normalized by log n. None of the coordinates is in the exceptional interval [ν,.2]. Thus H is the indicated signed subset sum: accepted subsets have the native Möbius sign, rejected subsets have sum above one half. The additional big-part cutoff cannot reject a subset whose total is below the lower margin. Every prime lies above the marked prime banks, so K=0. The triple passes good with three unit ranks. The five-factor row fails good on its smallest coordinate and has a forbidden third bin (19) in the sorted native box selector. Both rows are squarefree and polynomially rough. This proves the signs using the native definitions in FMSource, FMDirect and FMClosing.

Let λ(M)=N₃(M)/N₁(M). The denominator is positive for large x uniformly on J. Prime number estimates in the residual interval and reciprocal-prime summation on the two bands give, uniformly for R=1−log M/L,

    λ(M) = ∫_{.052−η}^{.052+η} ∫_{.132−η}^{.132+η}
                 R/[u v (R−u−v)] dv du + o(1) < .000012.

The centred native contribution of the two chambers is exactly

    2 Σ_{physical M} [H₃−λ H₁]
       −2 Σ_{physical M} (1−λ)[H₁−𝔖₂ N₁].

The matched part has zero ordinary mass at each M. The second term retains the unused negative population and its ordinary comparison. All other chambers stay in the complete ledger.

## A signed theorem with the actual prime selector

For any A>0 and any coefficients |b_d|≤1, let V(M)=Σ_{d|M, d≤x^.12} b_d. Then

    Σ_{integer M∈J} V(M)[H₃(M)−λ(M)H₁(M)] ≪_A x/(log x)^A.       (1)

The proof supplies a dimension-one distribution estimate individually for both nonnegative channels U₃=H₃ and U₁=λH₁. Set X₀=∫_J N₃(t)dt≪x. For odd d≤x^.12,

    Σ_{M∈J, d|M} U_j(M) = X₀/φ(d) + r_{j,d},
    Σ_{d odd, d≤x^.12}|r_{j,d}| ≪_A x/(log x)^A.                  (2)

Even d give no prime inputs. For fixed residual s and d, θ(Ms−2) with d|M is precisely the prime sum in class −2 mod sd over the allowed interval. The modulus is odd, and sd≤x^.4952. Each modulus occurs a uniformly bounded number of times: all residual prime factors exceed x^.0518 so there are only boundedly many choices for s among divisors of sd, and the three distinct bands specify its factors. The complementary d is then unique; it may share a divisor with s. The maximal Bombieri–Vinogradov theorem handles both endpoints and all these moduli with arbitrary logarithmic savings. The same holds for θ in place of Λ since the total trivial prime-power cost across moduli ≤x^.4952 is O(x^.9952 log²x).

Partial summation also allows λ(M) in (2). On each dyadic Y≤M≤2Y in J the denominator N₁≫x/(YL) and N₁,N₃≪x/(YL). The total variation of either count is O(x/(YL)): each is the difference of two monotone prefix counts. The total number of relevant triples in the swept residual interval is O(x/(YL)) by the prime upper bound for c and Σ_{a,b}1/(ab)≪1. The quotient has bounded variation per interval and O(L) variation over all J. For each s the intersection with I/s is a single interval.

Writing t for the real outer variable, the prime main density is s dt/φ(sd). Exactly,

    s φ(d)/φ(sd) = ∏_{ℓ|s, ℓ∤d}(1−1/ℓ)^(−1) = 1+O(x^−.0518).

After summing the two channels individually, the resulting power-saving error is O(x^(1−.0518) log^C x), using the nonnegative weights, X₀≪x and the harmonic sum of 1/φ(d). In the principal integrals λ(t)N₁(t)=N₃(t) pointwise. This proves (2) and hence (1).

## Polynomially rough outer variables and the exact unpaid set

Let 0<σ be small and fixed, and restrict the two channels to P⁻(M)>x^σ. Their true shifted prime weight forces M odd. On odd squarefree moduli the local density in (2) is the multiplicative function g(d)=1/φ(d). It has sieve dimension one, with V(z)=∏_{2<ℓ≤z}(1−1/(ℓ−1))≍1/log z. The two-sided fundamental lemma at D=x^.12 applied separately to each nonnegative channel gives the same principal X₀V(x^σ), with absolute errors bounded by O(X₀V(x^σ)E(.12/σ))+O_A(x/L^A). Here E(s) decays faster than any inverse power as s increases, and the dimension constant is independent of σ. Consequently

    lim_{σ↓0} limsup_{x→∞} |Σ_{M∈J, P⁻(M)>x^σ}(H₃−λH₁)|/S_b = 0.   (3)

Taking first large x is essential. For σ<.3029 every physical M=pq qualifies. Therefore the signed matched sum on the physical set equals the negative of the matched sum over *all other* qualifying M, up to the error in (3). The sign of that complement has not been determined. For example a prime M qualifies but is outside the physical set. Every short divisor test in (1) takes the same value b₁ on primes in J and on the selected pq. This observation concerns individual test values and gives no arithmetic equality of the two populations. A strict gain would need an estimate on that complement or a separate direct estimate with the physical pq factorization imposed. The chamber switch alone has limited capacity: Π₁<1.10·10⁻⁶, Π₃≤.000012Π₁; by the inherited 10/3 upper on these positive profiles, the normalized limsup absolute matched physical sum (including its factor two) is <9·10⁻¹¹. This does not pay the unmatched term.

Sources: Native definitions and analytic comparator at the pinned branch; maximal Bombieri–Vinogradov, https://personal.science.psu.edu/rcv4/Bombieri.pdf ; K. Ford, Sieve Methods, Theorem 3.6, https://ford126.web.illinois.edu/sieve2023.pdf .
