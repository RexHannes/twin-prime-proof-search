# Centering the entire nonempty small-prime sector

Use the notation of centered_charge_payment.md. Fix 0<η<1/6, U=x^t, H=x^{1/2−η}, with t small compared with η and ζ, and z=x^e, 0<e<t. For squarefree k, s is its complete product of primes at most U. Set W₊=B−P_t and W₋=D_t. For σ=+ or − write h=f_σ, d_h=S₂Π(h)/log x and let W denote its respective coefficient. Then

    lim_{t↓0} limsup_{e↓0} limsup_{x→∞}
      |Σ_{k∈I, s>1} R_z(k) μ²(k) [h(k+2)−d_h] W(k)| / S_b = 0.       (1)

The assertion applies separately to the two complete signs, with all true owner multiplicities retained. The forced-label four-band payment is a nontrivial subpopulation version proved separately. Equation (1) identifies the remaining centered correlation on inputs with zero small primes. It gives neither a favorable bound on that correlation nor a saving to be added to the current upper.

## Proof by short divisor sums, without assuming the missing prime correlation

Let W⁰ be the explicit expression for W with its genuine-prime summand 1_prime(k)log k removed. On s>1 it equals W, since a prime input in I is always above U. On squarefree inputs,

    R_z 1_{s>1} W = (R_z−R_U) W⁰.

There are only the following short divisor measurements in W⁰, including the weights log k or a log of a tagged prime:
the prefix Σ_{d|k,d≤U}μ(d);
this prefix times Σ_{p|k,p≤U}log p;
this prefix times the single marked count m;
and the pair-divisor correction P_t. For products with a repeated prime tag, one may group with the true least common multiple. For a pair specified in the quotient use pqd|k before deleting rough squareful inputs. All resulting modulus factors before the roughness sieve are ≤max(U³,HU). Coefficients of a fixed modulus have at most a fixed logarithmic-power loss: the rank or rank-two prime tags are specified and d is then determined up to the few named repeated prime factors. This validates the absolute summed progression error. The squared-prime exception is paid by the original divisor bound and R_z or R_U.

To compare the shifted profile h to its ordinary model d_h on R_z, use two positive fundamental-lemma weights for the extra presieve at level x^{η/4}. Works for t small enough that HU·x^{η/4}≤x^{1/2−η/2} and U³·x^{η/4} below the same level. Split every coefficient and h by sign as necessary. Common log k factors permit partial summation. Under the outer mask every base divisor has only primes >z; remove the others before the sieve. It is disjoint from the extra small-prime sieve divisor, so each base modulus is recovered from the combined modulus. The shifted principal is g_z/φ(b) with (k+2,b)=1 and the ordinary principal is V_z/b. Here b denotes any one positive base modulus. Because all its primes exceed z, b/φ(b)=1+o_e(1) uniformly for b≤x; shared primes with the output have negligible aggregate harmonic cost at fixed e,t since its prime factors exceed x^ζ and their number is bounded. The ratio g_z/V_z→S₂ includes the ordinary factor at 2. Both coefficient families have the same leading main after using Σh∼Π(h)X/L, including a common log(k)=L+O(1) weight. The roughness density supplies the needed extra 1/L for the O(1) variation. If Π(h)=0 use Σh=o(X/L) in the same comparison.

The sum of the normalized absolute bracketing errors is bounded by a fixed power of 1/e and 1+log(t/e), times E(η/(4e)), with constants depending on η,t and the fixed profile; it tends to zero at fixed t as e↓0. For this estimate sum the harmonic Möbius divisor in absolute value over R_z to get O(1/e), the two possible small labels each cost O(1+log(t/e)), while the single medium tag costs O(1+log(1/t)). The factor g_z log x costs O(1/e). Shared tags in the log s product may be split according to whether the named prime divides d; on overlap the modulus is d and the aggregate log weight of its tagged divisors is ≤log d. Thus this term also costs only a fixed power of 1/e. The primitive common-prefix errors of level below 1/2 have arbitrary log savings at every fixed e, t. This proves the R_z half for the successive limits.

On R_U the prefix is 1, log s=0, P_t=0 and W₊⁰=−log k, W₋⁰=(m−1)log k. There is at most one marked-prime *summation*, with exact multiplicity m at each physical k. Using the same comparison with sieve level x^{η/4} and primes up to U, the absolute normalized bracketing error is O_{η,h}((1+log(1/t))E(η/(4t))/t)+o_t(1). This tends to zero with t. Subtraction proves (1). No infinite sum over factor ranks or truncated occupancy index is used.

## The genuine prime term on the remaining stratum

On s=1 the expression W=W⁰+1_prime(k)log k is exact. The preceding R_U estimate pays the W⁰ terms at arbitrary terminal precision. The surviving signed term is therefore

    Σ_{k prime, k∈I} log k [ f(k+2) − S₂Π(f)/L ].

By the ordinary PNT this equals A(f)−S₂Σf+o(S_b). In these formulas all original native output masks remain inside f. This matches the full native Vaughan transfer independently and is a check on the sign and location of the surviving expense. Two-sided global centering is legal because on unshifted integers the ordinary PNT and the corresponding Type I/Dickman calculation annihilate the model as in centered_charge_payment.md.

Consequently a strategy concentrating exclusively on nonempty small-factor tags has zero new signed contribution at scale S_b after model payment. Returning the computed favorable mass from that sector while dropping the boundary above would use the model twice. To gain further terminal credit one needs genuinely new unmarked information on the complete covariance of the prime input and the two native output profiles, or an independent bound on the equivalent fully compensated owner expression.
