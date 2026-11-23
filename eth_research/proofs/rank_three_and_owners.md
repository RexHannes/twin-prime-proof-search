# Paying the adverse rank-three sources in the fixed-power representation

Use the sets, parameter order and corrected coefficient of simultaneous_core.md. Write f=f₊−f₋ where both parts are nonnegative. Define the scalar B=1_prime(k)log k−log(k/s)M_s(U), the raw retuned coefficient, and the pair correction on squarefree k

    P_t(k) = Σ_{p<q≤U, pq>U, pq|k} log(k/(pq))
                 Σ_{d|k/(pq), d≤U} μ(d).

All p,q in this formula are primes, with each unordered pair used once. Use the following physical coefficient over every retained k:

    Z_t(k,n) = f₊(n)[B(k)−P_t(k)] − f₋(n)D_t(k).

At subpower input roughness the total differs from the original signed O by o_t(S_b). With the polynomial mask x^e the additional absolute difference of totals in the iterated limit is arbitrarily small. The fixed-rank-three sector of Z_t is pointwise nonpositive and the adverse rank-two sector costs O_f(t)S_b in limsup. This is an upper decomposition with an explicitly retained favorable companion. No uniform smallness for the remaining ranks follows.

For the pair correction, pqd≤x^{3t}. The common log k is available by the primitive common-prefix estimate; the other weight −log(pq) is fixed for a marked pair. Multiple pairs at a given modulus cost at most O(L²) representations. In the subpower-mask case absolute squareful deletion and the small-prime fold have arbitrary log savings. After factoring primitive 1/φ(pq), the inner sum with d coprime to npq is A_{npq,w}(U); it has arbitrary log savings uniformly. If squarefreeness is first dropped, the overlap terms at p|d or q|d have an additional factor at most 1/w in the primitive main. At fixed z=x^e the same overlap costs o_e(1) per normalized source. The remaining prefix is ρ(t/e)+o_e(1). For the sieve-envelope error sum the ungrouped primitive harmonic coefficients: allowing every pair z<p,q≤x^t costs O((1+log(t/e))²); the d sum costs O(1/e), and g_z L≪1/e. Under x^{t/2} small-prime sieve level the moduli remain below x^{3.5t}<x^{1/2}. Thus the extra error in S_b units is O_{t,f}((1+log(t/e))²[ρ(t/e)/e + E(t/(2e))/e²])+o_{t,e}(1). The two other transfers are established in simultaneous_core.md.

Write k=pqr squarefree in the dyadic window for a physical rank-three input. If all factors exceed U, then B=−log k, P_t=0, and D_t=(m−1)log k≥0 since three primes >H would exceed x. If exactly one factor lies below or at U, M_s=0 and P_t=0. If two such primes p,q have pq≤U, their four divisors give M_s=0 and P_t=0. If pq>U, their two singles give M_s=−1, the remaining prime r exceeds H, and B=D_t=P_t=log r. Three small primes cannot form k. Hence f₊(B−P_t)≤0 and −f₋D_t≤0 in every case. On rank two, P_t vanishes. All remaining adverse rank-two weight lies on the same near-half band of simultaneous_core.md; f₊ may supply an additional favorable rank-two term and is retained. On primes Z_t=0. In particular an upper on Ω(k)≥4 without the favorable lower-rank terms is a valid sufficient route if it is independently small enough. Its magnitude must be established, with all constants in t recorded, before it can improve the numerical full bound.

## Finite extensions and their cost

For any fixed integer J≥2 choose t<min(1/12,1/(3(J+1))). For i=2,…,J add the full-source zero-mean corrections

    Q_i(k)= Σ_{S⊆{p|s}, |S|=i} Σ_{d|k/∏_{p∈S}p, d≤U} μ(d).

One can start directly from f₊B−f₋D_t and subtract log k·|f| Σ C_i Q_i. For exactly j small primes Q_j=1 and |Q_i|≤binom(j,i)2^{j−i}. The finite coefficient bound |B|,|D_t|≤2^j(2+1/t)log k follows from m≤1/t on this window. Choosing C_j=2^j(2+1/t)+1+Σ_{2≤i<j}C_i binom(j,i)2^{j−i} therefore makes every sector with 2≤j≤J nonpositive. At j=0,1 the correction vanishes and the original sign and near-half semiprime analysis applies. Each probe has modulus ≤x^{(i+1)t}, finite tag multiplicity, zero harmonic Möbius mean with R_w, and at fixed polynomial input cost bounded in S_b units by O_{t,i}((1+log(t/e))^i [ρ(t/e)/e + E(t/(2e))/e²])+o_e(1). Consequently the construction can confine all still-adverse rank ≥3 contributions to inputs with more than J small factors, while carrying every earlier negative term in the complete equality.

These finite extensions transfer a growing debt. In particular when all input primes exceed U, the favorable f₊ composite row equals −f₊log k and survives every correction unchanged. Its total has magnitude ≫_f S_b/t for small fixed t in the successive large-x limits: the two-sided sieve with spare profile level gives ∑ f₊ R_U log k ∼_{t↓0} S₂e^{−γ}Σf₊/t, ∑f₊ is a positive multiple of S_b, and the genuine prime exception is O_f(S_b) by the complete prime upper on the positive angular profile. Nonsquarefree errors are negligible. Discarding this favorable cohort before estimating the complementary positive terms destroys the scale needed for closure. The open joint inequality is for the appropriately centered, complete sum on the retained physical outputs, at scale S_b.
