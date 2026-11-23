# An explicit higher-rank core for the complete native signed source

For f=Φ−ψ fix any 0<a<1 in the original FM outside coefficient C_w(f). Let L=log x. The following uses fixed powers and keeps both signs of f. Given any tolerance η>0, there exist first 0<t<1/12 and then 0<e<min(t,ζ) for which

    limsup | C_w(f) − Σ_{x/2<n≤x} f_x(n) μ²(k) R_{x^e}(k)
                 1_{ω(k)≥3} D_t(k) | / S_b ≤ η,        k=n−2.

Use U=V=x^t, H=x^(.5−2t). For squarefree k let s be the product of its primes ≤U, let m count the prime divisors in (U,H], and define M_s(U)=Σ_{d|s,d≤U}μ(d). The explicit corrected coefficient for arbitrary squarefree k is

    D_t(k) = 1_{k prime} log k + [(m−1)log k + log s] M_s(U).

Thus both k and n are polynomially rough with fixed, finite ranks. The prime boundary is restored before projecting to rank ≥3. The theorem pays a controlled signed perturbation and a near-half semiprime population. It supplies no favorable estimate for the remaining signed core.

## Complete identity and legal correction

Put D=U². In this retuned Vaughan identity the short product is empty because both factors must exceed U. Every label ℓ>U has the full complement divisor prefix M_s(U), independent of ℓ, since every divisor d≤U has only primes ≤U. For a composite squarefree k the sum over d|k/ℓ has zero untruncated Möbius sum. The original coefficient on this representation is −log(k/s)M_s(U). When k is prime, restore +log k exactly. Add the centered measurement

    log k · Σ_{U<ℓ≤H,ℓ|k} Σ_{d|k/ℓ,d≤U} μ(d)

on the entire source, with both signs of f present. It is exactly m log k M_s(U). For the subpower input mask R_w its total is o_{t,f}(S_b). Indeed the combined modulus ℓd≤x^(.5−t) has a unique largest prime ℓ>U≥d. Fold the input presieve as in uniform_native_transfer.md, at fixed positive margin below 1/2. In the primitive principal after separating n and ℓ, the harmonic rough Möbius prefix is A_{nℓ,w}(U)=O_{B,t}(L^−B) for every B. Other factors cost at most a fixed power of L. The same retuned Vaughan principal is the native genuine prime sum minus S₂Σf+o_{t,f}(S_b), so the original sharp whole outside agrees with this retuned corrected whole outside up to o(S_b).

## Changing the input mask in the presence of the added measurement

At fixed t rerun sharp_polynomial_presieve.md with z=x^e and sieve-modulus level x^{t/2}. For the original retuned Type I terms e₀≤U²=x^{2t}, and for the probe e₀≤HU=x^(.5−t); with the smooth sieve divisor included every modulus is ≤x^(.5−t/2). The actual profile satisfies the same progression estimate. Absolute costs are O_t(e^−2 E(t/(2e))) in S_b units plus o at fixed e. The harmonic Möbius prefix at U is ρ(t/e)+o_e(1). The additional principal of the probe, including the log k weight, is O_t(e^−1ρ(t/e))+o_{t,e}(1) because Σ_{U<ℓ≤H}1/(ℓ−1) is O_t(1). The omitted squareful inputs with a repeated prime >w or >z are negligible under the divisor bound. The remaining first/second Type I errors tend to zero as e↓0 for this fixed t, exactly as in the original proof. This proves a collective signed approximation of the full corrected source; it uses no claim about separate physical rows surviving a retune.

## Prime, semiprime and higher-rank bookkeeping

For prime k, D_t(k)=0. If k=pq with p<q, then q>U on the dyadic range for large x. When p≤U, s=p and M_s(U)=0. When U<p≤H, s=1,m=1 for large x, since two primes ≤H cannot reach x/2−2; again D_t(k)=0. When p>H both factors exceed H and D_t(k)=−log k. For this last band bound ∣f∣ by its uniform bound and preserve the original output roughness P⁻(pq+2)>x^ζ. At fixed p the simultaneous upper sieve on q and pq+2 is ≪_ζ x/(pL²) uniformly for H<p≤√x and 0<t<1/12. For instance sieve odd primes through x^{min(ζ,.001)}, and use the ordinary upper large sieve with distribution length x/p≥x^.5. All such sieve primes are distinct from p. Multiplication by log k and summing 1/p over H<p≤√x gives O_f(log((1/2)/(1/2−2t)))S_b+o_t(S_b), with a constant independent of t. For all retained semiprimes the physical sum has now been estimated exactly or absolutely. For rank ≥3, 1<s≤U still implies M_s(U)=0. For s=1 the factor (m−1)log k can carry a substantial signed contribution through f and is retained.

For the stated η, choose t for the near-half cost and then e for the two analytic perturbations. Finally let x→∞ at these fixed parameters. This order does not allow a subpower cutoff to replace U inside this demonstration. Charges on all higher ranks, including s=1, remain inside D_t. Replacing this explicit higher-rank sum by a bound on its adverse part alone can destroy terminal capacity, as the separate subpower signed restoration calculation demonstrates.
