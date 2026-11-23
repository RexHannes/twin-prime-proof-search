# A payment at the terminal scale on the actual four-band adverse population

This result concerns the physical outside profile f=Φ−ψ and the sign-dependent representation in rank_three_and_owners.md. Write I={k:x/2<k+2≤x}, X=x/2, L=log x and S_b∼S₂X/L. For bounded native h let Π(h) be its angular profile, so Σ_{k∈I}h(k+2)∼Π(h)X/L when Π(h)>0. In particular Π(f₋)>1.64. Let 0<η<1/6, U=x^t, H=x^{1/2−η}, t small enough that 8t<min(ζ,1/2−η), and z=x^e with 0<e<t/4. Enlarging the gap below the half threshold is done in the complete sum: every added marker still has primitive product modulus below x^{1/2} by a fixed margin. The remaining semiprime band costs O_f(η)S_b with a constant independent of η; select η first and then t and e.

Let E consist of squarefree k∈I with precisely two prime factors at most U, one p∈(U^{1/4},U^{1/2}] and one q∈(U^{3/4},U]. Require at least one further prime in each of (U²,U⁴] and (U⁴,U⁸]. As before let m count factors in (U,H]. On this event k has at least five prime factors, R_z(k)=1, B−P=0, and the entire corrected signed summand is

    f₋(k+2) W(k),     W(k)=(m−1)log k+log(pq).

In the successive limits the genuine contribution is at least .021 S_b/t by the moment argument in higher_rank_charge.md. Bounding it by absolute value alone cannot pay it. Let d₋=S₂Π(f₋)/L. The following is a quantitative signed estimate on the same entire event, including m:

    lim_{t↓0} limsup_{x→∞} |Σ_{k∈E} [f₋(k+2)−d₋] W(k)| / S_b = 0                    (1)

for each fixed η in the stated range. The analogous assertion holds for the parts with m, 1, or log(pq) separately with their corresponding log weights. No prime-pair lower bound is assumed.

## Proof of (1)

At each x expand m as one extra prime ℓ∈(U,H] dividing k. Expand the two required occupancy indicators by inclusion–exclusion of the two events that a *whole* medium band is avoided. There are at most four terms. If the marked ℓ is already in a required band, that band is automatically occupied; terms asking for its avoidance are discarded. With r=pq or pqℓ fixed, the free cofactor k/r is sieved by all primes ≤U and the chosen zero, one or two forbidden medium bands. The ordinary count includes p=2 in the ≤U sieve; the native nonzero outputs impose odd k automatically. Marked p,q are uniquely specified on the exact event. When m is expanded every allowed ℓ is counted with its true multiplicity. Repeated square factors on the actual event cost O_t(x^{1−t/4}L^C); all factors of k there exceed x^{t/4} and the number of tags is bounded at fixed t.

Use the two-sided fundamental lemma of level x^{η/4}, with sieved primes at most U⁸. For the shifted profile target the local primitive density at odd primes is g′(p)=1/(p−1); for the ordinary integer count it is g(p)=1/p. The folded progression modulus is at most x^{1/2−3η/4+1.5t}, below x^{1/2−η/2} when t<η/16. Distinct tag representations have multiplicity at most a fixed logarithmic power. The signed native progression errors at this level are negligible to any fixed logarithmic power and the integral common weight log k is handled by partial summation. In the ordinary integer model each progression has O(1) floor error; their aggregate, including the finite logarithmic multiplicity, is o_t(X/L^C) for arbitrary fixed C. On the native side primes of the output can be removed from the primitive main at O_t(x^{−ζ}L^C) per output. In particular the extra marked ℓ need not be coprime to every candidate output before this correction. A tag prime shared with the cofactor sieve can be accounted for at p or q with an O_t(x^{−t/4}L^C) aggregate relative error: in 1/φ(rc) the ratio against 1/[φ(r)φ(c)] is ∏_{p|(r,c)}(1−1/p), and the ordinary 1/(rc) factorization is exact. A remaining shared medium ℓ is excluded by the occupancy branch. Working with the full positive and negative fundamental-lemma weights avoids an estimate for a sharp divisor-truncation remainder.

For each resulting term the shifted local product below U, divided by the ordinary product including 2, tends to S₂. Every extra forbidden prime in a medium band exceeds U, so its local product ratio is 1+o_t(1) by Σ_{p>U}p⁻²=o(1). Each named prime has the same 1+o_t(1) ratio when its primitive weight is compared to 1/p. These comparisons hold uniformly after summation at fixed t. The harmonic sums of p and q in their two bands are bounded by absolute constants. The possible ℓ introduces at most O(1+log(1/t)). At fixed t the genuine total profile Σf₋ differs from Π(f₋)X/L by o_t(X/L), also with its common log k weight, since log k=L+O(1) and the population estimate supplies the additional factor 1/L at fixed t. The choice d₋ exactly compensates for the product ratio S₂ in the ordinary model.

After both bracketing inequalities are summed the limsup in (1) is at most

    C_f (1+log(1/t)) E(η/(32t))/t,

where E(s)≪s^(−s/2) for s large. Here the log weight contributes at most O(L), while the complete small-prime factor is O(1/(tL)). The cost is absolute and applies to both signs of the difference. It tends to zero at fixed η, proving (1).

## Payment and what still has to be estimated

For the complete representation put d_±=S₂Π(f_±)/L, W₊=B−P and W₋=D_t. One can insert f_±−d_± throughout with an arbitrarily small limiting error after e↓0 at fixed η,t. On ordinary k, the common principal of the first Vaughan term is 1 per integer, matching Σ_{I}ϑ(k)∼X. The second term and additional tagged probes have a negligible principal with the original subpower input presieve. With a polynomial z the unsigned divisor costs in sharp_polynomial_presieve.md apply, now using divisibility 1/d, the product V_z and V_z log z→e^(−γ); the exponent headroom for a probe is positive. The primitive-free rough harmonic prefixes ∑ μ(m)R_z(m)/m again converge to ρ. Thus d_± times the ordinary full corrected coefficient is negligible in S_b units in the stated ordered limits. This operation retains the ordinary model over the *entire* complementary population as well.

Equation (1) now pays the specified actual rank-at-least-five cohort of the centered sum at the terminal scale, despite its uncentered physical contribution exceeding .021 S_b/t. It neither subtracts that large amount from the published complete upper nor grants a favorable sign to the other cohorts. The remaining condition is a strict estimate on the complete centered complement, including the unmarked prime boundary and all favorable contributions. In particular, a bare model-subtraction on E without the globally justified ordinary companion is insufficient.
