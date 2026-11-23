# A polynomial input presieve for the unaltered signed FM outside coefficient

Set L=log x, U=V=x^.24 and D=x^.49. Keep every prime label, strict threshold and squarefree condition in the native signed large-product coefficient B(k), with k=n−2. For h≥2 write

    C_h(f) = Σ_{x/2<n≤x} f_x(n) 1_{P⁻(k)>h} μ²(k) B(k).

The bounded output f may be the native Φ, ψ, Φ−ψ, or their positive or negative parts. For large x it has bounded rank and P⁻(n)>x^ζ on its support, ζ=1/(4·10^11), and ∑|f|≪_f x/L. Its signed and unsigned profiles satisfy the primitive product progression estimate proved in uniform_native_transfer.md, including common upper endpoints. All normalized sums use S_b∼S₂x/(2L).

**Theorem.** Fix 0<a<1 and w=exp(L^a). Then

    lim_{ε↓0} limsup_{x→∞} |C_w(f)−C_{x^ε}(f)|/S_b = 0.

In particular, for any requested error one can keep only squarefree physical inputs with every prime above one fixed power of x and with rank at most ⌊1/ε⌋. This is collective cancellation over the actual sharp tagged sum, including all original owners. It makes no statement about the sum of absolute row weights or an independently selected tag mask. The small-power exponent is chosen before letting x grow.

## Sieve cost with a fixed polynomial threshold

Write z=x^ε with fixed 0<ε<ζ. Apply the exact Vaughan identity used in uniform_native_transfer.md with the same original U,V,D. Prime inputs have weight θ(k) in either presieve. The proper powers and rough nonsquarefree inputs are negligible after the absolute divisor bound, since repeated primes now exceed z. It suffices to evaluate the same two Type I terms and the short product. Their moduli e₀≤x^.49 have no prime ≤z. The primitive progression is n≡2 mod e₀. Coefficients with the common factors log k extracted by partial summation are bounded by O(L) after grouping. For the short and Λ convolution sums this follows from Σ_{j|e₀}Λ(j)=log e₀. The positivity comparison can use the sum of the absolute ungrouped coefficients with the same O(L) bound.

For each e₀ sieve k/e₀ by the odd primes up to z, using the two dimension-one fundamental-lemma weights λ^± of level x^.002. They bracket the integer presieve pointwise. For each sign of the profile and coefficient, the total progression errors follow from the profile progression bound at level x^.492. In fact the representation e₀d is unique because primes of d are ≤z and primes of e₀ exceed z. The maximum cumulative coefficient is O(L), and the common weight log k costs one partial summation. All active n are coprime to d, so the sole remaining primitive exclusion is (n,e₀)=1. The main sum of λ^±(d)/φ(d) is g_z(1+O(E_s)) uniformly, where g_z=∏_{2<p≤z}(1−1/(p−1)), s=.002/ε, E_s≪s^(−s/2) as s→∞ with an absolute dimension-one constant. The dimension follows from the Mertens product for 1/(p−1) away from 2. The same upper and lower weights handle positive and negative coefficients.

On rough moduli, Σ_{e₀≤x^.49} R_z(e₀)/φ(e₀) ≪ 1/ε. This follows by comparing the Euler product, including all prime powers, to ∏_{z<p≤x}(1−1/p)⁻¹ with a bounded convergent correction. Also g_z L≪1/ε. Summing the majorant cost, including ∑|f|≪_f S_b, pays O_f(ε⁻² E_s) S_b+o_{ε,f}(S_b). This fixed-ε estimate is essential. A positive power of L multiplying E_s at fixed ε would invalidate the limiting argument.

## The degree-zero and degree-one Möbius means

For m odd put R_z(m)=1_{P⁻(m)>z}, with R_z(1)=1. At fixed ε and bounded 0≤v≤1, define the rough harmonic Möbius prefix A_z(x^v)=Σ_{m≤x^v}μ(m)R_z(m)/φ(m). Then, writing t=v/ε,

    A_z(x^v) = ρ(t) + o_ε(1),
    (log z)⁻¹ Σ_{m≤x^v} μ(m)R_z(m)log m/φ(m)
        = tρ(t)−∫₀ᵗρ(u)du + o_ε(1),

uniformly in v. Indeed m has bounded squarefree rank at fixed ε. Expand by rank j, divide the unordered labeled counts by j!, and use Mertens' theorem separately in each normalized logarithmic prime coordinate. The reciprocal p−1 may replace p with o(1) error, and repeated prime coordinates cost o(1). For j≥1 the cumulative limit of a rank j positive measure is continuous. Common-endpoint convergence is therefore uniform on the compact interval; the mass at the unit is handled exactly. The signed limit is the finite series

    Σ_{j≤t} (−1)^j/j! ∫_{u_i≥1,Σu_i≤t} du₁⋯duⱼ/(u₁⋯uⱼ).

It equals 1 on [0,1], and multiplication of its boundary derivative by t=Σu_i gives tρ′(t)=−ρ(t−1) for t>1. This specifies the Dickman function. Partial summation yields the second relation. Its standard properties give ∫₀^∞ρ(t)dt=e^γ and factorial decay. For the latter, tρ(t)=∫_{t−1}ᵗρ(t′)dt′ and monotonicity suffice. Exclusion of the at most 256 prime divisors of n or nℓ changes these prefixes by o_ε(1), with the same normalization in the log moment. The cost is O_ε(Σ_{p|nℓ}1/(p−1))=o_ε(1) where ℓ>z. For the second displayed prefix one multiplies this absolute bound by O(1/ε).

## The signed transfer

Mertens gives g_z log z→S₂e^(−γ), with S₂=2∏_{p>2}(1−1/(p−1)²). Put t₀=.24/ε. The first Type I principal per output is g_z[A_n(U)log k−B_n(U)], with B_n now the logarithmic harmonic prefix. Its difference from S₂ has limsup bounded by a constant times ε⁻¹ρ(t₀)+∫_{t₀}^∞ρ. For the Λ subtraction the main prefix has argument U, and the factor from summing log ℓ/φ(ℓ^j) costs O(L). The exact common-prime term has an extra 1/ℓ and is negligible, since all ℓ>z and the harmonic absolute prefix is O(1/ε). For the short-product subtraction the two main arguments D/ℓ and U are at least U whenever nonempty. The monotonicity of ρ and uniform convergence bound their difference by 2ρ(t₀)+o_ε(1). Its common-prime correction is negligible for the same reason. Thus all remaining principal errors divided by S_b are bounded in limsup by

    O_f( ε⁻¹ρ(.24/ε) + ∫_{.24/ε}^∞ρ + ε⁻²E_{.002/ε} ).

This expression tends to zero with ε. The original w transfer equals the same prime sum minus S₂Σf, with o(S_b) error. Subtraction proves the theorem.

**Scope in the closing ledger.** After choosing ε sufficiently small one may attempt the fixed-rank, jointly polynomially rough ORIGINAL k and k+2 problem, with prescribed tolerance on its entire sharp complement. The physical semiprimes and all associated positive and negative output terms still occur. A favorable source-specific estimate for the retained core is required for a strictly positive twin reserve. A restriction on k alone inserted into f cannot invoke its original product progression bound.

Koukoulopoulos, The Distribution of Prime Numbers, Theorem 19.1 (two-sided fundamental lemma): https://dms.umontreal.ca/~koukoulo/documents/publications/primes.pdf
Liu, Park and Song, Theorem 3.2 (underlying bounded-rank prime product progression estimate): https://doi.org/10.1007/s40993-017-0089-3
Lagarias, Euler's constant: Euler's work and modern developments, Theorem 3.5.1 (Dickman integral): https://doi.org/10.1090/S0273-0979-2013-01423-X
