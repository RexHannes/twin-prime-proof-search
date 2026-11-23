# Opposite output parities on the original two-prime outer set

Base: f7673e752d5832b1f7cce0c82c009aec3c3314ec. This paper tests the signed prime covariance with the original outer indicator in place throughout. Its mathematical conclusion is a limitation of congruence pairing. It gives no new full upper, S3, or G5.

## An eight-factor chamber paired with the original triple

Use I=(x/2,x], L=log x, and the original M=pq with p,q in the bands at .303 and .322 of radius .0001 in log_x coordinates. In the first channel choose a prime r in I/M. In a second choose six primes u,v,w,a,b,c with t=uvwabc in I/M. The first five occupy disjoint bands of radius .00001 about .027,.011,.012,.161,.080 respectively; thus the last lies within .00025+O(1/L) of .084. The differing bands distinguish every label, so each physical output has one owner. The six-factor residual and the original three-factor residual are disjoint.

On n=Mr the native f=Φ−ψ equals −2 by the rank-changing proof at the base. On n=Mt it equals the strictly positive weight

    W(M,t) = (1−(log d/log n)²)/64³,         d=u·v·w·p·a.

Here and below d contains the .303 prime p in the actual M. To verify the formula, in thousandths at the centre the eight exponents are 303,322,27,11,12,161,80,84. The closest subset sums to one half are .498 and .502. Every subset sum varies by at most .00025+O(1/L), using its complement if the dependent coordinate occurs. This remains true on changing from log x to log n up to O(1/L). There is no exceptional coordinate near 1/5. Every accepted subset has its native Möbius sign, and the accepted subsets are exactly those below one half: the total and big-part cutoffs have slack, and accepted big coordinates individually exceed 1/5. Complementary subsets have the same sign at even rank, giving H=0. All factors are above the subpower marked presieve eventually. The three distinguished banks have exactly the labels u,v,w. Among subsets of the remaining five coordinates, only .303+.161=.464 lies in the cofactor bank (.463,.465]; all other sums are at least .003 from .464. These statements have slack also when the bank uses x/2. The unique marked divisor has five factors, hence Möbius sign −1. The small .011 coordinate makes the rank test fail, eight is retained, and the five-box selector vanishes. Therefore f=H−K=W. The reference is the exact FMSource and FMDirect definitions. The triple and the eight-factor output have opposite Liouville signs.

## A direct test with every physical input retained

Write θ(k)=log k on primes and zero elsewhere. At each physical M let N₁ and H₁ be the ordinary count of r and the sum of θ(Mr−2). Let N₆ and H₆ denote the W-weighted ordinary and shifted-prime sums over t. Let N₃,H₃ denote the unweighted three-prime residual channel of the earlier paper. Set λ₆=N₆/N₁ and λ=(2N₃+N₆)/N₁. For large x the denominators are positive by the prime number theorem. On these three disjoint physical populations the complete centred contribution, in the native units before division by S_b, is exactly

    Σ_{M=pq} [2H₃+H₆−λH₁ − (2−λ)(H₁−𝔖₂N₁)].

Other native populations retain their original contributions. The −2 triple has been charged once across the two switches. No weight depending on p has been extended to an unlabelled rough M.

Consider D=Σ(H₆−λ₆H₁). Pair every allowed r with every allowed t at the same M. Their signed difference has weight W(M,t)/N₁, so summing reproduces D exactly. Let D_diff restrict these pairs to r and t of different residues mod 3. All residues of M,r,t are units. Exactly one of Mt−2 and Mr−2 is then divisible by 3; both exceed 3. For each M let N₁,b and N₆,b count the forbidden class, with the same W-weight in the six-factor channel. Summing the two orientations gives

    D_diff = Σ[(N₁,b/N₁)H₆ − (N₆,b/N₁)H₁]
           = D/2 + O_A(x/L^A)                          (all fixed A>0).

For proof, uniformly in the original M, N₁,b=N₁/2+O_A(x/(ML^A)) and N₆,b=N₆/2+O_A(x/(ML^A)). In the latter statement fix the five named labels and use the prime number theorem in either nonzero class mod 3 for the final c on (Y/2,Y], Y=x/(Muvwab). Its log is comparable to L uniformly. The factor W has bounded variation there because d is fixed and log n varies monotonically. Partial summation and the bounded reciprocal mass of each of the five fixed prime bands sum the errors. Finally N₁ is bounded below by a fixed multiple of x/(ML), the prime weight is at most L, N₆≪x/(ML), and Σ_{M=pq}1/M≪1. Arbitrary log savings absorb the log factors. This calculation uses equidistribution of the ordinary partner; it makes no equidistribution assumption for the true shifted-prime weight. The equal-residue pairs also carry D/2 to this accuracy. Mutual exclusion does not decide the sign of either half.

## Regular congruence pairings

The same argument applies for fixed B and moduli m=m(M)≤L^B. Every residual prime exceeds m eventually. At each M allow a relation on the unit classes of (t,r) modulo m, with the same degree on every row and every column. Let ρ_M be that degree divided by φ(m). By Siegel–Walfisz on the final prime, the ordinary partner weight in every allowed neighbor set equals ρ_M times its full mass up to O_{A,B}(x/(ML^A)), uniformly in the relation. Sum the per-class estimates with extra log precision to absorb φ(m). For W use the same partial summation in c at fixed p. Applying this once in each orientation proves that the restricted signed sum is

    Σ_{M=pq} ρ_M [H₆−λ₆H₁] + O_{A,B}(x/L^A).

For fixed density this leaves a scalar multiple of the unknown. Varying density with M can reweight outer fibres and must be accounted for in the complementary fibres. For nonregular relations, the separate row and column degrees remain attached to the actual shifted-prime sums. No result here prices those unequal marginals or proves that all arithmetic instruments fail. A strict normalized negative bound for D would already force actual prime inputs in the three-factor channel because H₆ is nonnegative. The complete source must also retain the unmatched term above. Tests of local admissibility alone supply neither bound.

References: [original source and three-to-five comparison](https://github.com/RexHannes/twin-prime-proof-search/blob/f7673e752d5832b1f7cce0c82c009aec3c3314ec/eth_research/proofs/rank_changing_prime_switch.md) and [Koukoulopoulos, The Distribution of Prime Numbers, Chapter 12](https://dms.umontreal.ca/~koukoulo/documents/publications/primes.pdf).
