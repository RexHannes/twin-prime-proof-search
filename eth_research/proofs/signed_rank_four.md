# Signed rank-four face bounds on the native ledger

Use the complete paper ledger on the 1,566 native boxes of branch commit
`528f762ac6a5f921ca0335ef52a7e94aa565c02d`. Its analytic inputs, limits,
box mass, and masks are unchanged. This note bounds the **omitted rank-four
remainder** before it enters the global identity. Rank four is a companion
in that identity; claiming the same amount a second time as a direct saving
from the outside prime covariance would double count.

Set λ=7/3, ε=10⁻⁹, δ=ε/400, ν=1/5−2ε, β=1/2−2ε, and ρ=1/100.
Write H for the native rank-four kernel and W for H multiplied by the original
off-good mask and physical roughness mask. The marked kernel K is zero here
by the four-factor size inequality in `collar_ledger.md`. The physical
comparator satisfies B(W±)/S_b→Π(W±), and the actual shifted prime sum
A(W±)/S_b has limsup at most (10/3)Π(W±) as proved in
`complete_ledger.md`. Throughout, inequalities for normalized physical sums
are asymptotic up to o(1) or, equivalently, bounds on their limsup.
If R=A(W)−B(W), these estimates give separate upper bounds for ±R/S_b
by Π(q(±W)), with q(v)=λ max(v,0)+max(−v,0). Indeed for +R charge
the positive actual term, drop the subtracted nonnegative actual term,
and retain both ordinary terms. Apply the same argument to −W for −R.
The convex piecewise linear q is positively homogeneous and subadditive,
and q(±v)≤λ|v|. The off-good mask can be dropped **after** majorization
by nonnegative functions for either sign.

On the simplex of four labeled exponents t_i≥δ with sum one, write
s_A=Σ_{i∈A}t_i. Physical exponents above the moving rough threshold
log(x^δ)/log n satisfy this lower bound as n≤x. Let E consist of the
coordinates in [ν,1/5]. For any coordinate set J define
F(J)=Σ_{A⊆J, s_A<1/2}(−1)^|A|. For an actual squarefree n of rank four,
the subset-product half equality cannot occur (it would make n a square),
so complementary subsets have equal parity and F([4])=0. Angular equality
faces have zero measure independently.

Remove E from [4] one coordinate at a time, keeping every physical coordinate
in the sum-to-one relation. The total change is a sum of D_i, where deleting
t=t_i from the currently available set {i}∪J gives exactly
D_i=Σ_{A⊆J, s_A<1/2−t}(−1)^|A|. Every subset meeting E is annihilated
by the native kernel: an exceptional selected factor is designated big but
has exponent ≤1/5. On subsets avoiding E, the actual kernel coefficient
is either its reference Möbius sign or zero. All terms with s_A≤β
are accepted (including the large-factor-sum test since that sum is ≤s_A);
no term with s_A≥1/2 is accepted. Indeed the surviving big exponents all
exceed 1/5 and the native big-part cap is β, so at most two such
exponents occur, and g0 then has the required sign. Consequently H is the
sum of the D_i, a **positive** count of certain omitted odd subsets, and a
**negative** count of certain omitted even subsets. Omitted subsets in these
two counts each satisfy β<s_A<1/2 and contain no exceptional coordinates.
For each count its own unrestricted narrow-subset count is a valid upper
bound. This identity, including the parity of omissions, precedes taking
absolute values or integrating.

## 1. The two narrow boundary costs have equal upper envelopes

Let C=26.022 and Q=4ε C²/[β(1−β)]. For h=1,2,3 the density for the
sum of h exponents at v is at most (h/v)log^(h−1)(v/δ). This follows by
multiplying the reciprocal-product density by v=Σt_j and integrating the
other h−1 coordinates over [δ,v]. Both v∈(β,1/2) and 1−v are at most
1−β, and log((1−β)/δ)<C by the baseline rational certificate.
After dropping the masks and dividing by 4! on the labeled simplex,
the multiplier for h is binom(4,h)h(4−h)/24, namely 1/2, 1, 1/2.
Thus the odd and even omitted counts **separately** have Π-mass at most
Q/2, using the width 2ε and v(1−v)≥β(1−β).
Even if the masks give unequal actual masses, q applied to their signed
sum costs at most λ times one bound plus the other. The same upper holds
with reversed signs. The resulting term is (λ+1)Q/2=(5/3)Q.

The preceding step alone gives |R|/S_b at most λE_old+(5/3)Q, with
E_old=2ε(26.492)²/[ν(1−ν)] from the original exceptional bound.
It saves (2/3)Q in each ledger direction.

## 2. Cancellation from a small companion exponent in the exceptional sector

For each exceptional deletion, |D_i|≤2. To check this with ≤3 remaining
coordinates, a downward family containing the triple is the entire cube
and its alternating sum vanishes. Otherwise the sum is 1−j+k for j permitted
singletons and k permitted pairs. For j≤3 and 0≤k≤binom(j,2) its modulus
is ≤2. When **all three physical** companions are >ρ, the preceding
convolution density with lower cutoff ρ and log(1/ρ)<4.606 gives
an integrated bound for Σ_i |D_i| on these rows of

    E_big = 2ε (4.606)²/[ν(1−ν)].

The coefficient 4·2·3/24=1 counts the four possible exceptional coordinates,
the height two and the three-variable convolution. This bound can be applied
using symmetric majorants regardless of the order of deletion.

On any remaining row choose a physical companion u≤ρ. Because ρ<ν,
this coordinate is still available in J, including after earlier deletions.
Pair the subsets in D_i with and without u. Their difference per pair is
supported on 1/2−t−u ≤ s_A < 1/2−t. Among subsets of the other two
physical coordinates, neither the empty subset nor the full pair can lie
in this interval, since the two sum to 1−t−u. Every contribution must
therefore come from a singleton v in this interval. All allowable subsets,
including when earlier deletions suppress one or both, are covered by
counting every possible ordered choice of u and v. The fourth physical
coordinate is r=1−t−u−v. Then v≥.29 and r≥.49. The interval for v has
length ≤u. Summing over the possible exceptional, short and singleton
labels and integrating with measure dt du dv/(tuvr) gives

    E_tiny ≤ (4·3·2/24)·(2ε/ν)·∫₀^ρ (du/u) u/(.29·.49)
           = 2ερ/[ν·.29·.49].

The absolute majorant counts every deletion even when E has multiple
coordinates and every tiny owner when there are several (an upper bound).
No pullback to a different input sequence, assumption of independence,
or unweighted replacement of an actual prime population is used.

Combining both directions with the signs in part 1 proves

    limsup |R|/S_b ≤ D_new = (7/3)(E_big+E_tiny)+(5/3)Q
                   < 0.000018677605997449.

For the signed sum before division by S_b, the limsup statement means
limsup_x |R(x)|/S_b(x). The former debit was D_old=(7/3)(E_old+Q).
The improvement D_old−D_new exceeds 0.0000270723817587424. The complete
ledger subtracts or adds the absolute debit once, so its whole upper
decreases by this amount and the whole lower increases by the same amount.
Combining with unchanged box calibration and nonnegativity gives a
strictly smaller upper for the complete native outside, not just this
factor population. The accompanying rational replay uses the original
J4 enclosure. Separate tighter enclosures can be substituted for the same
J. The certificate does not yield a strictly positive twin-prime reserve.

All dependencies for the actual and comparator arithmetic sums are the
existing written analytic arguments. The new parts are the signed
subset partition, the cancellation on the exceptional face and the
elementary bounds. No formalization of the new inequalities is asserted.
