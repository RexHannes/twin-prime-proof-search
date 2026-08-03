# Reciprocal Subset-Sum Entropy and Erdős #319: Critical Analysis

## Executive Summary

This document provides a rigorous assessment of the computational observations on reciprocal subset-sum entropy and their potential relevance to Erdős Problem #319. We separate proved facts from conjectures, identify the precise logical gaps, and propose a research roadmap.

**Bottom line:** The computational evidence is genuinely interesting and points to a plausible conjecture about bounded primitive support for smooth reciprocal identities. However, multiple substantial gaps remain between this conjecture and Erdős #319, and the conjecture itself is far from proved.

---

## A. What Is Already Proved (by Definitions)

The following are elementary consequences of the definitions, formalized and proved in Lean in `Elementary.lean`:

### A1. Injectivity Characterization

**Theorem.** `|Σ(Q)| = 2^|Q|` if and only if the map `U ↦ R(U)` is injective on subsets of `Q`.

*Status:* Proved (`subsetSumImage_card_eq_iff`). This is purely combinatorial — it is the statement that a function on a finite set has full image size iff it is injective.

### A2. Collisions from Non-Injectivity

**Theorem.** If the subset-sum map is not injective, there exist distinct `A, B ⊆ Q` with `R(A) = R(B)`.

*Status:* Proved (`exists_collision_of_not_injective`). Tautological negation of injectivity.

### A3. Disjoint Identity Extraction

**Theorem.** Given distinct `A, B ⊆ Q` with `R(A) = R(B)`, the pair `(A \ B, B \ A)` forms a disjoint reciprocal identity.

*Status:* Proved (`recipSum_sdiff_eq_of_eq`, `sdiff_nonempty_of_ne_and_eq`, `collision_to_identity`). The key step uses positivity of `1/q` for `q ∈ ℕ+`.

### A4. Collision Probability Formula

**Theorem.** `collisionCount(Q) = Σ_t subsetSumMult(Q,t)²`.

*Status:* Proved (`collisionCount_eq_sum_sq`). Standard double-counting.

### A5. Clearing Denominators

**Theorem.** For `A, B ⊆ Q` and `L` a common multiple, `R(A) = R(B)` iff `Σ_{a∈A} L/a = Σ_{b∈B} L/b`.

*Status:* Proved (`clearing_denominators`). Multiplying by `L` preserves equality exactly when all denominators divide `L`.

### A6. Basic Algebra

- `recipSum ∅ = 0`
- `recipSum {q} = 1/q`
- `recipSum (A ∪ B) = recipSum A + recipSum B` for disjoint `A, B`

*Status:* All proved.

### Important Non-Theorem

**H₂(Q) = |Q| iff all subset sums are distinct** — this is the *informal* statement people use, but it requires care: H₂ is defined via collision probability, which involves the *squared* multiplicity distribution. The formal equivalence `H₂(Q) = |Q| ⟺ CP(Q) = 2^{-|Q|} ⟺ all multiplicities = 1 ⟺ injectivity` holds but the Rényi entropy H₂ is a *real-valued* quantity involving logarithms. We have formalized the combinatorial core (injectivity ↔ full image size) and the collision count formula, which is the integer backbone. The logarithmic definition of H₂ itself was not formalized (it would be straightforward but not illuminating).

---

## B. What Is Computationally Observed

### B1. Forbidding Small Identities Restores Near-Injectivity

The central observation: for *y*-smooth composite denominators, after forbidding all reciprocal identities of support ≤ *s*, the entropy deficit `D(Q) = |Q| - H₂(Q)` drops dramatically.

| Universe | Anti-support | D(Q) | |Σ|/2^|Q| |
|---|---|---|---|
| N=32 composites, k=8 | ≤3 | 0.845 | 172/256 |
| N=32 composites, k=8 | ≤4 | 0.248 | 232/256 |
| N=32 composites, k=8 | ≤5 | 0.000 | 256/256 |
| y=7, N=50, k=9 | ≤4 | 0.604 | 393/512 |
| y=7, N=50, k=9 | ≤5 | 0.317 | 449/512 |
| y=7, N=50, k=9 | ≤6 | 0.114 | 491/512 |

### B2. Support Threshold Stabilizes

For *y* = 7, *N* = 50, anti-support ≤ 6, scaling *k* from 8 to 12: the minimum surviving support stays at 7. The deficit does not grow with *k* (it remains around 0.05–0.12).

### B3. Residual Identities Are Diverse

The support-7 identities that remain after forbidding ≤ 6 are not a single scaled family. Top family fractions are 3–10%, with many distinct support families and dilation-normalized families.

### B4. Phenomenon Persists for Larger Primes

Forced *y* = 11 (*N* = 60) and *y* = 13 (*N* = 70) tests show the same qualitative behavior: anti-support ≤ 6 yields min support 7 and small deficits, with diverse residual identity families.

---

## C. What Is a Plausible Conjecture

### C1. Bounded Smooth Reciprocal Circuit Conjecture (BSRCC)

**Conjecture.** For every smoothness bound *y* and every entropy deficit δ > 0, there exists a constant *C(y, δ)* such that for every finite set *Q* of *y*-smooth composite integers, if `|Q| - H₂(Q) ≥ δ`, then *Q* contains disjoint nonempty *A*, *B* ⊆ *Q* with `R(A) = R(B)` and `|A| + |B| ≤ C(y, δ)`.

**Assessment:** Plausible for fixed *y*, but with important caveats:

1. **The evidence is small-scale.** *k* ≤ 12, *N* ≤ 70, *y* ≤ 13. The stabilization at support 7 could be a finite-universe artifact: the number of available *y*-smooth composites ≤ *N* is itself bounded, and for *y* = 7 there are only ~20 candidates ≤ 50.

2. **The δ-dependence matters.** The data shows that as we forbid larger supports, the deficit shrinks but doesn't necessarily reach 0 (except in the exhaustive *N* = 32 case). The conjecture asserts that for any *fixed* δ > 0, a finite support threshold suffices. The data is consistent with this but does not rule out `C(y, δ) → ∞` as `δ → 0`.

3. **Exponents can grow.** For fixed prime set {2, 3, 5, 7}, as *N* grows, the exponent vectors *(v₂(q), v₃(q), v₅(q), v₇(q))* become increasingly varied. This means the integer kernel becomes richer, and it is not obvious that primitive element support stays bounded.

### C2. Weaker Plausible Variants

- **Sublinear growth:** `C(y, δ, |Q|) = o(|Q|)`. More plausible and might suffice for some applications.
- **Fixed-exponent version:** If all exponents are bounded by some *M*, then support is bounded by `f(y, M)`. This is more directly amenable to Graver-basis methods.
- **Contrapositive form:** Large minimum identity support implies near-injectivity. This is the form the data most directly supports.

---

## D. What Would Be Needed for a Real Proof

### D1. The Graver Basis / Primitive Partition Route

**Framework.** After clearing denominators with `L = lcm(Q)`, a reciprocal identity `R(A) = R(B)` becomes

`Σ_{a ∈ A} L/a = Σ_{b ∈ B} L/b`

This is a relation in the integer kernel of the weight vector `w = (L/q)_{q ∈ Q}`. With `{-1, 0, 1}` coefficients, these are precisely the *primitive partition identities* — a subset of the Graver basis of the integer kernel.

**What Graver theory gives.** The Graver basis of an integer program `Ax = 0, x ∈ ℤⁿ` has elements whose support is bounded by a function of the matrix *A*, specifically by the maximum absolute value of subdeterminants (by results of Cook, Gerards, Schrijver, Tardos). For a *single row* matrix `A = w^T`, the Graver basis elements have support bounded in terms of the entries of `w`.

**Critical issue.** For *y*-smooth *Q* ⊆ [1, *N*], the weights `L/q` can be exponentially large in *N* (since `L = lcm(Q)` grows). Standard Graver bounds depending on entry size would give support bounds growing with *N*, which is *not* what the conjecture claims.

**However.** The weights `L/q` have multiplicative structure — they are *y*-smooth numbers themselves. The question is whether this structure forces primitive `{-1, 0, 1}` elements to have bounded support. This is a more refined question than generic Graver theory addresses.

**Key reference direction:** The work of Geroldinger and collaborators on *zero-sum theory* over abelian groups, and the *Davenport constant*. The question of bounded-length zero-sum sequences over `(ℤ, +)` with prescribed coefficient sets is related but typically studied in finite groups.

**Verdict:** Generic Graver bounds are insufficient. A proof would need to exploit the *y*-smooth multiplicative structure of the weights.

### D2. The *p*-adic / Valuation Route

**Idea.** For each prime *p* ≤ *y*, consider the *p*-adic valuation. A reciprocal identity `R(A) = R(B)` with `A, B ⊆ Q` forces, after clearing denominators, an integer equation. The *p*-adic valuation of each side must agree.

**Layer peeling.** Consider the elements of *A* ∪ *B* with the highest *p*-adic valuation. In a primitive identity, the highest-valuation elements must "cancel" among themselves (otherwise the identity could be decomposed). This potentially bounds the number of elements at each valuation layer.

**What this could give.** If for each prime *p* and each valuation level *v*, at most `f(y)` elements can participate in a primitive identity at that level, and there are at most `g(y)` relevant valuation levels (which is problematic — valuation levels can grow with *N*!), one would get `support ≤ f(y) · g(y) · π(y)`.

**Obstruction.** The number of distinct *p*-adic valuation levels grows with *N* (since *Q* ⊆ [1, *N*] can have elements with *p*-adic valuation up to `log_p(N)`). So without further structure, this does not give a bound independent of *N*.

**Possible resolution.** In a *primitive* identity, the participating elements may be forced to span only `O(1)` valuation levels for each prime. The data (support 7 stabilizing) is consistent with this but a proof would require a new argument.

**Verdict:** Promising arithmetic approach, but the valuation-level growth is a real obstacle.

### D3. Anti-Concentration / Inverse Littlewood-Offord Route

**What's analogous.** The Tao-Vu inverse Littlewood-Offord theorem says: if the signed sum `Σ ε_i a_i` (with `ε_i ∈ {-1, +1}`) has high collision probability, then many of the `a_i` belong to a generalized arithmetic progression (GAP) of small rank and volume. This is analogous to saying high `CP(Q)` forces additive structure in `{1/q}`.

**Where the analogy fails.**
1. *Coefficient set.* Littlewood-Offord uses `{-1, +1}` (or `{0, 1}`) coefficients. Our subset sums use `{0, 1}` coefficients, which is the Littlewood-Offord setting, but the *identity extraction* uses `{-1, 0, 1}`.
2. *Additive vs. multiplicative.* The atoms `1/q` for *y*-smooth *q* have *multiplicative* structure (they lie in a finitely generated subgroup of `ℚ*`), not the additive GAP structure that inverse LO detects.
3. *Exact vs. approximate.* Inverse LO gives structural conclusions from *approximate* anti-concentration. We need *exact* rational identities.
4. *Target structure.* Inverse LO says the elements lie in a GAP. We want to conclude a *small* identity exists, which is a different conclusion.

**Possible adaptation.** For *y*-smooth rationals, the additive structure detected by inverse LO would correspond to approximate multiplicative relations. Converting these to exact identities would require additional number-theoretic input (e.g., the `1/q` values are separated by at least `1/lcm`, so approximate structure with gaps smaller than this becomes exact).

**Most relevant variant.** The *Nguyen-Vu* optimal inverse LO theorem gives rank bounds for the GAP. If the rank is bounded by `π(y)` (the number of primes), this could be exploited. But the conversion to a small identity remains unclear.

**Verdict:** Suggestive analogy but not directly applicable. An adaptation would be a significant new result.

---

## E. Relation to Erdős #319

### E1. What #319 Requires

Erdős #319 asks for the maximum size of a *primitive* pair `(P, Q)` with `R(P) = R(Q)`, `P, Q ⊆ [1, N]` disjoint. The known lower bound is `(1 - 1/e + o(1))N`. The "growing-*Q*" problem: prove that for `|Q|` exceeding this density, primitivity fails.

### E2. What BSRCC Would Give

If BSRCC holds, it gives: **low H₂(Q) ⟹ Q contains a small internal identity**. This is an *internal* statement about *Q* alone.

### E3. The Missing Bridge: Target Realization

For Erdős #319, the goal is not just an internal identity in *Q*, but finding `T ⊆ Q` with `R(T) ∈ Σ(P)`. The logical structure would be:

1. **[BSRCC]** Large *Q* → low H₂(Q) → small identity `R(A) = R(B)` inside *Q*.
2. **[???]** High density of *P* → `R(A) ∈ Σ(P)` (realization of a small rational target by a subset sum of *P*).
3. **[???]** Combining these violates primitivity.

**Gap 1: Large |Q| → low H₂.** BSRCC's hypothesis is low Rényi entropy, not large size. Why would a large set of denominators have high collision probability? For *y*-smooth denominators, this might follow from pigeonhole — many subsets of a large *y*-smooth set must collide because the subset sums live in a structured lattice. But this requires a separate argument.

**Gap 2: Realization theorem.** Given a small rational `r = R(A)` (with denominator bounded in terms of *y* and *C*), prove that a dense *P* ⊆ [1, *N*] has `r ∈ Σ(P)`. Results of Croot (2003) and Liu-Sawhney (2024) on unit fraction representations are relevant but address different problems:
- Croot: every sufficiently large *N* can be written as a sum of distinct unit fractions from [1, *N*].
- Liu-Sawhney: if *P* ⊆ [1, *N*] has density > 1 - 1/e + ε, then *P* can represent any sufficiently small rational as a subset sum of reciprocals.

The Liu-Sawhney result is the most directly relevant. If applicable, it would close Gap 2 and give: dense *P* can realize the target `R(A)`, yielding `R(T) = R(A) = R(B)` for some `T ⊆ P`, breaking primitivity of `(P ∪ A, Q ∪ B)` or similar.

**Gap 3: Non-smooth denominators.** BSRCC only addresses *y*-smooth *Q*. Erdős #319 allows arbitrary *Q* ⊆ [1, *N*]. Extending from smooth to general is a major additional challenge.

### E4. Summary of Gaps

| Component | Status | Difficulty |
|---|---|---|
| Elementary lemmas (A1-A6) | **Proved** | Easy |
| BSRCC for fixed *y*, fixed *N* | Computationally supported | Medium-Hard |
| BSRCC for fixed *y*, growing *N* | Conjectured, limited evidence | Hard |
| Large |Q| → low H₂ for *y*-smooth *Q* | Not addressed | Hard |
| Realization theorem for small targets | Partially addressed by Liu-Sawhney | Hard |
| Extension from smooth to general *Q* | Not addressed | Very Hard |
| Full Erdős #319 | Open problem | Very Hard |

---

## F. Critical Assessment of the Data

### F1. Bounded-Support Theorem vs. Slowly Growing C vs. Artifact

**Option 1: Bounded support (C depends only on y, δ).** The data is consistent: for *y* = 7, 11, 13, the threshold stabilizes at 7. But:
- The available *y*-smooth composites ≤ *N* are few (e.g., only ~20 for *y* = 7, *N* = 50).
- With *k* ≤ 12 and limited universe size, stabilization could reflect universe exhaustion.
- *Prediction test:* Compute with *y* = 7, *N* = 200 (about 50 candidates), *k* = 20. If support still stabilizes at 7, that's stronger evidence.

**Option 2: Slowly growing C(y, δ, |Q|).** This is harder to distinguish from Option 1 in small experiments. Growth like `C ~ log |Q|` or `C ~ log N` would look like stabilization for small *N*.

**Option 3: Finite-universe artifact.** If the universe has *m* elements, then any identity has support ≤ 2*m*, and if *m* is small, the "stabilization" is trivially bounded.
- For *y* = 7, *N* = 50: *m* ≈ 20. Support 7 out of max 40 is nontrivial.
- For *y* = 7, *N* = 50, *k* = 12: sets use 12/20 of the universe, so support 7 < 12 is meaningful.

**My assessment:** The data is *not* an obvious artifact, but the evidence is insufficient to distinguish Option 1 from Option 2. The key discriminating experiment is scaling *N* (and hence the universe) significantly while keeping *y* fixed.

### F2. The Support-7 Value

Is there a reason for 7 specifically? For *y* = 7, the prime set is {2, 3, 5, 7} (4 primes). The minimal support of a primitive reciprocal identity among *y*-smooth numbers might be related to 2·|{primes}| - 1 = 7 or similar. This is speculative but testable: check *y* = 5 (primes {2, 3, 5}, predict support ~5?) and *y* = 11 (primes {2, 3, 5, 7, 11}, predict support ~9?). The data shows support 7 for *y* = 11 and 13, which *doesn't* fit `2·π(y) - 1`. So this formula is wrong, or the true threshold hasn't been reached for larger *y* with the tested parameters.

---

## G. Proposed Note Outline (6–10 pages)

### Title
*Reciprocal Subset-Sum Entropy and the Rigidity of Primitive Egyptian Fraction Circuits*

### §1. Introduction (1 page)
- Erdős #319 and the growing-*Q* problem
- The 1 - 1/e barrier
- Our approach: entropy methods for the rigid side

### §2. Definitions and Elementary Facts (1.5 pages)
- Reciprocal sums, subset-sum image, collision probability, Rényi entropy
- Formal proofs of A1–A6 (reference Lean formalization)
- Clearing denominators and the integer-kernel viewpoint

### §3. Computational Evidence (2 pages)
- Exhaustive N=32 experiment
- y-smooth scaling experiments
- Identity family diagnostics
- Summary tables

### §4. The Bounded Smooth Reciprocal Circuit Conjecture (1 page)
- Precise statement
- Variants (fixed exponents, sublinear growth)
- Relation to Graver bases and primitive partition identities

### §5. Proof Approaches (2 pages)
- §5.1 Graver / toric ideal approach: strengths, limitations
- §5.2 *p*-adic layer peeling: the valuation argument
- §5.3 Anti-concentration / inverse Littlewood-Offord: analogy and gaps

### §6. Relation to Erdős #319 (1.5 pages)
- The three gaps: density → entropy, BSRCC, realization
- Liu-Sawhney realization theorem
- What a full proof would require

### §7. Questions and Further Experiments (1 page)
- Scaling tests for large *N*
- Fixed-exponent experiments
- Relation to Davenport constant

---

## H. Questions for Experts

### For Thomas Bloom (Egyptian fractions, Erdős problems)

1. Is the density → entropy step (large |Q| of smooth denominators forces low H₂) known or believable? Does your work on Erdős-Graham-type problems give any leverage here?
2. For a primitive circuit (P, Q) with |P| + |Q| > (1 - 1/e + ε)N, do you expect *Q* to have structured/smooth denominators, or could *Q* be essentially arbitrary?
3. Have you seen the phenomenon of "forbidding small identities restores injectivity" in other subset-sum contexts?

### For Mehtaab Sawhney (unit fraction representations, Liu-Sawhney theorem)

1. Does the Liu-Sawhney realization theorem apply to targets of the form R(A) where A is a small set of *y*-smooth integers? Specifically, if P ⊆ [1, N] has density > 1 - 1/e + ε, can you represent any rational of the form `Σ_{a ∈ A} 1/a` (|A| bounded, denominators *y*-smooth) as R(T) for some T ⊆ P?
2. What density threshold on P would be needed? Does it depend on the denominator of the target rational, or just on ε?
3. Would the bounded-support conjecture, if true, be useful as a black box for the growing-Q side of Erdős #319?

### For Alfred Geroldinger (zero-sum theory, Graver bases)

1. For the integer kernel of a weight vector w = (L/q₁, ..., L/qₙ) where the qᵢ are *y*-smooth, are there known bounds on the support of primitive {-1, 0, 1}-valued kernel elements that exploit the multiplicative structure?
2. Is this related to the Davenport constant in any precise sense? The group here is (ℤ, +) rather than a finite group, but the weights have multiplicative structure from the *y*-smooth factorizations.
3. Is the "conformal decomposition" of a {-1, 0, 1} kernel vector into smaller {-1, 0, 1} kernel vectors studied? In Graver-basis theory this is the decomposition into Graver elements, but what bounds exist for {-1, 0, 1} coefficients specifically?
4. For fixed prime set {p₁, ..., pₖ} and growing exponents, do primitive partition identities among numbers of the form `∏ pᵢ^{aᵢ}` have bounded support, or can they grow?

---

## I. Literature Keywords and References

### Primary Keywords
- **Graver basis**: The set of primitive elements of an integer kernel; support bounds via subdeterminant theory (Cook-Gerards-Schrijver-Tardos)
- **Toric ideal**: The ideal generated by binomials corresponding to kernel elements; its reduced Gröbner basis is related to Graver elements
- **Primitive partition identity**: A minimal equality `Σ aᵢ = Σ bⱼ` with no proper sub-equality; the {-1, 0, 1} coefficient case
- **Egyptian fraction identity**: An equality among sums of distinct unit fractions; our "reciprocal identity"
- **Subset-sum anti-concentration**: Bounds on `max_t P(Σ εᵢaᵢ = t)`; the Erdős-Littlewood-Offord problem
- **Inverse Littlewood-Offord**: Structural results when anti-concentration is poor (Tao-Vu, Nguyen-Vu)
- **Unit fraction reachability**: Representing rationals as subset sums of {1/n}; Croot, Liu-Sawhney

### Secondary Keywords
- **Davenport constant**: Maximum length of a zero-sum-free sequence in a finite abelian group
- **Rényi entropy**: H₂ = -log₂(Σ pᵢ²), the collision entropy
- **Smooth numbers**: Integers whose prime factors are all ≤ y
- **Multiplicative number theory**: Structure of smooth-number sequences
- **Integer programming**: Sensitivity analysis of integer kernels

### Key References to Investigate
- Cook, Gerards, Schrijver, Tardos (1986): Sensitivity theorems in integer programming
- Geroldinger, Halter-Koch (2006): Non-Unique Factorizations (for zero-sum theory)
- Tao, Vu (2009): Inverse Littlewood-Offord theorems
- Nguyen, Vu (2011): Optimal inverse Littlewood-Offord theorems
- Croot (2003): On unit fractions
- Liu, Sawhney (2024): Unit fraction representations
- Bloom (various): Egyptian fraction problems and Erdős conjectures
- De Loera, Hemmecke, Köppe (2013): Algebraic and Geometric Ideas in IP (for Graver bases)

---

## J. Formal Lean Artifacts

### Proved (in `Elementary.lean`)
All 11 lemmas compile without sorry:

1. `recipSum_empty` — R(∅) = 0
2. `recipSum_singleton` — R({q}) = 1/q
3. `recipSum_union_disjoint` — R(A ∪ B) = R(A) + R(B) for disjoint A, B
4. `subsetSumImage_card_le` — |Σ(Q)| ≤ 2^|Q|
5. `subsetSumImage_card_eq_iff` — |Σ(Q)| = 2^|Q| iff subset-sum map is injective
6. `exists_collision_of_not_injective` — non-injectivity yields a collision
7. `recipSum_sdiff_eq_of_eq` — R(A\B) = R(B\A) when R(A) = R(B)
8. `sdiff_nonempty_of_ne_and_eq` — A\B ≠ ∅ when A ≠ B and R(A) = R(B)
9. `collision_to_identity` — collision yields a disjoint reciprocal identity
10. `collisionCount_eq_sum_sq` — collision count = Σ_t mult(t)²
11. `clearing_denominators` — R(A) = R(B) iff integer-weighted sums agree

### Would Require External Number Theory (Not Formalized)
- BSRCC in any form
- Graver-basis support bounds for smooth weights
- Realization theorem (Liu-Sawhney type)
- Density → entropy implication
- Any form of inverse Littlewood-Offord for rational reciprocals

---

## K. Final Assessment

### What You Have
- A clean set of definitions and elementary lemmas, formally verified.
- Interesting computational evidence for a bounded-support phenomenon.
- A well-posed conjecture (BSRCC) with clear variants.

### What You Don't Have
- A proof of BSRCC for any y, even y = 2.
- Evidence at scales large enough to rule out slow growth of C.
- Any of the three bridges needed for Erdős #319.

### Recommendation
1. **Strengthen the computational evidence** by scaling *N* significantly (e.g., *N* = 500 for *y* = 7, giving ~100 candidates, *k* = 30).
2. **Attack BSRCC for y = 2 first.** The only 2-smooth composites are powers of 2: {4, 8, 16, ...}. Reciprocal identities among powers of 2 have very rigid structure (they correspond to binary representations). This could be a tractable warm-up case.
3. **Contact Geroldinger** about Graver-basis support bounds for multiplicatively structured weights.
4. **Contact Sawhney** about whether the realization theorem handles the specific targets arising from BSRCC.
5. **Write the note** as a question-posing paper rather than a results paper, clearly separating proved facts, computational observations, and conjectures.

### Honest Bottom Line
The computational evidence is suggestive but the path from BSRCC to Erdős #319 has at least three major gaps, each of which would be a substantial result on its own. The value of this work is primarily in:
(a) identifying a potentially useful decomposition of the problem,
(b) posing a precise, testable, and independently interesting conjecture (BSRCC), and
(c) providing a clean formal foundation for further work.

This is valuable as a research direction proposal, not as a proof strategy that is close to completion.
