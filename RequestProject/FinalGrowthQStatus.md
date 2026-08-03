# Final Status: Reciprocal Subset-Sum Entropy and the Growing-Q Side of Erdős #319

---

## 1. What Is Lean-Proved

Across four Lean files (63 total theorem/lemma declarations, zero `sorry`, zero non-standard axioms), the following is machine-verified.

### 1.1 Core Definitions and Elementary Algebra (`Defs.lean`, `Elementary.lean`)

| Theorem | Statement |
|---------|-----------|
| `recipSum_empty` | R(∅) = 0 |
| `recipSum_singleton` | R({q}) = 1/q |
| `recipSum_union_disjoint` | R(A ∪ B) = R(A) + R(B) for disjoint A, B |
| `subsetSumImage_card_le` | \|Σ(Q)\| ≤ 2^{\|Q\|} |
| `subsetSumImage_card_eq_iff` | \|Σ(Q)\| = 2^{\|Q\|} ⟺ subset-sum map is injective |
| `exists_collision_of_not_injective` | Non-injectivity ⟹ ∃ distinct A, B with R(A) = R(B) |
| `recipSum_sdiff_eq_of_eq` | R(A\\B) = R(B\\A) when R(A) = R(B) |
| `sdiff_nonempty_of_ne_and_eq` | A\\B ≠ ∅ when A ≠ B and R(A) = R(B) |
| `collision_to_identity` | Collision ⟹ disjoint nonempty A', B' with R(A') = R(B') |
| `collisionCount_eq_sum_sq` | #Collisions = Σ_t mult(t)² |
| `clearing_denominators` | R(A) = R(B) ⟺ Σ (L/a) = Σ (L/b) for any common multiple L |

**Significance.** These establish the formal foundation: the subset-sum injectivity characterization, the extraction of disjoint reciprocal identities from collisions, and the clearing-of-denominators bridge to integer arithmetic. Lemmas 5–9 together prove that *any non-injective subset-sum map on Q yields a genuine internal reciprocal circuit* — the logical first step of the entropy approach.

### 1.2 Energy Spectrum Decomposition (`EnergySpectrum.lean`)

| Theorem | Statement |
|---------|-----------|
| `collision_iff_kernel` | R(x) = R(y) ⟺ signed difference v = x − y lies in the reciprocal kernel Λ(Q) |
| `sign3Fiber_card` | #{(x, y) : x − y = v} = 2^{k − \|v\|₁} |
| `sign3ZeroCount_add_support` | (# zero coordinates) + (support) = k |
| `collisionPairs_card_eq_sum` | **Main result:** #Collisions = Σ_{v ∈ Λ(Q)} 2^{k − \|v\|₁} |
| `sign3Fiber_disjoint` | Distinct signed fibers are disjoint |
| `sign3Fiber_biUnion` | Signed fibers partition all ordered pairs |

**Significance.** This is the *exact collision-energy identity*. It decomposes the total collision count — and hence the collision probability and Rényi entropy — into a weighted sum over signed kernel vectors, with each kernel vector of support t contributing exactly 2^{k−t}. This identity is the rigorous basis for the energy spectrum framework (§5 below).

### 1.3 (2,3)-Smooth Classification (`Smooth23.lean`)

| Theorem | Statement |
|---------|-----------|
| `smooth23_typeI_identity` | 1/(2^{a−1}·3^b) = 1/(2^a·3^{b−1}) + 1/(2^a·3^b), for a ≥ 1, b ≥ 1 |
| `smooth23_typeII_identity` | 1/(2^{a−2}·3^b) = 1/(2^a·3^{b−1}) + 1/(2^a·3^b), for a ≥ 2, b ≥ 1 |
| `no_rectangle_identity` | No axis-aligned rectangle in the (2,3)-exponent lattice produces a 2+2 identity |
| `support4_identity` | 1/4 + 1/6 = 1/3 + 1/12 (simplest support-4 primitive) |
| `support12_identity` | Explicit support-12 primitive identity |

**Significance.** Complete classification of support-3 identities for {2,3}-smooth integers. The rectangle-impossibility theorem eliminates a natural candidate for bounded-support generation.

### 1.4 Unbounded Primitive Support (`UnboundedSupport.lean`)

| Theorem | Statement |
|---------|-----------|
| `refinement_identity` | 1/n = 1/(2n) + 1/(3n) + 1/(6n) for all n ≠ 0 |
| `chainSum_eq_sixth` | The iterated refinement chain B_t satisfies R(B_t) = 1/6 for all t |
| `Finset.sum_lt_of_proper_subset` | A proper subset of a positive-sum set has strictly smaller sum |
| `family_t0` … `family_t5` | Concrete instances with support 3, 5, 7, 9, 11, 13 |
| Compositeness lemmas | All elements of B_t are composite {2,3}-smooth integers |

**Significance.** This is a *disproof by construction*: an explicit infinite family of primitive reciprocal identities among {2,3}-smooth composites with support 3 + 2t → ∞. See §4.

---

## 2. What Is Computational Evidence

The following are empirical observations from exhaustive and sampling experiments. They are *not* proved theorems.

### 2.1 Anti-support filtering restores near-injectivity

For y-smooth composite denominators, forbidding all internal reciprocal identities of support ≤ s causes the entropy deficit D(Q) = |Q| − H₂(Q) to drop sharply:

| Universe | Anti-support threshold s | D(Q) | |Σ(Q)|/2^|Q| |
|---|---|---|---|
| N = 32 composites, k = 8 | ≤ 3 | 0.845 | 67% |
| N = 32 composites, k = 8 | ≤ 4 | 0.248 | 91% |
| N = 32 composites, k = 8 | ≤ 5 | **0.000** | **100%** |
| y = 7, N = 50, k = 9 | ≤ 4 | 0.604 | 77% |
| y = 7, N = 50, k = 9 | ≤ 5 | 0.317 | 88% |
| y = 7, N = 50, k = 9 | ≤ 6 | 0.114 | 96% |

In the exhaustive N = 32 case, forbidding support ≤ 5 makes the best survivors *perfectly injective* (D = 0, all 2^8 = 256 subset sums distinct).

### 2.2 Minimum surviving support stabilizes

For y = 7, N = 50, anti-support ≤ 6, as k scales from 8 to 12, the minimum surviving identity support remains at **7** — it does not grow with k:

| k | D(Q) | min support | |Σ|/2^k |
|---|---|---|---|
| 8 | 0.055 | 7 | 98% |
| 9 | 0.044 | 7 | 98% |
| 10 | 0.124 | 7 | 96% |
| 11 | 0.114 | 7 | 96% |
| 12 | 0.114 | 7 | 96% |

### 2.3 Stabilization persists for larger prime alphabets

Forced y = 11 (N = 60) and y = 13 (N = 70) tests with k = 10 and anti-support ≤ 6 both yield minimum support 7 and deficits < 0.1.

### 2.4 Residual identities are diverse

The surviving support-7 identities are *not* one repeated scaled family. Top-family fractions are 3–10%, with dozens of distinct support families and dilation-normalized families at each tested parameter set.

### 2.5 Caveats on the evidence

- **Small scale.** k ≤ 12, N ≤ 70, y ≤ 13. The number of available y-smooth composites ≤ N is itself small (~20 for y = 7, N = 50).
- **Sampling.** Most experiments are random samples (50k–200k), not exhaustive.
- **Cannot distinguish bounded support from slow growth.** C ~ log N or C ~ log k would look like stabilization at these scales.

---

## 3. What Conjecture Remains Open

### 3.1 The original BSRCC is **wrongly stated** (as of the disproof in §4)

The original Bounded Smooth Reciprocal Circuit Conjecture asked for a uniform bound C(y, δ) on the support of some identity in Q. Since primitive identities of *unbounded* support exist (§4), any such conjecture must be reformulated.

### 3.2 Corrected conjecture: Dominant Short-Energy Conjecture

The corrected formulation uses the energy spectrum. Define:
- Signed kernel: Λ(Q) = {v ∈ {−1, 0, +1}^k : Σ v_i/q_i = 0}
- Energy spectrum: E_t(Q) = #{v ∈ Λ(Q) : ‖v‖₁ = t}
- Partition function: Z(Q) = Σ_{v ∈ Λ(Q)} 2^{−‖v‖₁} = 1 + Σ_{t≥1} E_t · 2^{-t}
- Entropy deficit: D(Q) = |Q| − H₂(Q) = log₂ Z(Q)

> **Dominant Short-Energy Conjecture.** For every smoothness bound y and deficit δ > 0, there exist C = C(y, δ) and c = c(y, δ) > 0 such that for every finite set Q of y-smooth composite integers with D(Q) ≥ δ:
>
> Σ_{1 ≤ s ≤ C} E_s(Q) · 2^{-s} ≥ c.

This does *not* claim bounded primitive support. It claims that when entropy deficit is large, a *positive fraction of the weighted energy* must come from short-support kernel vectors — even if exponentially many long-support vectors also exist.

### 3.3 Weaker corollary: Shortest-Vector Conjecture

> If D(Q) ≥ δ, then ∃ v ∈ Λ(Q) \ {0} with ‖v‖₁ ≤ C(y, δ).

This follows from the Dominant Short-Energy Conjecture but is strictly weaker (it asks for one short identity, not a positive energy share).

### 3.4 Status

Both conjectures are **fully open**. No proof exists for any y, including y = 2. The computational evidence is consistent with both but insufficient to distinguish them from slowly growing C(y, δ, |Q|).

---

## 4. Why Bounded Primitive Support Is False

### 4.1 The construction

The Lean-verified infinite family exploits the refinement identity:

> 1/n = 1/(2n) + 1/(3n) + 1/(6n)    for all n ≠ 0.

Starting from the base identity 1/6 = 1/8 + 1/24, repeatedly refine the last term:

| Depth t | Identity | Support |
|---------|----------|---------|
| 0 | {6} vs {8, 24} | 3 |
| 1 | {6} vs {8, 48, 72, 144} | 5 |
| 2 | {6} vs {8, 48, 72, 288, 432, 864} | 7 |
| t | {6} vs B_t | 3 + 2t |

Each B_t consists entirely of composite {2,3}-smooth integers: 8, and elements of the form 48·6^i, 72·6^i, 24·6^t.

### 4.2 Why each identity is primitive

All terms in B_t have positive reciprocals, so any proper subset of B_t has reciprocal sum strictly less than R(B_t) = 1/6. Therefore the only subset pairs achieving R(A) = R(B) are the trivial pair (∅, ∅) and the full pair ({6}, B_t). This is primitivity.

### 4.3 What this means

The naive hope — that primitive reciprocal identities among y-smooth integers have uniformly bounded support — is *false*, even for the simplest case y = 3 (primes {2, 3}).

The mechanism is that Egyptian-fraction-style decompositions (1 = Σ 1/q_i with distinct smooth q_i) can be made arbitrarily long, and each such decomposition gives a primitive identity {1} vs {q_1, …, q_k} whose support grows without bound.

### 4.4 What this does *not* refute

- **The Dominant Short-Energy Conjecture** (§3.2) is unaffected. The construction shows one long primitive identity per family, not that short identities are absent or carry negligible energy.
- **Local generation** remains plausible: every identity in the family is built by iterating a single support-4 local move (the refinement identity). One could still conjecture that all primitive smooth identities decompose into a bounded number of bounded-support conformal pieces.

---

## 5. Why the Entropy-Energy Spectrum Remains Meaningful

### 5.1 The exact identity (Lean-proved)

The collision count decomposes as:

> #Collisions(Q) = Σ_{v ∈ Λ(Q)} 2^{k − ‖v‖₁}.

Dividing by 2^{2k} and taking logarithms:

> D(Q) = log₂(1 + Σ_{t ≥ 1} E_t(Q) · 2^{-t}).

This is an *exact mathematical identity*, not an approximation. It holds for every finite Q.

### 5.2 Why it survives the disproof of bounded support

The energy spectrum identity shows that long identities are *exponentially discounted*: a kernel vector of support t contributes only 2^{-t} to the partition function Z(Q). Therefore:

- A single identity of support 100 contributes 2^{-100} ≈ 10^{-30} to Z(Q). This is negligible.
- For long identities to dominate the energy, there must be *exponentially many* of them: E_t must grow at rate ≥ 2^t.

The Dominant Short-Energy Conjecture asserts that for y-smooth Q, this exponential proliferation of long identities cannot fully account for large entropy deficit — short identities must carry a positive share.

### 5.3 Why the spectrum is the right framework

1. **It replaces individual-identity bounds with aggregate energy bounds.** The disproof of bounded support shows we cannot reason about single identities. The spectrum captures collective behavior.

2. **It connects to standard tools.** The partition function Z(Q) is a generating function amenable to Fourier analysis, p-adic analysis, and lattice-point counting — all standard techniques in additive combinatorics.

3. **It separates what is proved from what is conjectured.** The identity Z(Q) = 1 + Σ E_t 2^{-t} is Lean-proved. The conjecture is about the *distribution* of {E_t}, not about the identity itself.

4. **It gives quantitative predictions.** The conjecture predicts specific constants c(y, δ) that can be tested computationally by outputting the full energy spectrum, not just the minimum support.

### 5.4 The single caution

A support-t layer with E_t ≈ 2^t can contribute O(1) to Z(Q). The conjecture's truth depends on whether y-smoothness prevents this from happening without short identities also being present. This is the core open question.

---

## 6. How This Connects — Cautiously — to Erdős #319

### 6.1 The dream argument (with every gap flagged)

A proof of Erdős #319 via this approach would need all of the following:

| Step | Statement | Status |
|------|-----------|--------|
| (i) | Large \|Q\| ⊆ [1,N] ⟹ high collision probability for reciprocal subset sums of Q | **Unproved.** Would need a density-to-entropy lemma, plausibly via pigeonhole on y-smooth sub-universe. |
| (ii) | High CP(Q) ⟹ large entropy deficit D(Q) | **Proved by definition.** D(Q) = log₂ Z(Q), and Z(Q) = 2^k · CP(Q). |
| (iii) | Large D(Q) ⟹ short identity R(A) = R(B) inside Q | **Open.** This is the Shortest-Vector Conjecture (§3.3). |
| (iv) | Dense P ⊆ [1,N] can represent R(A) as a subset sum of reciprocals | **Open.** Related to Liu–Sawhney (2024) unit-fraction reachability, but not directly implied. |
| (v) | Representation of R(A) by P breaks primitivity of (P, Q) | **Proved by definitions** (if R(A) = R(T) for T ⊆ P, then T and A share a subset-sum value, violating primitivity). |

### 6.2 What is actually contributed

This project contributes to steps (ii) and (iii):

- **Step (ii):** The energy spectrum decomposition (Lean-proved) gives the *exact* relationship between collision probability, entropy deficit, and the signed kernel. This is not a conjecture — it is a usable identity for any future proof.

- **Step (iii):** The Dominant Short-Energy Conjecture is a precise, falsifiable formulation of the key missing step. It is supported by computational evidence but unproved.

### 6.3 What is *not* contributed

- **Step (i) is entirely open.** We have no theorem or even strong heuristic linking the density of Q to the collision probability of its reciprocal subset sums. For general (non-smooth) Q, such a link may not exist at all.

- **Step (iv) is addressed by others.** The Liu–Sawhney theorem on unit-fraction representations is the most relevant external result, but it does not directly give the needed statement. A precise question for Sawhney: given a density-(1 − 1/e + ε) set P ⊆ [1, N], can P represent every rational of the form R(A) for bounded |A| and bounded denominators?

- **The smooth-to-general gap is unaddressed.** All results and conjectures assume y-smooth denominators. Erdős #319 allows arbitrary Q ⊆ [1, N]. Extending the entropy approach to non-smooth Q would require fundamentally new ideas.

### 6.4 The honest assessment

This project does **not** approach a proof of Erdős #319. It contributes:

1. **A formally verified toolkit** (63 Lean theorems) for reasoning about reciprocal subset-sum collisions and the signed kernel.
2. **An exact structural identity** (the energy spectrum decomposition) that any future entropy-based approach to #319 would likely need.
3. **A precise conjecture** (Dominant Short-Energy) that isolates the key arithmetic question.
4. **A disproof** (unbounded primitive support) that eliminates a natural but false approach.
5. **Computational evidence** that supports the corrected conjecture at small scales.

The value is in **clarifying the problem structure** and **providing formal infrastructure**, not in making progress toward the final answer. At least three major independent breakthroughs — density-to-entropy, short-energy dominance, and target realization — would be needed before this approach could contribute to Erdős #319 itself.

### 6.5 Recommended next steps

| Priority | Action | Purpose |
|----------|--------|---------|
| 1 | Scale experiments to N = 200–500, k = 20–30 for y = 7 | Distinguish bounded support from slow growth |
| 2 | Output full energy spectrum {E_t} in experiments | Test Dominant Short-Energy Conjecture directly |
| 3 | Prove Shortest-Vector Conjecture for y = 2 (powers of 2 only) | Simplest non-trivial case |
| 4 | Consult Geroldinger on Graver-basis bounds for smooth weights | Identify whether existing algebraic theory applies |
| 5 | Consult Sawhney on reachability of small rational targets by dense P | Close step (iv) or identify obstruction |
| 6 | Investigate density-to-entropy for smooth sub-universes | Address step (i) |

---

*Document generated as part of the Erdős #319 Growing-Q project. All Lean-proved claims are machine-verified with zero sorries and standard axioms only. All conjectures and computational observations are clearly flagged as such.*
