# y=3 Restricted Energy Architecture: Attackable Theorem Variants

**Last updated:** 2026-06-08

**Status:** Planning document. No proofs attempted for these variants yet.

---

## 0. Context

The full energy dominance theorem for y=3 states:

> For every δ > 0, there exist C and c > 0 such that for every finite set Q
> of positive {2,3}-smooth integers with totalWeightedEnergy(Q) ≥ δ,
> we have shortWeightedEnergy(Q, C) ≥ c.

This is too strong to attack directly. Below we identify three weaker variants
ordered by increasing difficulty, each of which captures a meaningful fragment
of the conjecture. For each, we state what classification results would be needed.

---

## 1. Variant A: Shortest-Vector Version (weakest)

### Statement

> For every δ > 0, there exists C = C(δ) such that for every finite set Q
> of positive {2,3}-smooth integers:
> if totalWeightedEnergy(Q) ≥ δ, then Q contains a nonzero kernel vector
> of support ≤ C.

```lean
theorem shortest_vector_y3_weak (δ : ℚ) (hδ : 0 < δ) :
    ∃ C : ℕ,
    ∀ k : ℕ, ∀ q : Fin k → ℕ,
      (∀ i, q i ≠ 0) →
      (∀ i, isSmooth 3 (q i)) →
      totalWeightedEnergy k q ≥ δ →
      ∃ s, s ≤ C ∧ 0 < energyAtSupport k q s := by sorry
```

### What classification results are needed

1. **Support-3 completeness** — ✅ DONE. The three families (Type I, II, III)
   are fully classified.

2. **Support-4 completeness** — 🔗 REDUCED. The 28-core catalogue is
   conjecturally complete; an effective S-unit bound would close this.

3. **Conformal decomposition**: Every kernel vector decomposes into
   primitive components. If we knew that every primitive {2,3}-smooth
   identity has support ≤ C₀ (FALSE by UnboundedSupport.lean!), this
   would follow trivially. Since primitive support is unbounded, we need
   a different argument.

4. **The key missing step**: Show that if totalWeightedEnergy ≥ δ, then
   among the (possibly exponentially many) kernel vectors, at least one
   has short support. This requires showing that the long-support kernel
   vectors cannot "conspire" to produce macroscopic energy without any
   short vector being present.

### Proof sketch (if support-4 completeness is available)

**Attempt via Pigeonhole on the 2-adic valuation layer.**

For {2,3}-smooth Q with k elements, consider the element q* with the
maximal 2-adic valuation v₂(q*). In any kernel vector v with v(q*) ≠ 0,
at least one other element q' with the same v₂ value must also have
v(q') ≠ 0 (to cancel the leading 2-adic term). If Q has many elements
at the same 2-adic level, pairs at that level may force support-3 identities.

**Obstruction**: Elements at the same 2-adic level may differ in their
3-adic valuation, preventing a support-3 identity. The argument would need
to cascade through 3-adic layers as well.

### Assessment

This is the most attackable variant. The core difficulty is purely
combinatorial: showing that {2,3}-smooth structure forces short kernel
vectors when energy is positive. A successful proof would likely proceed
by induction on the number of distinct valuation levels.

**Difficulty: Medium-Hard.**

---

## 2. Variant B: Tail-Decay Version (intermediate)

### Statement

> For every ε > 0, there exists C = C(ε) such that for every finite set Q
> of positive {2,3}-smooth integers:
>
> Σ_{s > C} E_s(Q) · 2^{-s} ≤ ε · totalWeightedEnergy(Q).

In words: the tail of the energy spectrum (beyond support C) carries at
most an ε-fraction of the total energy.

```lean
theorem tail_decay_y3 (ε : ℚ) (hε : 0 < ε) :
    ∃ C : ℕ,
    ∀ k : ℕ, ∀ q : Fin k → ℕ,
      (∀ i, q i ≠ 0) →
      (∀ i, isSmooth 3 (q i)) →
      totalWeightedEnergy k q -
        shortWeightedEnergy k q C ≤
      ε * totalWeightedEnergy k q := by sorry
```

### What classification results are needed

Everything from Variant A, plus:

5. **Kernel vector counting at each support level**: For fixed coprime core
   family F of support s, bound the number of instantiations of F in Q.
   If Q has k elements and F uses elements at t distinct valuation levels,
   then the instantiation count is at most O(k^t).

6. **Summability of the tail**: Show Σ_{s > C} (# families at support s) ·
   (max instantiation count) · 2^{-s} converges and can be made < ε
   by choosing C large enough.

### Proof sketch (speculative)

By Evertse's theorem, the number of coprime cores at support s is bounded
by some f(s, π(y)) = f(s, 2) for y=3. The Evertse bound is roughly
(2^{35(s+1)})^{s²}, which is enormous but finite for each s.

For each core, the number of instantiations in Q depends on how many
scaling factors g produce valid subsets of Q. Since g must be {2,3}-smooth
and g·a_i ∈ Q for all coordinates i of the core, the count is at most
|Q| (choose the largest scaled entry, which determines g).

So the tail energy is at most:

  Σ_{s > C} f(s,2) · k · 2^{-s}

For this to converge to something < ε · totalWeightedEnergy, we need
f(s,2) to grow sub-exponentially in s (specifically, slower than 2^s).

**Obstruction**: The Evertse bound is super-exponential in s. A tighter
bound specific to {2,3}-smooth structure is needed.

### What support-4/5 classification provides

If the support-4 catalogue is complete (28 cores), and if a support-5
classification yields M₅ cores, then we have explicit constants for the
first two terms of the tail. The tail energy from support 3 and 4 is:

  3 · k · 2^{-3} + 28 · k · 2^{-4} = (3/8 + 28/16) · k = (3/8 + 7/4) · k = 17k/8

This grows linearly in k, which is fine since totalWeightedEnergy also
grows with k when energy is positive. The key question is whether the
support-s core count grows sub-exponentially.

### Assessment

This is harder than Variant A because it requires quantitative control
over the energy tail, not just existence of one short vector. The
Evertse bounds are too loose for a direct approach. A proof would likely
require exploiting the specific structure of {2,3}-smooth identities
(the "exponent lattice" viewpoint) rather than generic S-unit theory.

**Difficulty: Hard.**

---

## 3. Variant C: Local-Generation Version (strongest short of full conjecture)

### Statement

> Every nonzero kernel vector among {2,3}-smooth denominators can be
> decomposed as a conformal sum of "local moves," each of support ≤ C₀,
> where C₀ is an absolute constant (independent of Q and k).

```lean
theorem local_generation_y3 :
    ∃ C₀ : ℕ,
    ∀ k : ℕ, ∀ q : Fin k → ℕ,
      (∀ i, q i ≠ 0) →
      (∀ i, isSmooth 3 (q i)) →
      ∀ v : Fin k → Sign3,
        signedRecipSum k q v = 0 →
        v ≠ zeroVec k →
        ∃ (n : ℕ) (ws : Fin n → (Fin k → Sign3)),
          (∀ j, signedRecipSum k q (ws j) = 0) ∧
          (∀ j, sign3Support k (ws j) ≤ C₀) ∧
          -- ws conformally compose to v
          True := by sorry
```

### What classification results are needed

Everything from Variants A and B, plus:

7. **Primitive identity support bound (conformal sense)**: Every primitive
   {-1,0,+1} kernel vector among {2,3}-smooth denominators has support ≤ C₀.
   This is FALSE for the standard notion of primitivity (by UnboundedSupport.lean).
   However, it might be true for a relaxed notion: perhaps every primitive
   vector can be *conformally approximated* by vectors of bounded support.

8. **Conformal decomposition algorithm**: An explicit procedure that, given
   a long kernel vector, extracts a short conformal component.

### Connection to the refinement identity

The unbounded-support family from `UnboundedSupport.lean` is built by
iterating the support-4 refinement identity `1/n = 1/(2n) + 1/(3n) + 1/(6n)`.
Each iteration is a local move of support 4 (replacing one entry by three).
So this family is locally generated with C₀ = 4.

**Key question**: Is every {2,3}-smooth primitive identity locally generated
by support-3 and support-4 moves? If yes, C₀ = 4 suffices.

### What support-4 classification provides

If the support-4 catalogue is complete, then the set of "local moves" is
explicitly known: the 3 support-3 families + 25 support-4 families + their
scalings. The local-generation conjecture then asks: does the group generated
by these moves (in the conformal/sign-preserving sense) exhaust all kernel
vectors?

### Assessment

This is the strongest variant and would imply both A and B. It is also the
most speculative. The evidence from the refinement family is suggestive but
a proof would require deep structural analysis of the {2,3}-smooth
exponent lattice.

**Difficulty: Very Hard.**

---

## 4. Recommended Next Attack

### Target: Variant A (Shortest-Vector) for y=3 with explicit C

Start with the following concrete sub-problem:

> **Sub-problem**: Prove that every finite set Q of positive {2,3}-smooth
> integers with at least one collision (totalWeightedEnergy > 0) contains
> a kernel vector of support ≤ 7.

This is supported by all computational evidence (the minimum surviving support
after anti-support-≤6 filtering is always 7 for y ∈ {7, 11, 13}).

### Decomposition into sub-lemmas

**Lemma 1** (2-adic layer): If v is a kernel vector and q* has maximal v₂(q*)
among {i : v(i) ≠ 0}, then at least one other element q' with v₂(q') = v₂(q*)
also has v(q') ≠ 0.

**Lemma 2** (3-adic layer): Similarly for v₃.

**Lemma 3** (layer interaction): If the 2-adic and 3-adic extremal elements
are distinct, the identity involves at least 4 elements at two valuation levels.

**Lemma 4** (short identity extraction): Given a kernel vector with identified
extremal elements, extract a sub-identity of bounded support using the
support-3 and support-4 classification.

### What this needs from the catalogue

- Support-3 completeness: ✅ available
- Support-4 completeness: 🔗 needed (or at minimum, the catalogue must
  cover all cores that appear in the layer-peeling argument)
- Support-5 classification: probably not needed for this sub-problem

---

## 5. Summary Table

| Variant | Strength | Difficulty | Classification needed | Status |
|---------|----------|------------|----------------------|--------|
| A. Shortest-Vector | Weakest | Medium-Hard | Support-3 ✅, Support-4 🔗 | Next target |
| B. Tail-Decay | Intermediate | Hard | Support-3 ✅, Support-4 🔗, counting bounds ❌ | Future |
| C. Local-Generation | Strongest | Very Hard | Full conformal decomposition ❌ | Speculative |
