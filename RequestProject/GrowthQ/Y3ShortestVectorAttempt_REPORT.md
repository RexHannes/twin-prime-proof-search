# Y=3 Shortest Vector Attempt: Report

**Date:** 2026-06-08  
**File:** `RequestProject/Y3ShortestVectorAttempt.lean`

---

## Stage 1: p-adic Extremal Layer Lemmas — ✅ COMPLETE

All 10 theorems proved, compiled without `sorry`, no custom axioms, no `native_decide`.

### Theorems proved

#### Generic signed-integer-sum lemmas

| Theorem | Statement | Status |
|---------|-----------|--------|
| `two_adic_extremal_unique` | If exactly one support element has odd weight, the kernel equation `∑ zᵢ wᵢ = 0` with `zᵢ ∈ {-1,0,1}` has no solution. | ✅ Proved |
| `even_card_oddWtSupp` | The number of odd-weight support elements is even. | ✅ Proved |
| `two_le_card_oddWtSupp` | If there are any odd-weight support elements, there are ≥ 2. | ✅ Proved |
| `three_adic_extremal_unique` | If exactly one support element has weight coprime to 3, the kernel equation has no solution. | ✅ Proved |
| `two_le_card_coprime3WtSupp` | If there are any coprime-to-3-weight support elements, there are ≥ 2. | ✅ Proved |

#### {2,3}-smooth weight structure lemmas

| Theorem | Statement | Status |
|---------|-----------|--------|
| `smooth23_weight_form` | `2^A · 3^B / (2^a · 3^b) = 2^{A-a} · 3^{B-b}` | ✅ Proved |
| `maximal_v2_gives_odd_weight` | `2^0 · 3^{B-b}` is odd | ✅ Proved |
| `maximal_v3_gives_coprime3_weight` | `2^{A-a} · 3^0` is coprime to 3 | ✅ Proved |

#### Main {2,3}-smooth corollaries

| Theorem | Statement | Status |
|---------|-----------|--------|
| `smooth23_two_adic_extremal` | In a nonzero kernel vector among {2,3}-smooth weights, ≥ 2 support elements share the maximal `v₂` value. | ✅ Proved |
| `smooth23_three_adic_extremal` | In a nonzero kernel vector among {2,3}-smooth weights, ≥ 2 support elements share the maximal `v₃` value. | ✅ Proved |

### Mathematical content

The core argument is modular arithmetic:

1. **2-adic**: After clearing denominators, the weight `wᵢ = 2^{A-aᵢ} · 3^{B-bᵢ}`. Elements with `aᵢ = A` (maximal `v₂`) have odd weight. Modulo 2, the sum of sign × weight is just the count of odd-weight support elements mod 2. For the sum to vanish, this count must be even, hence ≥ 2.

2. **3-adic**: Elements with `bᵢ = B` (maximal `v₃`) have weight coprime to 3. Modulo 3, a single nonzero `z_j · w_j` with `gcd(w_j, 3) = 1` cannot vanish, so there must be ≥ 2 such elements.

---

## Stage 2: Restricted Short-Vector Extraction — ❌ NOT ATTEMPTED

### Why Stage 2 was not attempted

The restricted short-vector extraction theorem requires substantial case analysis that goes beyond what the Stage 1 lemmas provide. Here is the gap:

#### What Stage 1 gives us

Given a kernel vector `z` among {2,3}-smooth weights:
- At least 2 support elements at the maximal `v₂` level
- At least 2 support elements at the maximal `v₃` level

#### What Stage 2 would need

To extract a short kernel vector (support ≤ 7), we would need:

1. **Layer-peeling iteration**: After identifying the extremal layer pair, "peel" them off to get a reduced equation. Repeat until the kernel vector is exhausted or a short sub-vector is found. This requires formalizing:
   - The reduced equation after peeling one layer
   - That peeling reduces the `v₂` or `v₃` range by ≥ 1
   - Termination after at most `A + B` steps (bounded by the exponent range)

2. **Interaction between layers**: If the 2-adic and 3-adic extremal pairs overlap (share elements), this immediately constrains the identity. If they don't overlap, we have ≥ 4 elements in the support, and their exponent structure is constrained. Making this precise requires:
   - Case analysis on overlap patterns
   - For each pattern, showing that either a support-3 or support-4 sub-identity exists, or the vector can be further reduced

3. **Connection to the support-3/4 classification**: The layer-peeling argument ultimately needs to bottom out in one of the known identity families (Type I, II, III for support 3; the 28-core catalogue for support 4). This requires:
   - Formalizing which coprime core each layer configuration produces
   - Checking that each configuration actually matches a classified identity
   - For support-4: the catalogue completeness is still **conjectural** (not proved)

#### Exact failed theorem signature (hypothetical)

```lean
theorem restricted_short_vector_extraction {k : ℕ} {z : Fin k → ℤ} {w : Fin k → ℕ}
    {a b : Fin k → ℕ} {A B : ℕ}
    (hsign : IsSignVec z)
    (hker : signedWtSum z w = 0)
    (hsupp_ne : (signSupp z).Nonempty)
    (hw : ∀ i, w i = 2 ^ (A - a i) * 3 ^ (B - b i))
    (hA : ∀ i, a i ≤ A) (hB : ∀ i, b i ≤ B)
    -- Extremal layer size constraint (simple configuration)
    (h2_layer : ((signSupp z).filter (fun i => a i = A)).card = 2)
    (h3_layer : ((signSupp z).filter (fun i => b i = B)).card = 2) :
    ∃ z' : Fin k → ℤ, IsSignVec z' ∧ signedWtSum z' w = 0 ∧
      (signSupp z').Nonempty ∧ (signSupp z').card ≤ 7 := by sorry
```

This was NOT attempted because:
- The layer-peeling induction structure is non-trivial to formalize
- It depends on support-4 catalogue completeness (which is conjectural)
- A single restricted case (both layers size exactly 2) would already require ~200+ lines of case analysis

#### The issue is mathematical, not Lean-formalization

The core difficulty is mathematical: showing that layer peeling terminates with a short vector requires either:
- A complete classification of all possible layer configurations (infeasible without support-4 completeness)
- An inductive argument showing that each peeling step produces a strictly smaller problem that must eventually bottom out

The Lean formalization challenges (defining layer peeling, managing indices) are secondary to this mathematical gap.

### What computational data would help

1. **Exhaustive layer-pattern survey**: For all kernel vectors among {2,3}-smooth integers up to some bound N, tabulate the extremal layer sizes and overlap patterns. This would reveal whether the "both layers size 2" case is the most common, and whether other patterns require larger support.

2. **Layer-peeling trace**: For each long kernel vector, trace the layer-peeling process step by step, recording:
   - Which layer is peeled at each step
   - The resulting reduced equation
   - Whether a short sub-vector is encountered

3. **Counter-example search**: Attempt to find a kernel vector among {2,3}-smooth integers with no sub-vector of support ≤ 7. If none exists up to large N, this strengthens the conjecture.

---

## Summary

| Stage | Status | Theorems proved |
|-------|--------|-----------------|
| Stage 1: p-adic extremal layer | ✅ Complete | 10/10 |
| Stage 2: Restricted short-vector extraction | ❌ Not attempted | 0 (gap is mathematical, not formalization) |

The Stage 1 lemmas are a solid foundation. They establish the necessary constraints on extremal p-adic layers that any future layer-peeling argument would build upon. The gap to Stage 2 is substantial and primarily mathematical.
