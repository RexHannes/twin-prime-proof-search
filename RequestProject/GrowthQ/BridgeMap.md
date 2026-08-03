# Bridge Map: Theorem Dependencies from Growth-Q Formalization to Main Conjecture

**Last updated:** 2026-06-08

---

## Overview

This document traces the exact theorem dependencies from the current Growth-Q
formal module to a possible proof of the **Dominant Short-Energy Conjecture**
(the corrected target after the disproof of bounded primitive support).

Each item is marked with one of:
- ✅ **Proved** — zero sorry, standard axioms, machine-verified
- 📊 **Computational evidence** — tested but not proved
- 🔗 **Reduced but not proved** — formally stated, reduces to a known-type problem
- 🔮 **Conjectural** — plausible but no reduction to known results
- ❌ **Missing** — not even formally stated; needed for the chain

---

## A. Foundation Layer (all ✅ Proved)

### A1. Reciprocal sum algebra
| Item | Status | File | Theorem |
|------|--------|------|---------|
| R(∅) = 0 | ✅ | `Elementary.lean` | `recipSum_empty` |
| R({q}) = 1/q | ✅ | `Elementary.lean` | `recipSum_singleton` |
| R(A ∪ B) = R(A) + R(B) for disjoint A,B | ✅ | `Elementary.lean` | `recipSum_union_disjoint` |

### A2. Collision-to-identity extraction
| Item | Status | File | Theorem |
|------|--------|------|---------|
| \|Σ(Q)\| ≤ 2^{\|Q\|} | ✅ | `Elementary.lean` | `subsetSumImage_card_le` |
| \|Σ(Q)\| = 2^{\|Q\|} ↔ injective | ✅ | `Elementary.lean` | `subsetSumImage_card_eq_iff` |
| Non-injective → distinct A,B with R(A)=R(B) | ✅ | `Elementary.lean` | `exists_collision_of_not_injective` |
| R(A)=R(B) → R(A\B)=R(B\A) | ✅ | `Elementary.lean` | `recipSum_sdiff_eq_of_eq` |
| A≠B, R(A)=R(B) → A\B nonempty | ✅ | `Elementary.lean` | `sdiff_nonempty_of_ne_and_eq` |
| Collision → disjoint reciprocal identity | ✅ | `Elementary.lean` | `collision_to_identity` |
| Collision count = Σ mult(t)² | ✅ | `Elementary.lean` | `collisionCount_eq_sum_sq` |
| Clearing denominators | ✅ | `Elementary.lean` | `clearing_denominators` |

### A3. Energy spectrum decomposition
| Item | Status | File | Theorem |
|------|--------|------|---------|
| Collision ↔ signed kernel vector | ✅ | `EnergySpectrum.lean` | `collision_iff_kernel` |
| Fiber cardinality = 2^(zero count) | ✅ | `EnergySpectrum.lean` | `sign3Fiber_card` |
| #Collisions = Σ_{v∈Λ} 2^{k-\|v\|₁} | ✅ | `EnergySpectrum.lean` | `collisionPairs_card_eq_sum` |
| #Collisions = 2^k + Σ E_s · 2^{k-s} | ✅ | `EnergySpectrumExact.lean` | `collisionPairs_card_eq_diagonal_add_energy` |
| CP = Z(Q)/2^k | ✅ | `CollisionProbability.lean` | `collisionProbability_eq` |
| Z(Q) ≥ 1 | ✅ | `CollisionProbability.lean` | `one_le_deficitProxy` |

### A4. Kernel vector algebra
| Item | Status | File | Theorem |
|------|--------|------|---------|
| Disjoint-support kernel addition | ✅ | `InverseLemma.lean` | `kernel_add_disjoint` |
| Kernel closed under negation | ✅ | `InverseLemma.lean` | `kernel_neg` |

---

## B. Classification Layer (y=3 case)

### B1. Support-3 completeness
| Item | Status | File | Theorem |
|------|--------|------|---------|
| Type I identity family | ✅ | `Smooth23.lean` | `smooth23_typeI_identity` |
| Type II identity family | ✅ | `Smooth23.lean` | `smooth23_typeII_identity` |
| Type III identity family | ✅ | `Smooth23.lean` | `smooth23_typeIII_identity` |
| No rectangle identity | ✅ | `Smooth23.lean` | `no_rectangle_identity` |
| Catalan bound: 3^b+1=2^a | ✅ | `Smooth23Completeness.lean` | `no_pow3_add_one_eq_pow2_of_ge_two` |
| Catalan bound: 2^a+1=3^b | ✅ | `Smooth23Completeness.lean` | `no_pow2_add_one_eq_pow3_of_ge_four` |
| Consecutive smooth pairs = {1,2,3,8} | ✅ | `Smooth23Completeness.lean` | `consecutive_smooth23_pairs` |
| Coprime smooth sum forces x=1 or y=1 | ✅ | `Smooth23Completeness.lean` | `coprime_smooth23_sum_has_one` |
| **Complete classification** | ✅ | `Smooth23Completeness.lean` | `support3_completeness_of_smooth23` |

### B2. Support-4 catalogue
| Item | Status | File | Theorem |
|------|--------|------|---------|
| 25 non-degenerate cores verified | ✅ | `Support4.lean` | `support4_core1`…`support4_core25` |
| 3 degenerate cores verified | ✅ | `Support4.lean` | `support4_degenerate1`…`support4_degenerate3` |
| Scaling preserves identities | ✅ | `Support4.lean` | `support4_scaling` |
| Denominator clearing for support-4 | ✅ | `Support4.lean` | `support4_clearing` |
| Integer core → reciprocal identity | ✅ | `Support4.lean` | `intCore_to_recip_identity` |
| Primitivity for cores 1, 5, 6, 7 | ✅ | `Support4.lean` | `support4_core{1,5,6,7}_primitive` |
| Catalogue stable to 10⁶ | 📊 | `Support4.lean` | (documented, not formalized) |
| S-unit finiteness (Evertse) | 🔗 | `Support4.lean` | `smooth23_four_term_sunit_finite` (sorry) |
| Support-4 completeness | 🔗 | `Support4.lean` | `support4_completeness_of_smooth23` (sorry) |

### B3. Unbounded primitive support (disproof)
| Item | Status | File | Theorem |
|------|--------|------|---------|
| Refinement identity 1/n = 1/(2n)+1/(3n)+1/(6n) | ✅ | `UnboundedSupport.lean` | `refinement_identity` |
| Chain sum = 1/6 for all t | ✅ | `UnboundedSupport.lean` | `chainSum_eq_sixth` |
| \|B_t\| = 2+2t | ✅ | `UnboundedSupport.lean` | `Bt_card_eq` |
| Primitive support → ∞ | ✅ | `UnboundedSupport.lean` | `support_unbounded_with_identity` |

---

## C. Energy Dominance Layer (the core conjecture)

### C1. Support-3 energy contribution
| Item | Status | File | Theorem |
|------|--------|------|---------|
| Support-3 vector → energy ≥ 1/8 | ✅ | `EnergyDominanceY3.lean` | `support3_energy_pos` |
| Support-3 vector → positive short energy | ✅ | `EnergyDominanceY3.lean` | `shortEnergy_pos_of_support3` |
| Type I identity creates support-3 energy | ✅ | `EnergyDominanceY3.lean` | `typeI_creates_support3_energy` |

### C2. Full energy dominance (y=3)
| Item | Status | File |
|------|--------|------|
| Energy dominance for y=3 | 🔮 | `EnergyDominanceY3.lean` — `energy_dominance_y3` (sorry) |
| Shortest-vector for y=3 | 🔮 | `EnergyDominanceY3.lean` — `shortest_vector_y3` (sorry) |

### C3. Full energy dominance (general y)
| Item | Status | File |
|------|--------|------|
| Dominant Short-Energy Conjecture | 🔮 | `DominantShortEnergy.lean` — `dominantShortEnergy_conjecture` (sorry) |
| Shortest-Vector Conjecture | 🔮 | `DominantShortEnergy.lean` — `shortestVector_conjecture` (sorry) |

---

## D. Missing Bridges

These are the theorems that do **not** yet exist in any form in the project,
but would be needed for a proof of the energy dominance conjecture or for
connecting to Erdős #319. Each is given a Lean-style signature.

### D1. Support-4 completeness (effective bound)

**Status:** ❌ Missing

The S-unit finiteness statement exists (`smooth23_four_term_sunit_finite`)
but uses `sorry`. A proof requires an effective upper bound on entries.

```lean
/-- Baker/de Weger effective bound: every coprime {2,3}-smooth solution to
    a + b = c + d has max(a,b,c,d) ≤ B for an explicit constant B. -/
theorem smooth23_sunit_effective_bound :
    ∃ B : ℕ, ∀ a b c d : ℕ,
      0 < a → 0 < b → 0 < c → 0 < d →
      isSmooth 3 a → isSmooth 3 b → isSmooth 3 c → isSmooth 3 d →
      a + b = c + d →
      Nat.gcd (Nat.gcd (Nat.gcd a b) c) d = 1 →
      max (max a b) (max c d) ≤ B := by sorry
```

### D2. Support-s classification for general s (y=3)

**Status:** ❌ Missing

For the energy dominance proof, we need to know that the number of
coprime support-s identity cores is bounded (for each fixed s).

```lean
/-- For each support level s, the number of coprime cores of
    support-s {2,3}-smooth reciprocal identities is finite. -/
theorem smooth23_support_s_finite (s : ℕ) :
    ∃ N : ℕ, ∀ (core : Fin s → ℕ),
      (∀ i, 0 < core i) →
      (∀ i, isSmooth 3 (core i)) →
      (∃ (σ : Fin s → Sign3),
        (∀ i, σ i ≠ Sign3.zero) ∧
        ∑ i, (σ i).toRat / (core i : ℚ) = 0 ∧
        Nat.gcd (Finset.univ.val.map (fun i => core i)).head! 1 = 1) →
      (Finset.univ.val.map (fun i => core i)).maximum ≤ N := by sorry
```

### D3. Kernel vector count bound at support s

**Status:** ❌ Missing

For energy dominance, we need that E_s(Q) cannot grow exponentially in s
without also having positive E_t for some t ≤ C.

```lean
/-- Key energy concentration lemma: if Q is y-smooth and has no nonzero
    kernel vector of support ≤ C, then E_s(Q) ≤ f(y,s) · (something sub-exponential). -/
theorem kernel_count_bound_no_short (y C s k : ℕ) (q : Fin k → ℕ)
    (hq : ∀ i, q i ≠ 0) (hs : ∀ i, isSmooth y (q i))
    (hno_short : ∀ t, t ≤ C → energyAtSupport k q t = 0) :
    energyAtSupport k q s ≤ sorry := by sorry
```

### D4. Conformal decomposition of kernel vectors

**Status:** ❌ Missing

Every kernel vector in {−1,0,1}^k decomposes conformally into primitive
ones. For smooth denominators, we need to show primitive components have
bounded support (in some averaged/energy sense).

```lean
/-- Every nonzero kernel vector decomposes as a conformal sum of
    primitive (Graver basis) elements. -/
theorem conformal_decomposition (k : ℕ) (q : Fin k → ℕ) (hq : ∀ i, q i ≠ 0)
    (v : Fin k → Sign3) (hv : signedRecipSum k q v = 0) (hv_nz : v ≠ zeroVec k) :
    ∃ (n : ℕ) (ws : Fin n → (Fin k → Sign3)),
      (∀ j, signedRecipSum k q (ws j) = 0) ∧
      (∀ j, ∀ i, ws j i ≠ Sign3.zero → ws j i = v i) ∧
      -- reconstruction: v = Σ ws (in sign3 sense, respecting conformal constraint)
      True := by sorry
```

### D5. Density-to-entropy (connecting to Erdős #319)

**Status:** ❌ Missing

This is the bridge from Erdős #319 density assumptions to the energy framework.

```lean
/-- If Q ⊆ [1,N] has |Q| ≥ (1 - 1/e + ε)N, then Q contains a y-smooth
    subset Q' with macroscopic entropy deficit. -/
theorem density_implies_deficit (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ y : ℕ,
    ∀ N : ℕ, ∀ Q : Finset ℕ,
      (∀ q ∈ Q, q ≤ N) →
      Q.card ≥ ⌈((1 - 1 / Real.exp 1 + ε) * N)⌉₊ →
      ∃ Q' : Finset ℕ,
        Q' ⊆ Q ∧
        (∀ q ∈ Q', isSmooth y q) ∧
        -- deficit of Q' ≥ δ
        True := by sorry
```

### D6. Target realization (connecting to Erdős #319)

**Status:** ❌ Missing

```lean
/-- If P ⊆ [1,N] has density ≥ (1 - 1/e + ε) and r = R(A) for a
    small set A of bounded denominators, then r ∈ Σ(P). -/
theorem dense_set_realizes_small_target (ε : ℝ) (hε : 0 < ε) (C : ℕ) :
    ∀ᶠ N in Filter.atTop,
    ∀ P : Finset ℕ, (∀ p ∈ P, p ≤ N) →
      P.card ≥ ⌈((1 - 1 / Real.exp 1 + ε) * N)⌉₊ →
    ∀ A : Finset ℕ, A.card ≤ C → (∀ a ∈ A, a ≤ N) →
      recipSum (A.image (fun n => (⟨n, sorry⟩ : ℕ+))) ∈
        subsetSumImage (P.image (fun n => (⟨n, sorry⟩ : ℕ+))) := by sorry
```

---

## E. Dependency Graph

```
Erdős #319
    │
    ├── D5. Density → entropy deficit (❌)
    │
    ├── D6. Target realization (❌)
    │
    └── Dominant Short-Energy Conjecture (🔮)
            │
            ├── D3. Kernel vector count bound (❌)
            │       │
            │       ├── D4. Conformal decomposition (❌)
            │       │       │
            │       │       └── D2. Support-s classification (❌)
            │       │               │
            │       │               └── D1. Effective S-unit bound (❌)
            │       │                       │
            │       │                       └── B2. Support-4 catalogue (🔗 reduced)
            │       │                               │
            │       │                               └── B1. Support-3 completeness (✅)
            │       │
            │       └── C1. Support-3 energy (✅)
            │
            ├── A3. Energy spectrum decomposition (✅)
            │
            └── A2. Collision-to-identity (✅)
```

---

## F. Assessment

### What is solid
The entire foundation layer (A) and support-3 classification (B1) are
machine-verified with no sorries. The energy spectrum identity
`#Collisions = 2^k + Σ E_s · 2^{k-s}` is an exact algebraic theorem,
not a conjecture.

### What is close to provable
Support-4 completeness (B2) reduces to effective Baker/de Weger bounds for
{2,3} S-unit equations — a solved problem in computational number theory.
The computational catalogue is stable to 10⁶.

### What is hard
The energy dominance conjecture (C2/C3) requires showing that y-smooth
denominators cannot support exponentially many long kernel vectors without
also having short ones. This is the key open problem.

### What is very far
The Erdős #319 bridges (D5, D6) are independent hard problems that are
not addressed by the current project at all.
