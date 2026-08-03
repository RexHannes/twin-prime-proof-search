import Mathlib
import RequestProject.EnergySpectrumExact
import RequestProject.CollisionProbability
import RequestProject.Support4
import RequestProject.Smooth23

/-!
# Restricted y=3 Energy Dominance

## Overview

We formulate a restricted version of the Dominant Short-Energy Conjecture
specialized to y=3 (i.e., {2,3}-smooth denominators). This is the simplest
non-trivial case and the one where we have the most structural information.

## Key structural facts for y=3

For {2,3}-smooth denominators, we have complete classification results:

1. **Support-3 completeness** (proved): Every support-3 identity belongs to
   Type I (from 1+2=3), Type II (from 1+3=4), or Type III (from 1+8=9).

2. **Support-4 catalogue** (partial): At least 25 coprime families exist,
   all arising from solutions to `a + b = c + d` in {2,3}-smooth integers.
   The complete list is finite by Evertse's theorem.

3. **Unbounded primitive support** (proved): The refinement identity
   `1/n = 1/(2n) + 1/(3n) + 1/(6n)` generates primitive identities of
   arbitrarily large support. So bounded primitive support is FALSE.

## What energy dominance would say for y=3

Even though individual primitive identities can have unbounded support,
the **energy-weighted** contribution of short-support identities should
dominate. Specifically:

**Restricted Energy Dominance for y=3**: For every `δ > 0`, there exist
`C` and `c > 0` such that for every finite set `Q` of {2,3}-smooth positive
integers, if the total weighted energy exceeds `δ`, then the weighted energy
from kernel vectors of support ≤ `C` exceeds `c`.

## The support-3 energy bound

We can make partial progress: if all energy comes from support-3 vectors,
then the energy per vector is exactly `2^{-3} = 1/8`, so even a single
support-3 kernel vector contributes a fixed positive amount to the short energy.

More precisely: `energyAtSupport k q 3 > 0` implies
`shortWeightedEnergy k q 3 ≥ 1/8`.

This is trivially true from the definition.

## What's needed for a full y=3 energy dominance proof

The hard part is showing that if total energy is large, there MUST be
short-support vectors. The danger is:

**Exponential-growth scenario**: Could there be a {2,3}-smooth denominator
set `Q` with no kernel vectors of support ≤ C, but `2^{0.95 s}` kernel
vectors at each support level `s > C`? This would give total energy
`Σ_{s > C} 2^{0.95s} · 2^{-s} = Σ 2^{-0.05s}`, which converges but
could be made large by starting at a large `C`.

This scenario would violate energy dominance. The conjecture asserts it
cannot happen for {2,3}-smooth denominators, but proving this requires
understanding the multiplicative structure of the kernel.

## Formal statements
-/

open Finset BigOperators

noncomputable section

/-! ## The support-3 energy contribution bound -/

/-- If a set has any support-3 kernel vector, the weighted energy at support 3
    is at least 1/8. This is immediate from definitions. -/
theorem support3_energy_pos (k : ℕ) (q : Fin k → ℕ)
    (h : 0 < energyAtSupport k q 3) :
    (energyAtSupport k q 3 : ℚ) / 2 ^ 3 ≥ 1 / 8 := by
  norm_num
  exact div_le_div_of_nonneg_right (by exact_mod_cast h) (by positivity)

/-- If a set has any support-3 kernel vector, the short weighted energy
    up to support 3 is positive. -/
theorem shortEnergy_pos_of_support3 (k : ℕ) (q : Fin k → ℕ)
    (h : 0 < energyAtSupport k q 3) :
    0 < shortWeightedEnergy k q 3 := by
  unfold shortWeightedEnergy
  apply Finset.sum_pos'
  · intro s _
    exact div_nonneg (Nat.cast_nonneg _) (by positivity)
  · exact ⟨3, Finset.mem_range.mpr (by omega), by
      apply div_pos
      · exact_mod_cast h
      · positivity⟩

/-! ## The y=3 restricted energy dominance conjecture

This is strictly weaker than the full Dominant Short-Energy Conjecture
because it fixes `y = 3`.
-/

/-- **Restricted Energy Dominance for y=3** (NOT proved).

    For every `δ > 0`, there exist constants `C` and `c > 0` such that:
    for every `k` and every `k`-tuple of positive {2,3}-smooth denominators `q`,
    if the total weighted energy ≥ δ, then the short weighted energy ≤ C
    satisfies shortWeightedEnergy ≥ c.

    **Status**: Conjectural. Supported by computational evidence for k ≤ 12.
    Would follow from a proof that exponentially many long kernel vectors
    cannot exist without short ones for {2,3}-smooth denominators.

    **Key obstruction**: Showing that the refinement family
    `1/n = 1/(2n) + 1/(3n) + 1/(6n)` cannot create exponentially many
    long kernel vectors without also creating short ones. -/
theorem energy_dominance_y3 (δ : ℚ) (hδ : 0 < δ) :
    ∃ C : ℕ, ∃ c : ℚ, 0 < c ∧
    ∀ k : ℕ, ∀ q : Fin k → ℕ,
      (∀ i, q i ≠ 0) →
      (∀ i, isSmooth 3 (q i)) →
      totalWeightedEnergy k q ≥ δ →
      shortWeightedEnergy k q C ≥ c := by
  sorry

/-! ## The y=3 shortest-vector conjecture

Weaker variant: if total energy is positive, at least one short kernel
vector exists.
-/

/-- **Restricted Shortest-Vector for y=3** (NOT proved). -/
theorem shortest_vector_y3 (δ : ℚ) (hδ : 0 < δ) :
    ∃ C : ℕ,
    ∀ k : ℕ, ∀ q : Fin k → ℕ,
      (∀ i, q i ≠ 0) →
      (∀ i, isSmooth 3 (q i)) →
      totalWeightedEnergy k q ≥ δ →
      ∃ s, s ≤ C ∧ 0 < energyAtSupport k q s := by
  sorry

/-! ## Relationship to S-unit equations

For y=3, the S-unit equation classification gives us:

1. **Support ≤ 3**: Fully classified (3 families: Type I, II, III).
   Each contributes energy 2^{-3} = 1/8 per kernel vector.

2. **Support ≤ 4**: At least 25 coprime families. Each contributes
   energy 2^{-4} = 1/16 per kernel vector.

3. **Support ≤ s for general s**: The number of coprime families is
   bounded by Evertse's theorem. For fixed coprime family, the number
   of instantiations in a given set Q depends on Q.

The energy dominance conjecture would follow if we could show:
- The number of coprime families at each support level grows at most
  polynomially in s (TRUE by Evertse's bound).
- The instantiation count per family is bounded.
- The total energy from all levels > C decays geometrically.

The missing bridge is the second point: bounding the number of
instantiations of each family in a given Q.
-/

/-! ## Concrete structural lemma: support-3 detection

For {2,3}-smooth denominators, if Q contains three elements forming
a Type I, II, or III identity, then energyAtSupport detects it.
-/

/-- A Type I triple `(2^(a-1)·3^b, 2^a·3^b, 2^a·3^(b-1))` creates
    a support-3 kernel vector. -/
theorem typeI_creates_support3_energy (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    (1 : ℚ) / (2 ^ (a - 1) * 3 ^ b) + 1 / (2 ^ a * 3 ^ b) =
    1 / (2 ^ a * 3 ^ (b - 1)) := by
  -- This is exactly `smooth23_typeI_identity`
  exact smooth23_typeI_identity a b ha hb

end
