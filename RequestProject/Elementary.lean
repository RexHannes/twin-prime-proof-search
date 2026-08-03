import Mathlib
import RequestProject.Defs

/-!
# Elementary Lemmas for Reciprocal Subset-Sum Entropy

These are the basic facts that follow from definitions, establishing:
1. Injectivity characterization of full entropy
2. Collisions imply reciprocal identities
3. Collision probability formula
4. Clearing denominators
-/

open scoped BigOperators
open Finset

noncomputable section

/-! ## 1. Injectivity ↔ Full Entropy

The subset-sum image has `|Σ(Q)| = 2^|Q|` iff the map `U ↦ R(U)` is injective
on `Q.powerset`. This is the combinatorial core of `H₂(Q) = |Q|`.
-/

/-
The subset-sum image has at most `2^|Q|` elements.
-/
theorem subsetSumImage_card_le (Q : Finset ℕ+) :
    (subsetSumImage Q).card ≤ 2 ^ Q.card := by
  exact Finset.card_image_le.trans_eq ( Finset.card_powerset _ )

/-
Full image size iff the subset-sum map is injective on powerset.
-/
theorem subsetSumImage_card_eq_iff (Q : Finset ℕ+) :
    (subsetSumImage Q).card = 2 ^ Q.card ↔
      Set.InjOn recipSum (↑Q.powerset : Set (Finset ℕ+)) := by
  constructor <;> intro h;
  · have := Finset.card_image_iff.mp ( by aesop : Finset.card ( Finset.image recipSum Q.powerset ) = _ ) ; aesop;
  · erw [ Finset.card_image_of_injOn h, Finset.card_powerset ]

/-! ## 2. Non-injectivity implies collisions

If the subset-sum map is not injective, there exist distinct A, B ⊆ Q
with R(A) = R(B).
-/

/-
If the subset-sum map is not injective on `Q.powerset`, there exist
    distinct `A, B ⊆ Q` with `R(A) = R(B)`.
-/
theorem exists_collision_of_not_injective (Q : Finset ℕ+)
    (h : ¬ Set.InjOn recipSum (↑Q.powerset : Set (Finset ℕ+))) :
    ∃ A B : Finset ℕ+, A ∈ Q.powerset ∧ B ∈ Q.powerset ∧ A ≠ B ∧
      recipSum A = recipSum B := by
  unfold Set.InjOn at h; aesop;

/-! ## 3. Collision → Disjoint Reciprocal Identity

Given distinct A, B ⊆ Q with R(A) = R(B), removing A ∩ B yields
disjoint nonempty A', B' with R(A') = R(B').
-/

/-
Removing the intersection preserves the reciprocal sum equality.
-/
theorem recipSum_sdiff_eq_of_eq {A B : Finset ℕ+}
    (h : recipSum A = recipSum B) :
    recipSum (A \ B) = recipSum (B \ A) := by
  -- Write A = (A \ B) ∪ (A ∩ B) and B = (B \ A) ∪ (A ∩ B) with disjoint unions.
  have h_decomp : recipSum A = recipSum (A \ B) + recipSum (A ∩ B) ∧ recipSum B = recipSum (B \ A) + recipSum (A ∩ B) := by
    unfold recipSum;
    exact ⟨ by rw [ ← Finset.sum_union ( Finset.disjoint_right.mpr fun x => by aesop ) ] ; congr; ext x; by_cases hx : x ∈ B <;> aesop, by rw [ ← Finset.sum_union ( Finset.disjoint_right.mpr fun x => by aesop ) ] ; congr; ext x; by_cases hx : x ∈ A <;> aesop ⟩;
  grind +revert

/-
If A ≠ B and R(A) = R(B), then A \ B is nonempty.
-/
theorem sdiff_nonempty_of_ne_and_eq {A B : Finset ℕ+}
    (hne : A ≠ B) (hsum : recipSum A = recipSum B) :
    (A \ B).Nonempty := by
  contrapose! hne; simp_all +decide [ Finset.sdiff_eq_empty_iff_subset ] ;
  -- Since $A$ is a subset of $B$ and their sums are equal, we can use the fact that if the sum of reciprocals of a subset is equal to the sum of reciprocals of the superset, then the subset must be equal to the superset.
  have h_eq : ∑ x ∈ B \ A, (1 : ℚ) / x = 0 := by
    unfold recipSum at hsum;
    rw [ ← Finset.sum_sdiff hne ] at hsum ; aesop;
  exact Finset.Subset.antisymm hne fun x hx => by_contra fun hx' => absurd h_eq <| ne_of_gt <| Finset.sum_pos ( fun y hy => one_div_pos.mpr <| Nat.cast_pos.mpr <| PNat.pos _ ) ⟨ x, by aesop ⟩ ;

/-
From a collision between distinct subsets, we extract a reciprocal identity.
-/
theorem collision_to_identity (Q : Finset ℕ+)
    (A B : Finset ℕ+) (hA : A ⊆ Q) (hB : B ⊆ Q)
    (hne : A ≠ B) (hsum : recipSum A = recipSum B) :
    ∃ _ : ReciprocalIdentity Q, True := by
  refine' ⟨ ⟨ A \ B, B \ A, _, _, _, _, _, _ ⟩, trivial ⟩ <;> simp_all +decide [ Finset.subset_iff, recipSum_sdiff_eq_of_eq ];
  · exact sdiff_nonempty_of_ne_and_eq hne hsum;
  · convert sdiff_nonempty_of_ne_and_eq _ _ using 1;
    · grind;
    · exact hsum.symm;
  · exact Finset.disjoint_left.mpr fun x hx₁ hx₂ => by aesop;

/-! ## 4. Collision Probability Formula

`collisionCount Q = ∑ t, (subsetSumMult Q t) ^ 2`.
-/

/-
The collision count equals the sum of squared multiplicities.
-/
theorem collisionCount_eq_sum_sq (Q : Finset ℕ+) :
    collisionCount Q =
      ∑ t ∈ subsetSumImage Q, (subsetSumMult Q t) ^ 2 := by
  unfold collisionCount subsetSumImage subsetSumMult;
  simp +decide only [card_filter, sq];
  simp +decide only [sum_product, sum_mul];
  rw [ Finset.sum_image' ];
  simp +contextual [ Finset.sum_filter ];
  simp +contextual [ eq_comm ]

/-! ## 5. Clearing Denominators

For finite Q, let L = lcm Q. Then R(A) = R(B) iff ∑_{a ∈ A} L/a = ∑_{b ∈ B} L/b.
-/

/-
Clearing denominators: if L is a common multiple of all elements of Q,
    then for A, B ⊆ Q, R(A) = R(B) iff the integer-weighted sums agree.
-/
theorem clearing_denominators (Q : Finset ℕ+) (L : ℕ+)
    (hL : ∀ q ∈ Q, (q : ℕ) ∣ (L : ℕ))
    (A B : Finset ℕ+) (hA : A ⊆ Q) (hB : B ⊆ Q) :
    recipSum A = recipSum B ↔
      ∑ a ∈ A, intWeight L a = ∑ b ∈ B, intWeight L b := by
  have h_clear_denominators : ∀ A : Finset ℕ+, A ⊆ Q → (∑ a ∈ A, (intWeight L a : ℚ)) = (L : ℚ) * (∑ a ∈ A, (1 : ℚ) / a) := by
    intro A hA; rw [ Finset.mul_sum _ _ _ ] ; refine Finset.sum_congr rfl fun x hx => ?_; simp +decide [ intWeight ] ;
    rw [ ← div_eq_mul_inv, Nat.cast_div ( hL x ( hA hx ) ) ( by positivity ) ];
  rw [ ← @Nat.cast_inj ℚ ] ; simp_all +decide [ recipSum ]

/-
`recipSum` distributes over disjoint union.
-/
theorem recipSum_union_disjoint {A B : Finset ℕ+} (h : Disjoint A B) :
    recipSum (A ∪ B) = recipSum A + recipSum B := by
  unfold recipSum; rw [ Finset.sum_union h ] ;

/-
`recipSum ∅ = 0`.
-/
theorem recipSum_empty : recipSum ∅ = 0 := by
  rfl

/-
`recipSum {q} = 1 / q`.
-/
theorem recipSum_singleton (q : ℕ+) :
    recipSum {q} = 1 / (q : ℚ) := by
  unfold recipSum; norm_num;

end