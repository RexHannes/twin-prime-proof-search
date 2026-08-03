import Mathlib
import RequestProject.Y3ShortestVectorAttempt

/-!
# Layer-Peel Extraction Lemmas

## Overview

This file proves restricted extraction lemmas for the layer-peeling strategy
on {2,3}-smooth kernel vectors. These lemmas formalize the simplest observed
patterns from the layer pattern survey (`GrowthQ/LayerPatternSurvey.md`).

## Main results

1. **Sub-kernel extraction** (`sub_kernel_extraction`): If a proper nonempty
   subset S of the support has signed-weighted sum 0, the kernel vector
   decomposes into two nonzero sub-kernel vectors with disjoint support.

2. **Equal-weight opposite-sign cancellation** (`equal_weight_cancel`): If
   two support elements have equal weight and opposite sign, they cancel
   and the remaining support forms a smaller kernel vector.

3. **v₂-peel divisibility** (`v2_peel_even`): The signed sum of the
   odd-weight support elements is always even.

4. **Type I layer extraction** (`typeI_layer_extraction`): If the v₂-layer
   has exactly 2 elements with consecutive 3-adic exponents (gap 1,
   opposite sign), and there exists a third support element with matching
   weight 2·3^β, then a support-3 sub-kernel vector exists corresponding
   to the Type I identity (1+2=3 scaled).

## Restrictions declared honestly

- These lemmas do NOT prove that a short sub-kernel vector always exists.
- The Type I extraction requires the matching third element to be present
  in the support — this is an assumption, not a consequence.
- No claim is made about primitivity or completeness.
-/

open Finset BigOperators

/-! ## Section 1: Sub-kernel Extraction -/

section SubKernelExtraction

/-
**Sub-kernel extraction lemma.**
If a sign vector `z` with `∑ zᵢ · wᵢ = 0` has a proper nonempty subset
`S ⊂ supp(z)` such that `∑_{i ∈ S} zᵢ · wᵢ = 0`, then the restriction
of `z` to `S` is a nonzero sub-kernel vector with smaller support.

Concretely: `z' i = if i ∈ S then z i else 0` is a nonzero kernel vector
with `signSupp z' = S`.
-/
theorem sub_kernel_extraction {k : ℕ} {z : Fin k → ℤ} {w : Fin k → ℕ}
    (hsign : IsSignVec z)
    (hker : signedWtSum z w = 0)
    (S : Finset (Fin k))
    (hS_sub : S ⊆ signSupp z)
    (hS_ne : S.Nonempty)
    (hS_proper : S ⊂ signSupp z)
    (hS_sum : ∑ i ∈ S, z i * (w i : ℤ) = 0) :
    let z' : Fin k → ℤ := fun i => if i ∈ S then z i else 0
    IsSignVec z' ∧
    signedWtSum z' w = 0 ∧
    (signSupp z').Nonempty ∧
    signSupp z' ⊂ signSupp z := by
      refine' ⟨ _, _, _, _ ⟩;
      · intro i; specialize hsign i; aesop;
      · simp_all +decide [ Finset.sum_ite, signedWtSum ];
      · obtain ⟨ i, hi ⟩ := hS_ne; use i; simp_all +decide [ signSupp ] ;
        exact Finset.mem_filter.mp ( hS_sub hi ) |>.2;
      · simp_all +decide [ Finset.ssubset_def, Finset.subset_iff ];
        unfold signSupp at *; aesop;

/-
**Complement sub-kernel vector.**
Under the same conditions, the complement `supp(z) \ S` also gives
a nonzero kernel vector.
-/
theorem complement_sub_kernel {k : ℕ} {z : Fin k → ℤ} {w : Fin k → ℕ}
    (hsign : IsSignVec z)
    (hker : signedWtSum z w = 0)
    (S : Finset (Fin k))
    (hS_sub : S ⊆ signSupp z)
    (hS_ne : S.Nonempty)
    (hS_proper : S ⊂ signSupp z)
    (hS_sum : ∑ i ∈ S, z i * (w i : ℤ) = 0) :
    let z'' : Fin k → ℤ := fun i => if i ∈ signSupp z \ S then z i else 0
    IsSignVec z'' ∧
    signedWtSum z'' w = 0 ∧
    (signSupp z'').Nonempty ∧
    signSupp z'' ⊂ signSupp z := by
      refine' ⟨ _, _, _, _ ⟩;
      · intro i; specialize hsign i; aesop;
      · convert congr_arg₂ ( · - · ) hker hS_sum using 1;
        simp +decide [ signedWtSum, Finset.sum_ite ];
        rw [ eq_sub_iff_add_eq', ← Finset.sum_union ];
        · rw [ Finset.sum_subset ];
          · exact Finset.subset_univ _;
          · simp +contextual [ signSupp ];
        · exact Finset.disjoint_left.mpr fun x hx₁ hx₂ => by aesop;
      · obtain ⟨ i, hi ⟩ := Finset.exists_of_ssubset hS_proper;
        use i; simp_all +decide [ signSupp ] ;
      · simp_all +decide [ Finset.ssubset_def, Finset.subset_iff, signSupp ];
        exact ⟨ _, hS_sub hS_ne.choose_spec, hS_ne.choose_spec ⟩

end SubKernelExtraction

/-! ## Section 2: Equal-Weight Opposite-Sign Cancellation -/

section EqualWeightCancel

/-
**Equal-weight opposite-sign cancellation.**
If two support elements `j₁ ≠ j₂` have equal weight `w j₁ = w j₂`
and opposite sign `z j₁ = -(z j₂)`, then `z j₁ · w j₁ + z j₂ · w j₂ = 0`,
so `{j₁, j₂}` witnesses a sub-kernel decomposition (provided |supp| ≥ 3).
-/
theorem equal_weight_cancel {k : ℕ} {z : Fin k → ℤ} {w : Fin k → ℕ}
    (hsign : IsSignVec z)
    (hker : signedWtSum z w = 0)
    (j₁ j₂ : Fin k)
    (hne : j₁ ≠ j₂)
    (hj₁_supp : z j₁ ≠ 0)
    (hj₂_supp : z j₂ ≠ 0)
    (hw_eq : w j₁ = w j₂)
    (hz_opp : z j₁ = -(z j₂))
    (hsupp_ge3 : 3 ≤ (signSupp z).card) :
    ∃ z' : Fin k → ℤ,
      IsSignVec z' ∧
      signedWtSum z' w = 0 ∧
      (signSupp z').Nonempty ∧
      (signSupp z').card + 2 ≤ (signSupp z).card := by
        refine' ⟨ fun i => if i = j₁ then 0 else if i = j₂ then 0 else z i, _, _, _, _ ⟩;
        · intro i; specialize hsign i; aesop;
        · simp_all +decide [ Finset.sum_ite, Finset.filter_ne', Finset.filter_eq', signedWtSum ];
          rw [ ← Finset.sum_erase_add _ _ ( Finset.mem_univ j₁ ), ← Finset.sum_erase_add _ _ ( Finset.mem_erase_of_ne_of_mem ( Ne.symm hne ) ( Finset.mem_univ j₂ ) ) ] at hker ; aesop;
        · contrapose! hsupp_ge3;
          rw [ show signSupp z = { j₁, j₂ } from ?_ ];
          · rw [ Finset.card_insert_of_notMem, Finset.card_singleton ] <;> aesop;
          · simp_all +decide [ Finset.ext_iff, signSupp ];
            grind;
        · rw [ show signSupp ( fun i => if i = j₁ then 0 else if i = j₂ then 0 else z i ) = signSupp z \ { j₁, j₂ } from ?_ ];
          · rw [ Finset.card_sdiff ];
            rw [ Finset.inter_eq_left.mpr ] <;> norm_num [ hne, hj₁_supp, hj₂_supp ];
            · omega;
            · simp_all +decide [ Finset.subset_iff, signSupp ];
          · ext i; by_cases hi₁ : i = j₁ <;> by_cases hi₂ : i = j₂ <;> simp +decide [ *, signSupp ] ;

end EqualWeightCancel

/-! ## Section 3: v₂-Peel Divisibility -/

section V2Peel

/-
**v₂-peel divisibility.**
If the odd-weight support has exactly 2 elements `j₁, j₂`, then their
signed contribution `z j₁ · w j₁ + z j₂ · w j₂` is even.

This is immediate from parity: both `w j₁` and `w j₂` are odd, and
`z j₁, z j₂ ∈ {±1}`, so the sum of two odd numbers is even.
-/
theorem v2_peel_even {k : ℕ} {z : Fin k → ℤ} {w : Fin k → ℕ}
    (hsign : IsSignVec z)
    (_hker : signedWtSum z w = 0)
    (j₁ j₂ : Fin k)
    (hne : j₁ ≠ j₂)
    (_hj₁ : j₁ ∈ oddWtSupp z w)
    (_hj₂ : j₂ ∈ oddWtSupp z w)
    (h_only : oddWtSupp z w = {j₁, j₂}) :
    (2 : ℤ) ∣ (z j₁ * (w j₁ : ℤ) + z j₂ * (w j₂ : ℤ)) := by
      simp_all +decide [ Finset.ext_iff, oddWtSupp ];
      cases hsign j₁ <;> cases hsign j₂ <;> simp_all +decide [ ← even_iff_two_dvd, parity_simps ];
      · grind;
      · cases ‹_› <;> simp_all +decide [ Nat.even_iff ];
        · specialize h_only j₂ ; simp_all +decide [ signSupp ];
        · grind;
      · cases ‹z j₁ = 0 ∨ z j₁ = 1› <;> simp_all +decide [ Nat.even_iff ];
        · specialize h_only j₁ ; simp_all +decide [ signSupp ];
        · grind;
      · cases ‹z j₁ = 0 ∨ z j₁ = 1› <;> cases ‹z j₂ = 0 ∨ z j₂ = 1› <;> simp_all +decide [ Nat.even_iff ];
        · specialize h_only j₁ ; simp_all +decide [ signSupp ];
        · specialize h_only j₂; simp_all +decide [ signSupp ] ;
        · grind

/-
**v₂-peel: the odd-weight layer sum equals minus the even-weight sum.**
Since `∑ zᵢ wᵢ = 0`, the odd-weight subtotal and even-weight subtotal
must be negatives of each other.
-/
theorem v2_peel_complement {k : ℕ} {z : Fin k → ℤ} {w : Fin k → ℕ}
    (_hsign : IsSignVec z)
    (hker : signedWtSum z w = 0) :
    ∑ i ∈ oddWtSupp z w, z i * (w i : ℤ) =
    -(∑ i ∈ (signSupp z) \ (oddWtSupp z w), z i * (w i : ℤ)) := by
      rw [ eq_neg_iff_add_eq_zero, ← Finset.sum_union ];
      · rw [ ← hker, Finset.sum_subset ];
        congr! 1;
        · exact Finset.subset_univ _;
        · unfold oddWtSupp signSupp; aesop;
      · exact Finset.disjoint_sdiff

end V2Peel

/-! ## Section 4: Type I Layer Extraction -/

section TypeIExtraction

/-
**Type I layer extraction.**

Suppose a kernel equation `∑ zᵢ · wᵢ = 0` has three support elements
`j₁, j₂, j₃` with weights satisfying the Type I relation (based on 1+2=3):

  `w j₁ = 3 * g`, `w j₂ = 2 * g`, `w j₃ = 1 * g`

for some positive `g`, and signs `z j₁ = ε`, `z j₂ = -ε`, `z j₃ = -ε`.
(Here `j₁` is the "3-part", `j₂` is the "2-part", `j₃` is the "1-part".)

Then `z j₁ · w j₁ + z j₂ · w j₂ + z j₃ · w j₃ = 0`, and provided the
total support has ≥ 4 elements, the kernel vector decomposes.

**Restriction**: This assumes the matching elements are all present in the
support. This is an assumption, not a consequence of the layer structure.

The pattern arises from the v₂-peel when the odd-weight pair has consecutive
3-adic exponents (gap 1) and opposite signs:
  `z₁ · 3^{β+1} - z₁ · 3^β = z₁ · 3^β · 2`
which matches the even-weight element `w = 2 · 3^β`.
-/
theorem typeI_layer_extraction {k : ℕ} {z : Fin k → ℤ} {w : Fin k → ℕ}
    (hsign : IsSignVec z)
    (hker : signedWtSum z w = 0)
    (j₁ j₂ j₃ : Fin k)
    (hdistinct : j₁ ≠ j₂ ∧ j₁ ≠ j₃ ∧ j₂ ≠ j₃)
    (g : ℕ) (hg : 0 < g)
    (hw₁ : w j₁ = 3 * g)
    (hw₂ : w j₂ = 2 * g)
    (hw₃ : w j₃ = g)
    (_hj₁_supp : z j₁ ≠ 0)
    (hj₂_supp : z j₂ ≠ 0)
    (hj₃_supp : z j₃ ≠ 0)
    (hz_rel : z j₁ = -(z j₂) ∧ z j₁ = -(z j₃))
    (hsupp_ge4 : 4 ≤ (signSupp z).card) :
    -- The three elements form a sub-kernel equation:
    z j₁ * (w j₁ : ℤ) + z j₂ * (w j₂ : ℤ) + z j₃ * (w j₃ : ℤ) = 0 ∧
    -- And consequently a proper sub-kernel vector exists:
    ∃ z' : Fin k → ℤ,
      IsSignVec z' ∧
      signedWtSum z' w = 0 ∧
      (signSupp z').Nonempty ∧
      signSupp z' ⊂ signSupp z := by
        refine' ⟨ _, _ ⟩;
        · push_cast [ * ] ; ring;
          grind;
        · convert sub_kernel_extraction hsign hker { j₁, j₂, j₃ } ?_ ?_ ?_ ?_ using 1;
          · constructor;
            · rintro -;
              convert sub_kernel_extraction hsign hker { j₁, j₂, j₃ } ?_ ?_ ?_ ?_ using 1;
              · simp_all +decide [ Finset.subset_iff, signSupp ];
              · simp +decide;
              · simp_all +decide [ Finset.ssubset_def, Finset.subset_iff ];
                obtain ⟨ x, hx ⟩ := Finset.exists_of_ssubset ( Finset.ssubset_iff_subset_ne.mpr ⟨ Finset.insert_subset ( show j₁ ∈ signSupp z from by
                                                                                                                          unfold signSupp; aesop; ) ( Finset.insert_subset ( show j₂ ∈ signSupp z from by
                                                                                                                                                                                        exact Finset.mem_filter.mpr ⟨ Finset.mem_univ _, hj₂_supp ⟩ ) ( Finset.singleton_subset_iff.mpr ( show j₃ ∈ signSupp z from by
                                                                                                                                                                                                                                                                  exact Finset.mem_filter.mpr ⟨ Finset.mem_univ _, hj₃_supp ⟩ ) ) ), by
                                                                                                                                                                                                                                                                  grind ⟩ ) ; use by
                                                                                                                                                                                                                                                                  unfold signSupp; aesop;
                exact ⟨ x, hx.1, by aesop ⟩;
              · simp_all +decide [ Finset.sum_singleton ];
                cases lt_or_gt_of_ne hj₂_supp <;> cases lt_or_gt_of_ne hj₃_supp <;> nlinarith;
            · exact fun h => ⟨ _, h ⟩;
          · simp_all +decide [ Finset.subset_iff, signSupp ];
          · simp +decide;
          · simp_all +decide [ Finset.ssubset_def, Finset.subset_iff ];
            have h_card : Finset.card (signSupp z \ {j₁, j₂, j₃}) ≥ 1 := by
              grind;
            obtain ⟨ x, hx ⟩ := Finset.card_pos.mp h_card; use ⟨ by
              unfold signSupp; aesop;, by
              exact Finset.mem_filter.mpr ⟨ Finset.mem_univ _, hj₂_supp ⟩, by
              exact Finset.mem_filter.mpr ⟨ Finset.mem_univ _, hj₃_supp ⟩ ⟩ ; use x; aesop;
          · simp +decide [ *, Finset.sum_singleton ] ; ring;
            grind

/-
**Type II layer extraction** (based on 1+3=4).

If three support elements have weights `w j₁ = 4g`, `w j₂ = 3g`, `w j₃ = g`
with signs `z j₁ = -ε`, `z j₂ = ε`, `z j₃ = ε`, then they form a sub-kernel.

This pattern arises when the odd-weight pair has gap 1 and same sign:
  `ε · 3^{β+1} + ε · 3^β = ε · 3^β · 4`
matching an even-weight element `w = 4 · 3^β`.
-/
theorem typeII_layer_extraction {k : ℕ} {z : Fin k → ℤ} {w : Fin k → ℕ}
    (hsign : IsSignVec z)
    (hker : signedWtSum z w = 0)
    (j₁ j₂ j₃ : Fin k)
    (hdistinct : j₁ ≠ j₂ ∧ j₁ ≠ j₃ ∧ j₂ ≠ j₃)
    (g : ℕ) (hg : 0 < g)
    (hw₁ : w j₁ = 4 * g)
    (hw₂ : w j₂ = 3 * g)
    (hw₃ : w j₃ = g)
    (_hj₁_supp : z j₁ ≠ 0)
    (_hj₂_supp : z j₂ ≠ 0)
    (hj₃_supp : z j₃ ≠ 0)
    (hz_rel : z j₂ = z j₃ ∧ z j₁ = -(z j₂))
    (hsupp_ge4 : 4 ≤ (signSupp z).card) :
    z j₁ * (w j₁ : ℤ) + z j₂ * (w j₂ : ℤ) + z j₃ * (w j₃ : ℤ) = 0 ∧
    ∃ z' : Fin k → ℤ,
      IsSignVec z' ∧
      signedWtSum z' w = 0 ∧
      (signSupp z').Nonempty ∧
      signSupp z' ⊂ signSupp z := by
        refine' ⟨ _, _ ⟩;
        · push_cast [ * ] ; ring;
        · convert sub_kernel_extraction hsign hker { j₁, j₂, j₃ } ?_ ?_ ?_ ?_ using 1;
          · constructor <;> intro h <;> simp_all +decide [ Finset.ssubset_def, Finset.subset_iff ];
            · convert sub_kernel_extraction hsign hker { j₁, j₂, j₃ } ?_ ?_ ?_ ?_ using 1 <;> simp_all +decide [ Finset.subset_iff, Finset.ssubset_def ];
              · unfold signSupp; aesop;
              · have h_card : #(signSupp z \ {j₁, j₂, j₃}) ≥ 1 := by
                  grind;
                obtain ⟨ x, hx ⟩ := Finset.card_pos.mp h_card; use by
                  simp_all +decide [ signSupp ];
                exact ⟨ x, Finset.mem_sdiff.mp hx |>.1, by aesop ⟩;
              · ring;
            · exact ⟨ _, h ⟩;
          · simp_all +decide [ Finset.subset_iff, signSupp ];
          · simp +decide;
          · simp_all +decide [ Finset.ssubset_def, Finset.subset_iff ];
            have h_complement : Finset.card (signSupp z \ {j₁, j₂, j₃}) ≥ 1 := by
              grind;
            obtain ⟨ x, hx ⟩ := Finset.card_pos.mp h_complement; use ⟨ by
              unfold signSupp; aesop;, by
              unfold signSupp; aesop;, by
              unfold signSupp; aesop; ⟩ ; use x; aesop;
          · simp_all +decide [ Finset.sum_singleton ];
            ring

/-
**Type III layer extraction** (based on 1+8=9).

If three support elements have weights `w j₁ = 9g`, `w j₂ = 8g`, `w j₃ = g`
with signs `z j₁ = -ε`, `z j₂ = ε`, `z j₃ = ε`, then they form a sub-kernel.

This pattern arises from exponent gap 2, opposite sign:
  `ε · 3^{β+2} - ε · 3^β = ε · 3^β · 8`
matching an even-weight element `w = 8 · 3^β`.
-/
theorem typeIII_layer_extraction {k : ℕ} {z : Fin k → ℤ} {w : Fin k → ℕ}
    (hsign : IsSignVec z)
    (hker : signedWtSum z w = 0)
    (j₁ j₂ j₃ : Fin k)
    (hdistinct : j₁ ≠ j₂ ∧ j₁ ≠ j₃ ∧ j₂ ≠ j₃)
    (g : ℕ) (hg : 0 < g)
    (hw₁ : w j₁ = 9 * g)
    (hw₂ : w j₂ = 8 * g)
    (hw₃ : w j₃ = g)
    (_hj₁_supp : z j₁ ≠ 0)
    (_hj₂_supp : z j₂ ≠ 0)
    (hj₃_supp : z j₃ ≠ 0)
    (hz_rel : z j₂ = z j₃ ∧ z j₁ = -(z j₂))
    (hsupp_ge4 : 4 ≤ (signSupp z).card) :
    z j₁ * (w j₁ : ℤ) + z j₂ * (w j₂ : ℤ) + z j₃ * (w j₃ : ℤ) = 0 ∧
    ∃ z' : Fin k → ℤ,
      IsSignVec z' ∧
      signedWtSum z' w = 0 ∧
      (signSupp z').Nonempty ∧
      signSupp z' ⊂ signSupp z := by
        refine' ⟨ _, _ ⟩;
        · push_cast [ hw₁, hw₂, hw₃, hz_rel ] ; ring;
        · convert sub_kernel_extraction hsign hker { j₁, j₂, j₃ } _ _ _ _ <;> simp_all +decide [ Finset.subset_iff ];
          · constructor;
            · rintro -;
              convert sub_kernel_extraction hsign hker { j₁, j₂, j₃ } _ _ _ _ using 1;
              all_goals simp_all +decide [ Finset.subset_iff, signSupp ];
              · grind;
              · ring;
            · exact fun h => ⟨ _, h ⟩;
          · unfold signSupp; aesop;
          · refine' ⟨ _, _ ⟩;
            · simp_all +decide [ Finset.subset_iff, signSupp ];
            · intro h; have := Finset.card_le_card h; simp_all +decide ;
              grind;
          · ring

end TypeIExtraction