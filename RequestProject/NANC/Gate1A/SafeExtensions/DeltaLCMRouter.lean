/-
# NANC Gate 1A v9 — the delta-LCM finite router

The hard `(delta, delta')` pairs are those with `lcm(d,d') ≤ J`, where
`d = |delta|`, `d' = |delta'|` are positive.  Since `lcm(d,d') = r` forces
`d ∣ r` and `d' ∣ r`, the count is bounded by the exact finite sum

    #HardDeltaPairs J ≤ ∑_{r ∈ [1,J]} (#divisors r)².

No asymptotic divisor theorem, and in particular no `J·X^{o(1)}` claim, is
banked.
-/
import Mathlib

namespace TwinPrimeProject.NANC.Gate1A.V9

open Finset

/-- The hard `(d, d')` pairs with `lcm(d,d') ≤ J`; both entries are positive and
automatically at most `J`. -/
def HardDeltaPairs (J : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 J) ×ˢ (Finset.Icc 1 J)).filter fun p => Nat.lcm p.1 p.2 ≤ J

theorem mem_hardDeltaPairs {J : ℕ} {p : ℕ × ℕ} :
    p ∈ HardDeltaPairs J ↔
      (1 ≤ p.1 ∧ p.1 ≤ J) ∧ (1 ≤ p.2 ∧ p.2 ≤ J) ∧ Nat.lcm p.1 p.2 ≤ J := by
  simp [HardDeltaPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, and_assoc]

/-- **Exact finite router bound.** -/
theorem hardDeltaPairs_card_le_divisorSquareSum (J : ℕ) :
    (HardDeltaPairs J).card ≤ ∑ r ∈ Finset.Icc 1 J, (Nat.divisors r).card ^ 2 := by
  have hsub : HardDeltaPairs J ⊆
      (Finset.Icc 1 J).biUnion fun r => (Nat.divisors r) ×ˢ (Nat.divisors r) := by
    intro p hp
    rw [mem_hardDeltaPairs] at hp
    obtain ⟨⟨hp1, _⟩, ⟨hp2, _⟩, hlcm⟩ := hp
    have hd1 : p.1 ≠ 0 := by omega
    have hd2 : p.2 ≠ 0 := by omega
    have hlcm0 : Nat.lcm p.1 p.2 ≠ 0 := Nat.lcm_ne_zero hd1 hd2
    refine Finset.mem_biUnion.mpr ⟨Nat.lcm p.1 p.2, ?_, ?_⟩
    · exact Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr hlcm0, hlcm⟩
    · exact Finset.mem_product.mpr
        ⟨Nat.mem_divisors.mpr ⟨Nat.dvd_lcm_left _ _, hlcm0⟩,
         Nat.mem_divisors.mpr ⟨Nat.dvd_lcm_right _ _, hlcm0⟩⟩
  calc (HardDeltaPairs J).card
      ≤ ((Finset.Icc 1 J).biUnion fun r => (Nat.divisors r) ×ˢ (Nat.divisors r)).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ r ∈ Finset.Icc 1 J, ((Nat.divisors r) ×ˢ (Nat.divisors r)).card :=
        Finset.card_biUnion_le
    _ = ∑ r ∈ Finset.Icc 1 J, (Nat.divisors r).card ^ 2 := by
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [Finset.card_product, sq]

end TwinPrimeProject.NANC.Gate1A.V9
