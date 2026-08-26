/-
NANC V4 — weighted twin mass and the finite existence implication.

`positive weighted twin mass  →  existence of a twin-prime pair` is a genuine
finite theorem and is banked here.  Twin-prime *infinitude* is NOT declared.
-/
import Mathlib
import RequestProject.NANC.V4.ShiftedPrimeModel

namespace NANC.V4

open scoped BigOperators

/-- The weighted twin mass of a finite set `S`:
`∑_{p ∈ S, p prime} log(p+2) · 1_{p+2 prime}`. -/
noncomputable def weightedTwinMass (S : Finset ℕ) : ℝ :=
  ∑ p ∈ S.filter Nat.Prime, shiftedPrimeWeight p

theorem weightedTwinMass_nonneg (S : Finset ℕ) : 0 ≤ weightedTwinMass S :=
  Finset.sum_nonneg fun p _ => shiftedPrimeWeight_nonneg p

/-- **Positive weighted twin mass produces a twin-prime pair.** -/
theorem positive_weightedTwinMass_exists_twin {S : Finset ℕ} (h : 0 < weightedTwinMass S) :
    ∃ p ∈ S, Nat.Prime p ∧ Nat.Prime (p + 2) := by
  by_contra hcon
  push_neg at hcon
  have hzero : weightedTwinMass S = 0 := by
    refine Finset.sum_eq_zero ?_
    intro p hp
    obtain ⟨hpS, hpp⟩ := Finset.mem_filter.mp hp
    exact shiftedPrimeWeight_eq_zero_of_not_prime (hcon p hpS hpp)
  rw [hzero] at h
  exact lt_irrefl 0 h

/-- The same statement for an abstract nonnegative prime weight, where positivity
on the shifted primes is not needed: only the vanishing off the twin support. -/
theorem positive_genericTwinMass_exists_twin (W : PrimeWeight) {S : Finset ℕ}
    (h : 0 < ∑ p ∈ S.filter Nat.Prime, W.w p) :
    ∃ p ∈ S, Nat.Prime p ∧ Nat.Prime (p + 2) := by
  by_contra hcon
  push_neg at hcon
  have hzero : ∑ p ∈ S.filter Nat.Prime, W.w p = 0 := by
    refine Finset.sum_eq_zero ?_
    intro p hp
    obtain ⟨hpS, hpp⟩ := Finset.mem_filter.mp hp
    exact W.w_eq_zero_of_not_shifted_prime p (hcon p hpS hpp)
  rw [hzero] at h
  exact lt_irrefl 0 h

/-- **Interface (not inhabited).**  Twin mass is positive in arbitrarily late
windows.  This is exactly the analytic conclusion that the Ford–Maynard endgame
would have to supply; it is *not* proved here. -/
def EventuallyPositiveTwinMass : Prop :=
  ∀ N : ℕ, ∃ S : Finset ℕ, (∀ p ∈ S, N ≤ p) ∧ 0 < weightedTwinMass S

/-- Conditional: positivity of twin mass in arbitrarily late windows gives
infinitely many twin primes.  This is a genuine finite/logical deduction from the
(uninhabited) interface above. -/
theorem eventuallyPositiveTwinMass_imp_infinite (h : EventuallyPositiveTwinMass) :
    {p : ℕ | Nat.Prime p ∧ Nat.Prime (p + 2)}.Infinite := by
  refine Set.infinite_of_not_bddAbove ?_
  rintro ⟨B, hB⟩
  obtain ⟨S, hSmem, hSpos⟩ := h (B + 1)
  obtain ⟨p, hpS, hp1, hp2⟩ := positive_weightedTwinMass_exists_twin hSpos
  have hple : p ≤ B := hB ⟨hp1, hp2⟩
  have := hSmem p hpS
  omega

end NANC.V4
