import Mathlib

/-! REAL 1B. Gold 4.50-B §10, (19)–(20), retained in Gold 4.53-B.
    The upper twin is n. The range begins at 2 since the prime-only
    weight at n - 2 vanishes for both n = 0 and n = 1. -/
namespace REAL1B

open ArithmeticFunction
noncomputable section
open Classical

def Rough (n : ℕ) : Prop := n < n.minFac ^ 4

theorem rough_iff (n : ℕ) (hn : 1 < n) :
    Rough n ↔ ∀ p : ℕ, p.Prime → p ∣ n → n < p ^ 4 := by
  constructor
  · intro h p hp hd
    exact lt_of_lt_of_le h (Nat.pow_le_pow_left (Nat.minFac_le_of_dvd hp.two_le hd) 4)
  · intro h
    exact h _ (Nat.minFac_prime (by omega)) (Nat.minFac_dvd n)

private theorem pow_length_le_prod (p : ℕ) (l : List ℕ)
    (h : ∀ q ∈ l, p ≤ q) : p ^ l.length ≤ l.prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simpa [pow_succ, Nat.mul_comm] using
      Nat.mul_le_mul (h a (by simp)) (ih (fun q hq => h q (by simp [hq])))

theorem rough_rank (n : ℕ) (hn : 1 < n) (hr : Rough n) :
    cardFactors n = 1 ∨ cardFactors n = 2 ∨ cardFactors n = 3 := by
  have hb := pow_length_le_prod n.minFac n.primeFactorsList (fun q hq =>
    Nat.minFac_le_of_dvd (Nat.prime_of_mem_primeFactorsList hq).two_le
      (Nat.dvd_of_mem_primeFactorsList hq))
  rw [Nat.prod_primeFactorsList (by omega)] at hb
  have hpos := cardFactors_pos_iff_one_lt.mpr hn
  have hlt : cardFactors n < 4 := by
    by_contra! h
    exact (not_le_of_gt hr) ((Nat.pow_le_pow_right (Nat.minFac_pos n) h).trans hb)
  omega

def mu (n : ℕ) : ℝ := (moebius n : ℤ)
def primeMask (n : ℕ) : ℝ := if n.Prime then 1 else 0
def roughMask (n : ℕ) : ℝ := if Rough n then 1 else 0
def classMask (k n : ℕ) : ℝ :=
  if Rough n ∧ Squarefree n ∧ cardFactors n = k then 1 else 0

private theorem prime_rough {n : ℕ} (hp : n.Prime) : Rough n := by
  unfold Rough
  rw [hp.minFac_eq]
  simpa using (Nat.pow_lt_pow_right hp.one_lt (by decide : 1 < 4))

/-- Pointwise unsigned and signed classifications on the entire input. -/
theorem parity_masks (n : ℕ) (hn : 1 < n) :
    (mu n ^ 2 * roughMask n = primeMask n + classMask 2 n + classMask 3 n) ∧
    (mu n * roughMask n = -primeMask n + classMask 2 n - classMask 3 n) := by
  by_cases hr : Rough n
  · by_cases hs : Squarefree n
    · rcases rough_rank n hn hr with h | h | h
      · have hp := cardFactors_eq_one_iff_prime.mp h
        norm_num [mu, moebius_apply_prime hp, primeMask, roughMask, classMask, hr, hs, hp, h]
      · have hp : ¬n.Prime := fun hp => by have := cardFactors_apply_prime hp; omega
        norm_num [mu, moebius_apply_of_squarefree hs, primeMask, roughMask, classMask, hr, hs, hp, h]
      · have hp : ¬n.Prime := fun hp => by have := cardFactors_apply_prime hp; omega
        norm_num [mu, moebius_apply_of_squarefree hs, primeMask, roughMask, classMask, hr, hs, hp, h]
    · have hp : ¬n.Prime := fun hp => hs hp.squarefree
      simp [mu, moebius_eq_zero_of_not_squarefree hs, primeMask, roughMask, classMask, hs, hp]
  · have hp : ¬n.Prime := fun hp => hr (prime_rough hp)
    simp [primeMask, roughMask, classMask, hr, hp]

def mass (X : ℝ) (f : ℕ → ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 2 ⌊2 * X⌋₊,
    (if X < (n : ℝ) ∧ (n - 2).Prime then Real.log (n - 2 : ℕ) else 0) * f n

theorem source_parity (X : ℝ) :
    mass X (fun n => mu n ^ 2 * roughMask n) =
      mass X primeMask + mass X (classMask 2) + mass X (classMask 3) ∧
    mass X (fun n => mu n * roughMask n) =
      -mass X primeMask + mass X (classMask 2) - mass X (classMask 3) := by
  constructor
  · unfold mass
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    simp only
    rw [(parity_masks n (Finset.mem_Icc.mp hn).1).1]
    ring
  · unfold mass
    rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    simp only
    rw [(parity_masks n (Finset.mem_Icc.mp hn).1).2]
    ring

theorem h2_identity (X : ℝ) :
    2 * mass X primeMask =
      mass X (fun n => mu n ^ 2 * roughMask n) - 2 * mass X (classMask 3) -
      mass X (fun n => mu n * roughMask n) := by
  obtain ⟨hu, hs⟩ := source_parity X
  linarith

/-- The two error terms can be controlled separately. The signed bound is a hypothesis. -/
theorem h2_lower (X h₀ ρ e N E₁ E₂ : ℝ)
    (hu : (h₀ - e) * N - E₁ ≤ mass X (fun n => mu n ^ 2 * roughMask n) -
      2 * mass X (classMask 3))
    (hs : mass X (fun n => mu n * roughMask n) + ρ * N ≤ N / 8 + E₂) :
    (h₀ + ρ - e - 1 / 8) * N - E₁ - E₂ ≤ 2 * mass X primeMask := by
  linarith only [h2_identity X, hu, hs]

/-- A positive mass forces a pair at the original open lower endpoint. -/
theorem pair_of_mass_pos {X : ℝ} (h : 0 < mass X primeMask) :
    ∃ n : ℕ, X < n ∧ n ≤ ⌊2 * X⌋₊ ∧ n.Prime ∧ (n - 2).Prime := by
  by_contra! he
  have hz : mass X primeMask = 0 := by
    unfold mass
    apply Finset.sum_eq_zero
    intro n hn
    by_cases hm : X < (n : ℝ) ∧ (n - 2).Prime
    · have hnp : ¬ n.Prime := fun hp =>
        he n hm.1 (Finset.mem_Icc.mp hn).2 hp hm.2
      simp [primeMask, hnp]
    · simp [hm]
  linarith

/-- Conditional endpoint: positive source mass at arbitrarily large scales. -/
theorem infinite_of_unbounded_mass
    (h : ∀ B : ℕ, ∃ X : ℝ, (B : ℝ) < X ∧ 0 < mass X primeMask) :
    Set.Infinite {p : ℕ | p.Prime ∧ (p + 2).Prime} := by
  intro hf
  obtain ⟨b, hb⟩ := hf.bddAbove
  obtain ⟨X, hX, hpos⟩ := h (b + 2)
  obtain ⟨n, hn, _, hp, hm⟩ := pair_of_mass_pos hpos
  have hbn : b + 2 < n := by exact_mod_cast hX.trans hn
  have hshift : n - 2 + 2 = n := by omega
  have hmem : n - 2 ∈ {p : ℕ | p.Prime ∧ (p + 2).Prime} :=
    ⟨hm, hshift.symm ▸ hp⟩
  have := hb hmem
  omega

end
end REAL1B

#print axioms REAL1B.rough_iff
#print axioms REAL1B.rough_rank
#print axioms REAL1B.parity_masks
#print axioms REAL1B.source_parity
#print axioms REAL1B.h2_identity
#print axioms REAL1B.h2_lower
#print axioms REAL1B.pair_of_mass_pos
#print axioms REAL1B.infinite_of_unbounded_mass
