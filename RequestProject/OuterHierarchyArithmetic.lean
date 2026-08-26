import Mathlib

/-! Finite arithmetic used by the outer-block hierarchy. -/

namespace ShiftedMobiusBank

/-- Ordered weights of total mass one have at least average mass in any initial
segment. The sequence is represented on `ℕ`; only its first `d` values matter. -/
theorem OUTER_BLOCK_AVERAGE_LEMMA {d k : ℕ} (hk : k ≤ d)
    (w : ℕ → ℝ) (hord : Antitone w) (hsum : ∑ i ∈ Finset.range d, w i = 1) :
    (k : ℝ) / d ≤ ∑ i ∈ Finset.range k, w i := by
  by_cases hd : d = 0
  · -- If d = 0, then k ≤ d implies k = 0
    simp [hd]
    have : k = 0 := Nat.eq_zero_of_le_zero (hk.trans hd.le)
    simp [this]
  · have hd' : (0 : ℝ) < d := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hd)
    by_cases hk0 : k = 0
    · -- k = 0: both sides are 0
      simp [hk0]
    · -- k > 0
      have hk' : (0 : ℝ) < k := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk0)
      -- Key: sum of tail ≤ (d - k) * w k, and sum of head ≥ k * w k
      -- Since w is antitone, for i < k: w i ≥ w k, and for i ≥ k: w i ≤ w k
      have htail : ∑ i ∈ Finset.Ico k d, w i ≤ (d - k) * w k := by
        have hcard : (Finset.Ico k d).card = d - k := by simp [Nat.card_Ico]
        have hle : ∀ i ∈ Finset.Ico k d, w i ≤ w k := by
          intro i hi
          exact hord (Finset.mem_Ico.mp hi).1
        calc ∑ i ∈ Finset.Ico k d, w i ≤ ∑ _i ∈ Finset.Ico k d, w k := Finset.sum_le_sum hle
          _ = (Finset.Ico k d).card * w k := by simp [Finset.sum_const]
          _ = (d - k : ℕ) * w k := by rw [hcard]
          _ = ((d : ℝ) - k) * w k := by rw [Nat.cast_sub hk]
      have hhead : k * w k ≤ ∑ i ∈ Finset.range k, w i := by
        have hle : ∀ i ∈ Finset.range k, w k ≤ w i := by
          intro i hi
          exact hord (Finset.mem_range.mp hi).le
        calc (k : ℝ) * w k = ∑ _i ∈ Finset.range k, w k := by simp [Finset.sum_const]
          _ ≤ ∑ i ∈ Finset.range k, w i := Finset.sum_le_sum hle
      -- Split the sum: range d = range k ∪ Ico k d
      have hsplit : ∑ i ∈ Finset.range d, w i = ∑ i ∈ Finset.range k, w i + ∑ i ∈ Finset.Ico k d, w i := by
        rw [← Finset.sum_union (Finset.disjoint_right.mpr fun i hi => by simp_all [Finset.mem_Ico])]
        congr 1
        ext i
        simp [Finset.mem_range, Finset.mem_Ico]
        omega
      -- Combine: 1 = head + tail ≤ head + (d-k) * w k ≤ head + (d-k) * (head / k) = head * d / k
      have hknd : (k : ℝ) ≤ d := Nat.cast_le.mpr hk
      have h2 : 1 ≤ ∑ i ∈ Finset.range k, w i + (d - k) * w k := by linarith [htail]
      have hwk_bound : w k ≤ (∑ i ∈ Finset.range k, w i) / k := by
        rw [le_div_iff₀ hk']
        linarith
      have h3 : 1 ≤ ∑ i ∈ Finset.range k, w i + (d - k) * ((∑ i ∈ Finset.range k, w i) / k) := by
        have hnk : (0 : ℝ) ≤ d - k := sub_nonneg.mpr hknd
        have := mul_le_mul_of_nonneg_left hwk_bound hnk
        linarith
      have h4 : 1 ≤ (∑ i ∈ Finset.range k, w i) * (1 + (d - k) / k) := by
        convert h3 using 1
        field_simp
      have h5 : 1 ≤ (∑ i ∈ Finset.range k, w i) * d / k := by
        convert h4 using 1
        field_simp
        ring
      have h6 : (k : ℝ) ≤ (∑ i ∈ Finset.range k, w i) * d := by
        have h5' : (1 : ℝ) * k ≤ (∑ i ∈ Finset.range k, w i) * d := by
          have := mul_le_mul_of_nonneg_right h5 (le_of_lt hk')
          field_simp at this
          linarith
        linarith
      calc (k : ℝ) / d ≤ (∑ i ∈ Finset.range k, w i) * d / d := by gcongr
        _ = ∑ i ∈ Finset.range k, w i := by field_simp

/-- The first integer strictly exceeding `d w*` is `⌊d w*⌋₊ + 1`.
This is the precise integer arithmetic behind the hierarchy threshold. -/
noncomputable def kMin (d : ℕ) (wStar : ℝ) : ℕ := ⌊(d : ℝ) * wStar⌋₊ + 1

theorem kMin_formula (d : ℕ) (wStar : ℝ) :
    kMin d wStar = ⌊(d : ℝ) * wStar⌋₊ + 1 := rfl

theorem kMin_is_minimal {d : ℕ} {wStar : ℝ} (hw : 0 ≤ wStar) :
    (d : ℝ) * wStar < kMin d wStar ∧
      ∀ k : ℕ, (d : ℝ) * wStar < k → kMin d wStar ≤ k := by
  constructor
  · simpa [kMin] using Nat.lt_floor_add_one ((d : ℝ) * wStar)
  · intro k hk
    rw [kMin, Nat.add_one_le_iff]
    exact (Nat.floor_lt (mul_nonneg (Nat.cast_nonneg d) hw)).2 hk

/-- Sol-corrected routing threshold, retained exactly as a rational function. -/
def fordWStar (mu : ℚ) : ℚ := (40 + 61 * mu) / 81

@[simp] theorem fordWStar_zero : fordWStar 0 = 40 / 81 := by
  norm_num [fordWStar]

theorem fordWStar_affine (mu : ℚ) : 81 * fordWStar mu = 40 + 61 * mu := by
  unfold fordWStar
  ring

/-- Exact finite-level arithmetic can be instantiated once the Ford-relevant
rational `mu` and levels are supplied by a cited audit. -/
theorem FINITE_OUTER_LEVEL_ARITHMETIC (d : ℕ) (mu : ℚ) :
    kMin d (fordWStar mu) = ⌊(d : ℝ) * (fordWStar mu : ℝ)⌋₊ + 1 := rfl

end ShiftedMobiusBank
