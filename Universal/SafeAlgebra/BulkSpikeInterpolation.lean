/-
# Universal safe algebra v8.3 — bulk/spike finite interpolation

**Status: PROVED_FINITE.**

Pure finite analysis.  For a finite index set `D`, coefficients `A, T : D → ℂ`
and a threshold `L > 0`, split `D` into

    bulk  = {d : ‖A d‖ ≤ L},      spike = {d : L < ‖A d‖}

and bound each piece:

* `bulk_bound`     — `∑_bulk ‖A d T d‖ ≤ L √(#D) ‖T‖₂`;
* `spike_l1_bound` — `∑_spike ‖A d‖ ≤ ‖A‖₂² / L`;
* `spike_weighted_bound` — `∑_spike ‖A d T d‖ ≤ ‖T‖_∞ ‖A‖₂² / L`;
* `spike_card_l1_bound`, `spike_l2_card_bound` — the two spike-cardinality
  estimates;
* `bulkSpike_bound` — the combined interpolation inequality.

No asymptotics, no arithmetic input.
-/
import Mathlib

namespace Universal.SafeAlgebra

open Finset

variable {D : Type*} [Fintype D]

/-- The bulk index set. -/
noncomputable def bulkSet (A : D → ℂ) (L : ℝ) : Finset D := univ.filter (fun d => ‖A d‖ ≤ L)

/-- The spike index set. -/
noncomputable def spikeSet (A : D → ℂ) (L : ℝ) : Finset D := univ.filter (fun d => L < ‖A d‖)

/-- The ℓ² norm of a finite coefficient vector. -/
noncomputable def l2Norm (T : D → ℂ) : ℝ := Real.sqrt (∑ d : D, ‖T d‖ ^ 2)

theorem l2Norm_nonneg (T : D → ℂ) : 0 ≤ l2Norm T := Real.sqrt_nonneg _

/-- Cauchy–Schwarz on any subset: the ℓ¹ mass is at most `√(#D)` times the
global ℓ² norm. -/
theorem sum_norm_le_sqrt_card_mul_l2 (T : D → ℂ) (s : Finset D) :
    ∑ d ∈ s, ‖T d‖ ≤ Real.sqrt (Fintype.card D) * l2Norm T := by
  have h1 : (∑ d ∈ s, ‖T d‖) ^ 2 ≤ (s.card : ℝ) * ∑ d ∈ s, ‖T d‖ ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  have h2 : (s.card : ℝ) ≤ (Fintype.card D : ℝ) := by
    exact_mod_cast Finset.card_le_univ s
  have h3 : ∑ d ∈ s, ‖T d‖ ^ 2 ≤ ∑ d : D, ‖T d‖ ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
      (fun d _ _ => by positivity)
  have hs2 : (0 : ℝ) ≤ ∑ d ∈ s, ‖T d‖ ^ 2 := Finset.sum_nonneg fun d _ => by positivity
  have hsq : (∑ d ∈ s, ‖T d‖) ^ 2 ≤ (Real.sqrt (Fintype.card D) * l2Norm T) ^ 2 := by
    have hcard : (0 : ℝ) ≤ (Fintype.card D : ℝ) := by positivity
    have hall : (0 : ℝ) ≤ ∑ d : D, ‖T d‖ ^ 2 := Finset.sum_nonneg fun d _ => by positivity
    rw [mul_pow, Real.sq_sqrt hcard, l2Norm, Real.sq_sqrt hall]
    calc (∑ d ∈ s, ‖T d‖) ^ 2 ≤ (s.card : ℝ) * ∑ d ∈ s, ‖T d‖ ^ 2 := h1
      _ ≤ (Fintype.card D : ℝ) * ∑ d ∈ s, ‖T d‖ ^ 2 := by
          exact mul_le_mul_of_nonneg_right h2 hs2
      _ ≤ (Fintype.card D : ℝ) * ∑ d : D, ‖T d‖ ^ 2 := by
          exact mul_le_mul_of_nonneg_left h3 hcard
  have ha : 0 ≤ ∑ d ∈ s, ‖T d‖ := Finset.sum_nonneg fun d _ => norm_nonneg _
  have hb : 0 ≤ Real.sqrt (Fintype.card D) * l2Norm T :=
    mul_nonneg (Real.sqrt_nonneg _) (l2Norm_nonneg T)
  nlinarith [hsq, ha, hb]

/-- **Bulk bound.** -/
theorem bulk_bound (A T : D → ℂ) (L : ℝ) (hL : 0 ≤ L) :
    ∑ d ∈ bulkSet A L, ‖A d * T d‖ ≤ L * Real.sqrt (Fintype.card D) * l2Norm T := by
  have step1 : ∑ d ∈ bulkSet A L, ‖A d * T d‖ ≤ L * ∑ d ∈ bulkSet A L, ‖T d‖ := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun d hd => ?_
    have hdle : ‖A d‖ ≤ L := by
      have := Finset.mem_filter.1 hd
      exact this.2
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right hdle (norm_nonneg _)
  have step2 : ∑ d ∈ bulkSet A L, ‖T d‖ ≤ Real.sqrt (Fintype.card D) * l2Norm T :=
    sum_norm_le_sqrt_card_mul_l2 T _
  calc ∑ d ∈ bulkSet A L, ‖A d * T d‖ ≤ L * ∑ d ∈ bulkSet A L, ‖T d‖ := step1
    _ ≤ L * (Real.sqrt (Fintype.card D) * l2Norm T) := mul_le_mul_of_nonneg_left step2 hL
    _ = L * Real.sqrt (Fintype.card D) * l2Norm T := by ring

/-- **Spike ℓ¹ bound**: `∑_spike ‖A d‖ ≤ ‖A‖₂² / L`. -/
theorem spike_l1_bound (A : D → ℂ) (L : ℝ) (hL : 0 < L) :
    ∑ d ∈ spikeSet A L, ‖A d‖ ≤ (∑ d : D, ‖A d‖ ^ 2) / L := by
  have hpt : ∀ d ∈ spikeSet A L, ‖A d‖ ≤ ‖A d‖ ^ 2 / L := by
    intro d hd
    have hlt : L < ‖A d‖ := (Finset.mem_filter.1 hd).2
    rw [le_div_iff₀ hL, sq]
    exact mul_le_mul_of_nonneg_left hlt.le (norm_nonneg _)
  calc ∑ d ∈ spikeSet A L, ‖A d‖ ≤ ∑ d ∈ spikeSet A L, ‖A d‖ ^ 2 / L :=
        Finset.sum_le_sum hpt
    _ = (∑ d ∈ spikeSet A L, ‖A d‖ ^ 2) / L := by rw [Finset.sum_div]
    _ ≤ (∑ d : D, ‖A d‖ ^ 2) / L := by
        have hsub : ∑ d ∈ spikeSet A L, ‖A d‖ ^ 2 ≤ ∑ d : D, ‖A d‖ ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun d _ _ => by positivity)
        gcongr

/-- **Weighted spike bound**: `∑_spike ‖A d T d‖ ≤ ‖T‖_∞ ‖A‖₂² / L`. -/
theorem spike_weighted_bound (A T : D → ℂ) (L Tsup : ℝ) (hL : 0 < L) (hTnn : 0 ≤ Tsup)
    (hT : ∀ d, ‖T d‖ ≤ Tsup) :
    ∑ d ∈ spikeSet A L, ‖A d * T d‖ ≤ Tsup * ((∑ d : D, ‖A d‖ ^ 2) / L) := by
  have step : ∑ d ∈ spikeSet A L, ‖A d * T d‖ ≤ Tsup * ∑ d ∈ spikeSet A L, ‖A d‖ := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun d _ => ?_
    rw [norm_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hT d) (norm_nonneg _)
  exact step.trans (mul_le_mul_of_nonneg_left (spike_l1_bound A L hL) hTnn)

/-- **Spike cardinality from the ℓ¹ mass.** -/
theorem spike_card_l1_bound (A : D → ℂ) (L : ℝ) (hL : 0 < L) :
    ((spikeSet A L).card : ℝ) ≤ (∑ d : D, ‖A d‖) / L := by
  rw [le_div_iff₀ hL]
  have h1 : ∑ _d ∈ spikeSet A L, L = ((spikeSet A L).card : ℝ) * L := by
    simp [Finset.sum_const, nsmul_eq_mul]
  calc ((spikeSet A L).card : ℝ) * L = ∑ _d ∈ spikeSet A L, L := h1.symm
    _ ≤ ∑ d ∈ spikeSet A L, ‖A d‖ :=
        Finset.sum_le_sum fun d hd => (Finset.mem_filter.1 hd).2.le
    _ ≤ ∑ d : D, ‖A d‖ :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun d _ _ => norm_nonneg _)

/-- **Spike cardinality from the ℓ² mass.** -/
theorem spike_l2_card_bound (A : D → ℂ) (L : ℝ) (hL : 0 < L) :
    ((spikeSet A L).card : ℝ) ≤ (∑ d : D, ‖A d‖ ^ 2) / L ^ 2 := by
  rw [le_div_iff₀ (by positivity)]
  have h1 : ∑ _d ∈ spikeSet A L, L ^ 2 = ((spikeSet A L).card : ℝ) * L ^ 2 := by
    simp [Finset.sum_const, nsmul_eq_mul]
  calc ((spikeSet A L).card : ℝ) * L ^ 2 = ∑ _d ∈ spikeSet A L, L ^ 2 := h1.symm
    _ ≤ ∑ d ∈ spikeSet A L, ‖A d‖ ^ 2 := by
        refine Finset.sum_le_sum fun d hd => ?_
        have hlt : L < ‖A d‖ := (Finset.mem_filter.1 hd).2
        nlinarith [hL.le, norm_nonneg (A d)]
    _ ≤ ∑ d : D, ‖A d‖ ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun d _ _ => by positivity)

/-- **Combined bulk/spike interpolation.** -/
theorem bulkSpike_bound (A T : D → ℂ) (L Tsup : ℝ) (hL : 0 < L) (hTnn : 0 ≤ Tsup)
    (hT : ∀ d, ‖T d‖ ≤ Tsup) :
    ∑ d : D, ‖A d * T d‖
      ≤ L * Real.sqrt (Fintype.card D) * l2Norm T + Tsup * ((∑ d : D, ‖A d‖ ^ 2) / L) := by
  classical
  have hsplit : ∑ d : D, ‖A d * T d‖
      = ∑ d ∈ bulkSet A L, ‖A d * T d‖ + ∑ d ∈ spikeSet A L, ‖A d * T d‖ := by
    unfold bulkSet spikeSet
    rw [← Finset.sum_filter_add_sum_filter_not univ (fun d => ‖A d‖ ≤ L)]
    congr 1
    exact Finset.sum_congr (Finset.filter_congr fun d _ => by simp [not_le]) fun d _ => rfl
  rw [hsplit]
  exact add_le_add (bulk_bound A T L hL.le) (spike_weighted_bound A T L Tsup hL hTnn hT)

end Universal.SafeAlgebra
