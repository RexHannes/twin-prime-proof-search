/-
# UniversalV8 Modules B and C — finite discrete bounded variation, and
#                                piecewise-constant routing variation

Everything here is exact finite algebra / normed inequalities.

NOTHING in this file asserts anything about an actual arithmetic routing weight.
In particular the antecedent of the piecewise-constant bound (that the literal
Gate routing multiplicity has few jumps) is NOT declared anywhere; see
`UniversalV8/Interfaces.lean` (`ROUTE-BV45`, source-open).
-/
import UniversalV8.DiscreteAbel

open Finset

namespace UniversalV8

/-! ## Module B — elementary closure rules for the discrete variation -/

@[simp] theorem variation_empty (m n : ℕ) (h : n ≤ m) (w : ℕ → ℂ) : variation m n w = 0 := by
  simp [variation, Finset.Ico_eq_empty_of_le h]

theorem variation_nonneg (m n : ℕ) (w : ℕ → ℂ) : 0 ≤ variation m n w :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

@[simp] theorem variation_const (m n : ℕ) (c : ℂ) : variation m n (fun _ => c) = 0 := by
  simp [variation]

theorem variation_smul (m n : ℕ) (c : ℂ) (w : ℕ → ℂ) :
    variation m n (fun k => c * w k) = ‖c‖ * variation m n w := by
  simp only [variation, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← mul_sub, norm_mul]

theorem variation_add (m n : ℕ) (w v : ℕ → ℂ) :
    variation m n (fun k => w k + v k) ≤ variation m n w + variation m n v := by
  simp only [variation, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun k _ => ?_
  calc ‖w (k + 1) + v (k + 1) - (w k + v k)‖
      = ‖(w (k + 1) - w k) + (v (k + 1) - v k)‖ := by ring_nf
    _ ≤ ‖w (k + 1) - w k‖ + ‖v (k + 1) - v k‖ := norm_add_le _ _

theorem variation_sub (m n : ℕ) (w v : ℕ → ℂ) :
    variation m n (fun k => w k - v k) ≤ variation m n w + variation m n v := by
  simp only [variation, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun k _ => ?_
  calc ‖w (k + 1) - v (k + 1) - (w k - v k)‖
      = ‖(w (k + 1) - w k) - (v (k + 1) - v k)‖ := by ring_nf
    _ ≤ ‖w (k + 1) - w k‖ + ‖v (k + 1) - v k‖ := norm_sub_le _ _

theorem variation_mul (m n : ℕ) (w v : ℕ → ℂ) (Mw Mv : ℝ)
    (hw : ∀ k, m ≤ k → k ≤ n → ‖w k‖ ≤ Mw) (hv : ∀ k, m ≤ k → k ≤ n → ‖v k‖ ≤ Mv) :
    variation m n (fun k => w k * v k) ≤ Mw * variation m n v + Mv * variation m n w := by
  simp only [variation, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun k hk => ?_
  simp only [Finset.mem_Ico] at hk
  have hMw : ‖w (k + 1)‖ ≤ Mw := hw (k + 1) (by omega) (by omega)
  have hMv : ‖v k‖ ≤ Mv := hv k (by omega) (by omega)
  calc ‖w (k + 1) * v (k + 1) - w k * v k‖
      = ‖w (k + 1) * (v (k + 1) - v k) + (w (k + 1) - w k) * v k‖ := by ring_nf
    _ ≤ ‖w (k + 1) * (v (k + 1) - v k)‖ + ‖(w (k + 1) - w k) * v k‖ := norm_add_le _ _
    _ = ‖w (k + 1)‖ * ‖v (k + 1) - v k‖ + ‖w (k + 1) - w k‖ * ‖v k‖ := by
          rw [norm_mul, norm_mul]
    _ ≤ Mw * ‖v (k + 1) - v k‖ + Mv * ‖w (k + 1) - w k‖ := by
          refine add_le_add (mul_le_mul_of_nonneg_right hMw (norm_nonneg _)) ?_
          rw [mul_comm Mv]
          exact mul_le_mul_of_nonneg_left hMv (norm_nonneg _)

/-- Concatenation: the variation is additive along a splitting point. -/
theorem variation_concat (m p n : ℕ) (hmp : m ≤ p) (hpn : p ≤ n) (w : ℕ → ℂ) :
    variation m n w = variation m p w + variation p n w := by
  simp only [variation]
  rw [← Finset.sum_Ico_consecutive _ hmp hpn]

/-- Monotonicity under restriction to a subinterval. -/
theorem variation_mono (m m' n' n : ℕ) (h1 : m ≤ m') (h2 : n' ≤ n) (w : ℕ → ℂ) :
    variation m' n' w ≤ variation m n w := by
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => norm_nonneg _)
  exact Finset.Ico_subset_Ico h1 h2

/-- If `w` is constant across the interval then its variation vanishes. -/
theorem variation_piecewise_const (m n : ℕ) (w : ℕ → ℂ)
    (h : ∀ k, m ≤ k → k < n → w (k + 1) = w k) : variation m n w = 0 := by
  refine Finset.sum_eq_zero fun k hk => ?_
  simp only [Finset.mem_Ico] at hk
  simp [h k hk.1 hk.2]

/-- The effective discrete-BV cost with a supplied uniform bound `M`. -/
noncomputable def dBV (M : ℝ) (m n : ℕ) (w : ℕ → ℂ) : ℝ := M + variation m n w

/-- **(ABEL-BV) in dBV form.**  A partial-sum bound `Δ` plus a uniform weight bound `M`
gives `|∑ a w| ≤ Δ (M + Var w)`. -/
theorem weighted_sum_le_partialSum_mul_dBV (m n : ℕ) (hmn : m < n) (a w : ℕ → ℂ)
    (Δ M : ℝ) (hP : ∀ t, m ≤ t → t < n → ‖partialSum m a t‖ ≤ Δ)
    (hM : ∀ k, m ≤ k → k < n → ‖w k‖ ≤ M) :
    ‖∑ k ∈ Finset.Ico m n, a k * w k‖ ≤ Δ * dBV M m (n - 1) w := by
  have hΔ : 0 ≤ Δ := le_trans (norm_nonneg _) (hP m le_rfl hmn)
  refine le_trans (norm_sum_le_partialSumBound_mul_variation m n hmn a w Δ hP) ?_
  have : ‖w (n - 1)‖ ≤ M := hM (n - 1) (by omega) (by omega)
  unfold dBV
  gcongr

/-! ## Module C — piecewise-constant routing variation

Abstract theorem only: `J` jump locations and a uniform bound `M` give `Var ≤ 2 M J`.
This says nothing about whether any actual routing weight has few jumps.
-/

/-- The set of adjacent pairs in `[m, n)` at which `w` jumps. -/
noncomputable def jumpSet (m n : ℕ) (w : ℕ → ℂ) : Finset ℕ :=
  (Finset.Ico m n).filter (fun k => w (k + 1) ≠ w k)

/-- **(PC-BV).**  `Var(w) ≤ 2 M · #jumps`. -/
theorem variation_le_two_mul_bound_mul_jumpCount (m n : ℕ) (w : ℕ → ℂ) (M : ℝ)
    (hM : ∀ k, m ≤ k → k ≤ n → ‖w k‖ ≤ M) :
    variation m n w ≤ 2 * M * (jumpSet m n w).card := by
  classical
  have hsplit : variation m n w
      = ∑ k ∈ jumpSet m n w, ‖w (k + 1) - w k‖ := by
    unfold variation jumpSet
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.Ico m n) (fun k => w (k + 1) ≠ w k)]
    have : ∑ k ∈ (Finset.Ico m n).filter (fun k => ¬ (w (k + 1) ≠ w k)), ‖w (k + 1) - w k‖ = 0 := by
      refine Finset.sum_eq_zero fun k hk => ?_
      simp only [Finset.mem_filter, not_not] at hk
      simp [hk.2]
    rw [this, add_zero]
  rw [hsplit]
  have hterm : ∀ k ∈ jumpSet m n w, ‖w (k + 1) - w k‖ ≤ 2 * M := by
    intro k hk
    simp only [jumpSet, Finset.mem_filter, Finset.mem_Ico] at hk
    have h1 : ‖w (k + 1)‖ ≤ M := hM (k + 1) (by omega) (by omega)
    have h2 : ‖w k‖ ≤ M := hM k (by omega) (by omega)
    calc ‖w (k + 1) - w k‖ ≤ ‖w (k + 1)‖ + ‖w k‖ := norm_sub_le _ _
      _ ≤ M + M := add_le_add h1 h2
      _ = 2 * M := by ring
  calc ∑ k ∈ jumpSet m n w, ‖w (k + 1) - w k‖
      ≤ ∑ _k ∈ jumpSet m n w, (2 * M) := Finset.sum_le_sum hterm
    _ = 2 * M * (jumpSet m n w).card := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring

/-- **(PC-dBV).**  `dBV(w) ≤ M (1 + 2 J)`. -/
theorem dBV_le_of_jumpCount (m n : ℕ) (w : ℕ → ℂ) (M : ℝ)
    (hM : ∀ k, m ≤ k → k ≤ n → ‖w k‖ ≤ M) :
    dBV M m n w ≤ M * (1 + 2 * (jumpSet m n w).card) := by
  have := variation_le_two_mul_bound_mul_jumpCount m n w M hM
  unfold dBV
  nlinarith [this]

end UniversalV8
