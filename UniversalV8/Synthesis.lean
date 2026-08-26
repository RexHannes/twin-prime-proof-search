/-
# UniversalV8 Modules E and F — actual-vector transport and the Schur congestion criterion

Exact finite/Hilbert-space inequalities only.  Nothing here asserts that any
Gate-specific kernel satisfies a Schur row bound.
-/
import Mathlib

open Finset

namespace UniversalV8

/-! ## Module E — actual-vector transport (AVT) -/

/-- **(AVT).**  If `‖G z‖ ≤ η ‖z‖` then `|⟪z, G z⟫| ≤ η ‖z‖²`.
Positive semidefiniteness is not needed for this absolute-value form. -/
theorem inner_apply_le_of_apply_norm_le {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (G : H → H) (z : H) (η : ℝ) (hG : ‖G z‖ ≤ η * ‖z‖) :
    ‖(inner ℂ z (G z) : ℂ)‖ ≤ η * ‖z‖ ^ 2 := by
  calc ‖(inner ℂ z (G z) : ℂ)‖ ≤ ‖z‖ * ‖G z‖ := norm_inner_le_norm _ _
    _ ≤ ‖z‖ * (η * ‖z‖) := mul_le_mul_of_nonneg_left hG (norm_nonneg _)
    _ = η * ‖z‖ ^ 2 := by ring

/-- Actual-vector transport in the real-part form: `re ⟪z, G z⟫ ≤ ‖z‖ ‖G z‖`.
This is the safe finite form of "signed-source transport": no Gate-specific bound on
`‖G z‖` is asserted. -/
theorem actualVectorTransport {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (G : H → H) (z : H) :
    (inner ℂ z (G z) : ℂ).re ≤ ‖z‖ * ‖G z‖ :=
  le_trans (Complex.re_le_norm _) (norm_inner_le_norm z (G z))

/-! ## Module F — Schur congestion criterion -/

/-- **(SCHUR-0).**  A symmetric nonnegative kernel with all row sums `≤ η` has quadratic
form bounded by `η ∑ x_i²`.  (No sign assumption on `x` is needed.) -/
theorem unweightedSchur {ι : Type*} [Fintype ι] (K : ι → ι → ℝ) (x : ι → ℝ) (η : ℝ)
    (hK : ∀ i j, 0 ≤ K i j) (hsymm : ∀ i j, K i j = K j i)
    (hrow : ∀ i, ∑ j, K i j ≤ η) :
    ∑ i, ∑ j, K i j * x i * x j ≤ η * ∑ i, x i ^ 2 := by
  set A := ∑ i, ∑ j, K i j * x i ^ 2 with hA
  have key : ∑ i, ∑ j, K i j * x i * x j ≤ ∑ i, ∑ j, K i j * ((x i ^ 2 + x j ^ 2) / 2) := by
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
    have h : x i * x j ≤ (x i ^ 2 + x j ^ 2) / 2 := by nlinarith [sq_nonneg (x i - x j)]
    calc K i j * x i * x j = K i j * (x i * x j) := by ring
      _ ≤ K i j * ((x i ^ 2 + x j ^ 2) / 2) := mul_le_mul_of_nonneg_left h (hK i j)
  have swap : ∑ i, ∑ j, K i j * x j ^ 2 = A := by
    rw [hA, Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by rw [hsymm]
  have expand : ∑ i, ∑ j, K i j * ((x i ^ 2 + x j ^ 2) / 2) = A := by
    have hrow' : ∀ i : ι, ∑ j, K i j * ((x i ^ 2 + x j ^ 2) / 2)
        = (∑ j, K i j * x i ^ 2) / 2 + (∑ j, K i j * x j ^ 2) / 2 := by
      intro i
      rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [Finset.sum_congr rfl fun i _ => hrow' i, Finset.sum_add_distrib, ← Finset.sum_div,
      ← Finset.sum_div, swap, ← hA]
    ring
  have hAle : A ≤ η * ∑ i, x i ^ 2 := by
    rw [hA, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (hrow i) (sq_nonneg _)
  linarith [key, expand ▸ key]

/-- **Weighted Schur test.**  For a symmetric nonnegative kernel and positive weights `w`
with `∑_j K i j w j ≤ η w i` for every `i`, the quadratic form is bounded by `η ∑ x_i²`.

The symmetry hypothesis is what makes the single (row) condition sufficient; without a
column condition or symmetry the one-sided statement is false. -/
theorem weightedSchur {ι : Type*} [Fintype ι] (K : ι → ι → ℝ) (w x : ι → ℝ) (η : ℝ)
    (hK : ∀ i j, 0 ≤ K i j) (hsymm : ∀ i j, K i j = K j i) (hw : ∀ i, 0 < w i)
    (hrow : ∀ i, ∑ j, K i j * w j ≤ η * w i) :
    ∑ i, ∑ j, K i j * x i * x j ≤ η * ∑ i, x i ^ 2 := by
  have amgm : ∀ i j, x i * x j ≤ ((w j / w i) * x i ^ 2 + (w i / w j) * x j ^ 2) / 2 := by
    intro i j
    have hwi := hw i; have hwj := hw j
    rw [← sub_nonneg]
    have expand : ((w j / w i) * x i ^ 2 + (w i / w j) * x j ^ 2) / 2 - x i * x j
        = (w j * x i - w i * x j) ^ 2 / (2 * (w i * w j)) := by field_simp; ring
    rw [expand]; positivity
  have key : ∑ i, ∑ j, K i j * x i * x j
      ≤ ∑ i, ∑ j, (K i j * w j * (x i ^ 2 / w i) / 2 + K i j * w i * (x j ^ 2 / w j) / 2) := by
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
    have hle := mul_le_mul_of_nonneg_left (amgm i j) (hK i j)
    have hwi := hw i; have hwj := hw j
    calc K i j * x i * x j = K i j * (x i * x j) := by ring
      _ ≤ K i j * (((w j / w i) * x i ^ 2 + (w i / w j) * x j ^ 2) / 2) := hle
      _ = K i j * w j * (x i ^ 2 / w i) / 2 + K i j * w i * (x j ^ 2 / w j) / 2 := by
          field_simp
  have row : ∀ i : ι, (∑ j, K i j * w j) * (x i ^ 2 / w i) / 2 ≤ η * x i ^ 2 / 2 := by
    intro i
    have hwi := hw i
    have h1 : (∑ j, K i j * w j) * (x i ^ 2 / w i) ≤ (η * w i) * (x i ^ 2 / w i) :=
      mul_le_mul_of_nonneg_right (hrow i) (by positivity)
    have h2 : (η * w i) * (x i ^ 2 / w i) = η * x i ^ 2 := by field_simp
    rw [h2] at h1; linarith
  have part1 : ∑ i, ∑ j, K i j * w j * (x i ^ 2 / w i) / 2 ≤ (η * ∑ i, x i ^ 2) / 2 := by
    have hfac : ∀ i : ι, ∑ j, K i j * w j * (x i ^ 2 / w i) / 2
        = (∑ j, K i j * w j) * (x i ^ 2 / w i) / 2 := by
      intro i; rw [← Finset.sum_div, ← Finset.sum_mul]
    rw [Finset.sum_congr rfl fun i _ => hfac i]
    calc ∑ i, (∑ j, K i j * w j) * (x i ^ 2 / w i) / 2 ≤ ∑ i, η * x i ^ 2 / 2 :=
          Finset.sum_le_sum fun i _ => row i
      _ = (η * ∑ i, x i ^ 2) / 2 := by rw [← Finset.sum_div, ← Finset.mul_sum]
  have part2 : ∑ i, ∑ j, K i j * w i * (x j ^ 2 / w j) / 2 ≤ (η * ∑ i, x i ^ 2) / 2 := by
    rw [Finset.sum_comm]
    have heq : ∑ j, ∑ i, K i j * w i * (x j ^ 2 / w j) / 2
        = ∑ j, ∑ i, K j i * w i * (x j ^ 2 / w j) / 2 :=
      Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by rw [hsymm i j]
    rw [heq]
    have hfac : ∀ j : ι, ∑ i, K j i * w i * (x j ^ 2 / w j) / 2
        = (∑ i, K j i * w i) * (x j ^ 2 / w j) / 2 := by
      intro j; rw [← Finset.sum_div, ← Finset.sum_mul]
    rw [Finset.sum_congr rfl fun j _ => hfac j]
    calc ∑ j, (∑ i, K j i * w i) * (x j ^ 2 / w j) / 2 ≤ ∑ j, η * x j ^ 2 / 2 :=
          Finset.sum_le_sum fun j _ => row j
      _ = (η * ∑ i, x i ^ 2) / 2 := by rw [← Finset.sum_div, ← Finset.mul_sum]
  have hsplit : ∑ i, ∑ j, (K i j * w j * (x i ^ 2 / w i) / 2 + K i j * w i * (x j ^ 2 / w j) / 2)
      = (∑ i, ∑ j, K i j * w j * (x i ^ 2 / w i) / 2)
        + ∑ i, ∑ j, K i j * w i * (x j ^ 2 / w j) / 2 := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_add_distrib
  rw [hsplit] at key
  linarith

/-- The one-sided weighted Schur criterion genuinely needs symmetry (or a column
condition): here is a nonsymmetric `5 × 5` kernel with all weighted row sums `≤ 1`
whose quadratic form exceeds `1 · ∑ x_i²`. -/
theorem weightedSchur_needs_symmetry :
    ∃ (K : Fin 5 → Fin 5 → ℝ) (w x : Fin 5 → ℝ) (η : ℝ),
      (∀ i j, 0 ≤ K i j) ∧ (∀ i, 0 < w i) ∧ (∀ i, ∑ j, K i j * w j ≤ η * w i) ∧
        η * ∑ i, x i ^ 2 < ∑ i, ∑ j, K i j * x i * x j := by
  refine ⟨fun _ => ![1, 0, 0, 0, 0], fun _ => 1, ![1, 1/2, 1/2, 1/2, 1/2], 1, ?_, ?_, ?_, ?_⟩
  · intro _ j; fin_cases j <;> norm_num
  · intro _; norm_num
  · intro _; norm_num [Fin.sum_univ_succ]
  · norm_num [Fin.sum_univ_succ]

end UniversalV8
