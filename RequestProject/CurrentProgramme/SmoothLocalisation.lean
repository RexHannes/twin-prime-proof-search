import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Phase A3 · smooth-localisation compiler (source-independent finite algebra)

The Lean-safe core underlying `LOCALIZED-FIVEFOLD-MOTOHASHI45`.

Given a **prefix discrepancy** `E : ℕ → ℝ` with `E 0 = 0` and a finite weight
`F : ℕ → ℝ`, the weighted discrepancy over `range n` is

  `wDiscrepancy F E n = ∑_{i < n} F i * (E (i+1) - E i)`.

The theorem proved here is purely finite summation by parts:

  `|wDiscrepancy F E n| ≤ (supNorm F n + totalVariation F n) * T`

whenever `|E k| ≤ T` for all `k ≤ n`.

**No Bombieri–Vinogradov estimate is claimed.**  `T` is a hypothesis.  The
module is a *transfer*: it converts a sharp-cutoff discrepancy bound into a
smooth/discrete-weight discrepancy bound at cost `‖F‖_∞ + Var F`.
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace SmoothLocalisation

/-- Weighted discrepancy of the increments of `E` against the weight `F`. -/
def wDiscrepancy (F E : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, F i * (E (i + 1) - E i)

/-- Sup-norm of `F` over the relevant window (a max over `range n`, plus the
endpoint value, taken as an explicit hypothesis bound below). -/
def supNormBound (F : ℕ → ℝ) (n : ℕ) (S : ℝ) : Prop := ∀ i < n, |F i| ≤ S

/-- Discrete total variation of `F` over `range (n-1)`. -/
def totalVariation (F : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n - 1), |F (i + 1) - F i|

theorem totalVariation_nonneg (F : ℕ → ℝ) (n : ℕ) : 0 ≤ totalVariation F n :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

/-- Telescoping: the partial sums of the increments recover `E`, given
`E 0 = 0`. -/
theorem sum_increments (E : ℕ → ℝ) (hE0 : E 0 = 0) (m : ℕ) :
    ∑ i ∈ Finset.range m, (E (i + 1) - E i) = E m := by
  induction m with
  | zero => simpa using hE0.symm
  | succ k ih => rw [Finset.sum_range_succ, ih]; ring

/-- **A3, Abel summation.**  Exact summation-by-parts identity for the weighted
discrepancy. -/
theorem wDiscrepancy_abel (F E : ℕ → ℝ) (hE0 : E 0 = 0) (n : ℕ) :
    wDiscrepancy F E n =
      F (n - 1) * E n - ∑ i ∈ Finset.range (n - 1), (F (i + 1) - F i) * E (i + 1) := by
  have h := Finset.sum_range_by_parts F (fun i => E (i + 1) - E i) n
  simp only [smul_eq_mul] at h
  rw [wDiscrepancy, h, sum_increments E hE0 n]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sum_increments E hE0 (i + 1)]

/-- **A3, the localisation compiler.**  If the sharp-cutoff discrepancy
satisfies `|E k| ≤ T` for all `k ≤ n`, and `F` has sup-norm bound `S` on the
window, then the weighted discrepancy is at most `(S + Var F) * T`.

This is source-independent finite algebra: no analytic input is used, and `T`
is not proved. -/
theorem wDiscrepancy_le (F E : ℕ → ℝ) (hE0 : E 0 = 0) (n : ℕ) {S T : ℝ}
    (hT : ∀ k ≤ n, |E k| ≤ T) (hS : ∀ i < n, |F i| ≤ S) (hn : 0 < n) :
    |wDiscrepancy F E n| ≤ (S + totalVariation F n) * T := by
  have hT0 : 0 ≤ T := le_trans (abs_nonneg (E 0)) (hT 0 (Nat.zero_le n))
  rw [wDiscrepancy_abel F E hE0 n]
  have hmain : |F (n - 1) * E n| ≤ S * T := by
    rw [abs_mul]
    exact mul_le_mul (hS (n - 1) (by omega)) (hT n le_rfl) (abs_nonneg _)
      (le_trans (abs_nonneg _) (hS (n - 1) (by omega)))
  have htail :
      |∑ i ∈ Finset.range (n - 1), (F (i + 1) - F i) * E (i + 1)|
        ≤ totalVariation F n * T := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    rw [totalVariation, Finset.sum_mul]
    refine Finset.sum_le_sum fun i hi => ?_
    rw [abs_mul]
    have hib : i + 1 ≤ n := by
      simp only [Finset.mem_range] at hi; omega
    exact mul_le_mul_of_nonneg_left (hT (i + 1) hib) (abs_nonneg _)
  calc |F (n - 1) * E n - ∑ i ∈ Finset.range (n - 1), (F (i + 1) - F i) * E (i + 1)|
      ≤ |F (n - 1) * E n| + |∑ i ∈ Finset.range (n - 1), (F (i + 1) - F i) * E (i + 1)| :=
        abs_sub _ _
    _ ≤ S * T + totalVariation F n * T := add_le_add hmain htail
    _ = (S + totalVariation F n) * T := by ring

/-- **Uniformity in a residue parameter.**  The same bound, held uniformly over
a finite family of residues `a`, which is the form `LOCALIZED-FIVEFOLD-…`
consumes: `max_a |weighted discrepancy| ≤ (‖F‖_∞ + Var F) · T(q)`. -/
theorem wDiscrepancy_le_uniform {ι : Type*} (F : ℕ → ℝ) (E : ι → ℕ → ℝ)
    (hE0 : ∀ a, E a 0 = 0) (n : ℕ) {S T : ℝ}
    (hT : ∀ a, ∀ k ≤ n, |E a k| ≤ T) (hS : ∀ i < n, |F i| ≤ S) (hn : 0 < n) :
    ∀ a, |wDiscrepancy F (E a) n| ≤ (S + totalVariation F n) * T :=
  fun a => wDiscrepancy_le F (E a) (hE0 a) n (hT a) hS hn

/-- **Counterguard.**  The compiler genuinely needs the variation term: with
`T = 1` and a rapidly oscillating weight of sup-norm `1`, the sup-norm alone
does not bound the weighted discrepancy.  Concretely `F i = (-1)^i`,
`E k = k % 2` gives `|wDiscrepancy| = 4 > 1 · 1` at `n = 4`. -/
theorem supNorm_alone_insufficient :
    ∃ (F E : ℕ → ℝ) (n : ℕ) (S T : ℝ),
      E 0 = 0 ∧ (∀ k ≤ n, |E k| ≤ T) ∧ (∀ i < n, |F i| ≤ S) ∧
        ¬ (|wDiscrepancy F E n| ≤ S * T) := by
  refine ⟨fun i => (-1 : ℝ) ^ i, fun k => if k % 2 = 0 then 0 else 1, 4, 1, 1,
    by norm_num, ?_, ?_, ?_⟩
  · intro k _
    by_cases h : k % 2 = 0 <;> simp [h]
  · intro i _; simp [abs_pow]
  · norm_num [wDiscrepancy, Finset.sum_range_succ]

end SmoothLocalisation
end CurrentProgramme
end TwinPrimeProject
