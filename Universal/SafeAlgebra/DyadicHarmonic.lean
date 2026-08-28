/-
# Universal v8.4 — dyadic harmonic fibre

**Status: PROVED_FINITE.**

The dyadic harmonic sum is bounded by an absolute constant:

  `∑_{S ≤ s ≤ 2S} 1/s ≤ 2`  (for `S ≥ 1`),

and consequently

  `∑_{S ≤ s ≤ 2S} φ(d)/(d s) ≤ 2 φ(d)/d`.

This supports the natural-scale counting calculation; no asymptotics are used.
-/
import Mathlib

namespace Universal.SafeAlgebra

open Finset

/-- Each term of a dyadic block is at most `1/S`. -/
theorem dyadic_term_le {S s : ℕ} (hS : 1 ≤ S) (hs : s ∈ Finset.Icc S (2 * S)) :
    (1 : ℝ) / s ≤ 1 / S := by
  have hs1 : S ≤ s := (Finset.mem_Icc.1 hs).1
  have hSpos : (0 : ℝ) < S := by exact_mod_cast hS
  have hspos : (0 : ℝ) < s := lt_of_lt_of_le hSpos (by exact_mod_cast hs1)
  exact one_div_le_one_div_of_le hSpos (by exact_mod_cast hs1)

/-- **Dyadic harmonic bound.**  `∑_{S ≤ s ≤ 2S} 1/s ≤ 2` for `S ≥ 1`. -/
theorem dyadic_harmonic_le_two {S : ℕ} (hS : 1 ≤ S) :
    ∑ s ∈ Finset.Icc S (2 * S), (1 : ℝ) / s ≤ 2 := by
  have hcard : (Finset.Icc S (2 * S)).card = S + 1 := by
    rw [Nat.card_Icc]; omega
  have hSpos : (0 : ℝ) < S := by exact_mod_cast hS
  have hbound : ∑ s ∈ Finset.Icc S (2 * S), (1 : ℝ) / s
      ≤ ∑ _s ∈ Finset.Icc S (2 * S), (1 : ℝ) / S :=
    Finset.sum_le_sum (fun s hs => dyadic_term_le hS hs)
  refine hbound.trans ?_
  rw [Finset.sum_const, hcard, nsmul_eq_mul]
  have h1 : (1 : ℝ) ≤ S := by exact_mod_cast hS
  push_cast
  rw [mul_one_div, div_le_iff₀ hSpos]
  linarith

/-- **Weighted dyadic fibre.**  `∑_{S ≤ s ≤ 2S} φ(d)/(d s) ≤ 2 φ(d)/d`. -/
theorem dyadic_totient_fibre_le {S d : ℕ} (hS : 1 ≤ S) (hd : 1 ≤ d) :
    ∑ s ∈ Finset.Icc S (2 * S), ((d.totient : ℝ) / (d * s))
      ≤ 2 * ((d.totient : ℝ) / d) := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hnn : (0 : ℝ) ≤ (d.totient : ℝ) / d := div_nonneg (by positivity) hdpos.le
  have hrw : ∀ s ∈ Finset.Icc S (2 * S),
      ((d.totient : ℝ) / (d * s)) = ((d.totient : ℝ) / d) * (1 / s) := by
    intro s _; field_simp
  rw [Finset.sum_congr rfl hrw, ← Finset.mul_sum]
  have := dyadic_harmonic_le_two (S := S) hS
  calc ((d.totient : ℝ) / d) * ∑ s ∈ Finset.Icc S (2 * S), (1 : ℝ) / s
      ≤ ((d.totient : ℝ) / d) * 2 := by
        exact mul_le_mul_of_nonneg_left this hnn
    _ = 2 * ((d.totient : ℝ) / d) := by ring

end Universal.SafeAlgebra
